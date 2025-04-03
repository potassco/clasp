//
// Copyright (c) 2010-present Benjamin Kaufmann
//
// This file is part of Clasp. See https://potassco.org/clasp/
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.
//
#pragma once

#include <clasp/config.h>

#include <cassert>

namespace Clasp::mt { // NOLINT

//! Non-owning lock-free stack that is NOT ABA-safe by itself.
class LockFreeStack {
public:
    struct Node {
        using AtomicPtr = ThreadSafe<Node*>;
        AtomicPtr next;
    };

    LockFreeStack()                = default;
    ~LockFreeStack()               = default;
    LockFreeStack(LockFreeStack&&) = delete;

    void push(Node* n) {
        auto* assumedTop = top_.load(memory_order_acquire);
        do {
            n->next.store(assumedTop, memory_order_relaxed); // not shared
        } while (not top_.compare_exchange_weak(assumedTop, n));
    }

    Node* tryPop() {
        Node *next, *n = top_.load(memory_order_acquire);
        do {
            if (n == nullptr) {
                return nullptr;
            }
            // NOTE:
            // it is the caller's job to guarantee that n is safe
            // and n->next is ABA-safe at this point.
            next = n->next.load(memory_order_relaxed);
        } while (not top_.compare_exchange_weak(n, next));
        return n;
    }

    Node* release() { return top_.exchange(nullptr); }

private:
    Node::AtomicPtr top_{nullptr};
};

//! A class for distributing items between a fixed number of threads.
/*!
 * Logically, the class maintains n queues, one for each involved thread.
 * Threads must register themselves by calling addThread().
 * The returned handle can then be used for consuming items.
 */
template <typename T>
class MultiQueue {
public:
    using ThreadId = LockFreeStack::Node*;

    //! Creates a new object for at most m threads.
    explicit MultiQueue(uint32_t m) : maxQ_(m) {}
    //! Destroys the object and all unconsumed items.
    ~MultiQueue() {
        destroy(head_.next.load(), true);
        destroy(free_.release(), false);
    }
    MultiQueue(MultiQueue&&) = delete;

    //! Pre-allocate a given number of internal queue nodes.
    void reserve(uint32_t n) {
        for (uint32_t i = 0; i != n; ++i) { free_.push(new SharedNode()); }
    }

    //! Returns the maximal number of threads that can access this queue.
    [[nodiscard]] uint32_t maxThreads() const { return maxQ_; }

    //! Registers a thread with the queue.
    /*!
     * \note Shall be called at most @c maxThreads() times.
     * \return A handle identifying the new thread.
     */
    ThreadId addThread() { return &head_; }

    //! Returns whether the given thread has unconsumed items in the queue.
    [[nodiscard]] bool hasItems(const ThreadId& cId) const { return cId != tail_.load(); }

    //! Tries to consume an item from the queue associated with the given thread.
    /*!
     * \pre cId was initially obtained via a call to addThread()
     * \note tryConsume() is thread-safe w.r.t different ThreadIds
     * \note The returned pointer is only valid until the next call to this function from the given thread.
     */
    const T* tryConsume(ThreadId& cId) {
        if (cId != tail_.load()) {
            auto* n = cId;
            cId     = cId->next.load();
            assert(cId != nullptr && "MultiQueue is corrupted!");
            release(n);
            return toNode(cId)->value();
        }
        return nullptr;
    }

    //! Adds a new item to all queues.
    void publish(T&& in) { publishSafe(allocate(std::forward<T>(in))); }

    //! Adds new item to all queues.
    /*!
     * \note the function is *not* thread-safe, i.e. it must not be called concurrently.
     */
    void unsafePublish(T&& in) { publishUnsafe(allocate(std::forward<T>(in))); }

private:
    using TailPtr  = LockFreeStack::Node::AtomicPtr;
    using BaseNode = LockFreeStack::Node;
    struct SharedNode : BaseNode {
        RefCount refs;
        alignas(T) char buffer[sizeof(T)];
        const T* value() const { return reinterpret_cast<const T*>(buffer); }
    };
    static constexpr SharedNode* toNode(BaseNode* x) { return static_cast<SharedNode*>(x); }
    static void                  destroyValue(SharedNode* x) { std::destroy_at(reinterpret_cast<T*>(x->buffer)); }

    void destroy(BaseNode* head, bool destruct) {
        for (auto* x = head; x;) {
            auto* n = toNode(x);
            x       = x->next.load(memory_order_relaxed);
            if (destruct) {
                destroyValue(n);
            }
            delete n;
        }
    }
    SharedNode* allocate(T&& in) {
        // If the queue is used correctly, the raw stack is ABA-safe at this point.
        // The ref-counting in the queue ensures that a node cannot be added back
        // to the stack while another thread is still in tryConsume() - that thread had
        // not yet the chance to decrease the node's ref count.
        auto* n = toNode(free_.tryPop());
        if (not n) {
            n = new SharedNode();
        }
        n->next.store(nullptr, memory_order_relaxed);
        n->refs.reset(maxQ_);
        std::construct_at(std::launder(reinterpret_cast<T*>(n->buffer)), std::forward<T>(in));
        return n;
    }
    void release(BaseNode* n) {
        if (n != &head_ && toNode(n)->refs.release()) {
            head_.next.store(n->next.load());
            destroyValue(toNode(n));
            free_.push(n);
        }
    }
    void publishSafe(BaseNode* newNode) {
        assert(newNode->next.load() == nullptr);
        for (;;) {
            auto* assumedTail = tail_.load();
            auto* assumedNext = assumedTail->next.load();
            if (assumedTail != tail_.load()) {
                // tail has changed - try again
                continue;
            }
            if (assumedNext != nullptr) {
                // someone has added a new node but has not yet
                // moved the tail - assist him and start over
                tail_.compare_exchange_weak(assumedTail, assumedNext);
            }
            else if (assumedTail->next.compare_exchange_weak(assumedNext, newNode)) {
                // Now that we managed to link a new node to what we think is the current tail
                // we try to update the tail. If the tail is still what we think it is,
                // it is moved - otherwise some other thread already did that for us.
                tail_.compare_exchange_strong(assumedTail, newNode);
                break;
            }
        }
    }
    void publishUnsafe(BaseNode* newNode) {
        tail_.load()->next.store(newNode);
        tail_.store(newNode);
    }

    BaseNode      head_{};
    TailPtr       tail_{&head_};
    LockFreeStack free_{};
    uint32_t      maxQ_;
};

//! Unbounded non-intrusive lock-free multi-producer single consumer queue.
/*!
 * Based on Dmitriy Vyukov's MPSC queue:
 * https://www.1024cores.net/home/lock-free-algorithms/queues/non-intrusive-mpsc-node-based-queue
 */
template <auto AlignSize = sizeof(void*)>
class MpScPtrQueue {
public:
    using BaseNode = LockFreeStack::Node;
    struct Node : BaseNode {
        void* data{};
    };
    using SafeNodePtr = ThreadSafe<Node*>;
    static Node* toNode(BaseNode* n) { return static_cast<Node*>(n); }
    explicit MpScPtrQueue(Node& sent) : head_(&sent), tail_(&sent) {
        sent.next.store(nullptr, std::memory_order_relaxed);
        sent.data = nullptr;
    }
    MpScPtrQueue(const MpScPtrQueue&)            = delete;
    MpScPtrQueue& operator=(const MpScPtrQueue&) = delete;

    [[nodiscard]] bool empty() const { return tail_->next == nullptr; }
    void               push(Node* n) {
        n->next.store(nullptr, std::memory_order_relaxed);
        Node* p = head_.exchange(n);
        p->next.store(n, std::memory_order_release);
    }
    Node* pop() {
        Node* t = tail_;
        if (Node* n = toNode(t->next.load(std::memory_order_acquire)); n) {
            tail_   = n;
            t->data = n->data;
            n->data = nullptr;
            return t;
        }
        return nullptr;
    }

private:
    SafeNodePtr head_{};              // producers
    alignas(AlignSize) Node* tail_{}; // consumer
};

} // end namespace Clasp::mt
