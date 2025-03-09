//
// Copyright (c) 2016-present Benjamin Kaufmann
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
//! \file
//! \brief Types and functions for accessing statistics.
#pragma once

#include <clasp/claspfwd.h>
#include <clasp/pod_vector.h>
#include <potassco/clingo.h>
namespace Clasp {

//! Discriminated union representing either a single statistic value or a composite.
class StatisticObject {
public:
    using Type = Potassco::StatisticsType;
    //! Creates a Type::value object with value 0.0.
    StatisticObject();
    //! Creates a Type::value object - static_cast<double>(*obj) shall be valid.
    template <typename T>
    static StatisticObject value(const T* obj) {
        return value<T, toDouble>(obj);
    }
    //! Creates a mapped Type::value object: f(obj) -> double
    template <typename T, double (*Op)(const T*)>
    static StatisticObject value(const T* obj) {
        return StatisticObject(obj, registerValue<T, Op>());
    }
    //! Creates a Type::map object.
    /*!
     * The following expression shall be valid:
     * - obj->size(): shall return the number of keys in obj
     * - obj->key(i): shall return the i-th key of this object (i >= 0).
     * - obj->at(const char* k): shall return the StatisticObject under the given key.
     *  If k is invalid, shall either throw an exception or return an empty object.
     */
    template <typename T>
    static StatisticObject map(const T* obj) {
        return StatisticObject(obj, registerMap<T>());
    }
    //! Creates a Type::array object.
    /*!
     * The following expression shall be valid:
     * - obj->size(): shall return the size of the array.
     * - obj->at(i): shall return the StatisticObject under the given index i >= 0.
     *  If the index is invalid, shall either throw an exception or return an empty object.
     */
    template <typename T>
    static StatisticObject array(const T* obj) {
        return StatisticObject(obj, registerArray<T>());
    }
    //! Returns the type of this object.
    [[nodiscard]] Type type() const;
    //! Returns the number of children of this object or 0 if this is not a composite object.
    [[nodiscard]] uint32_t size() const;

    /*!
     * \name Map
     * \pre type() == Type::map
     */
    //@{
    //! Returns the i-th key of this map.
    /*!
     * \pre i < size()
     */
    [[nodiscard]] const char* key(uint32_t i) const;
    //! Returns the object under the given key.
    /*!
     * \pre k in key([0;size()))
     */
    StatisticObject at(const char* k) const;
    //@}

    //! Returns the object at the given index.
    /*!
     * \pre type() == Type::array
     * \pre i < size()
     */
    StatisticObject operator[](uint32_t i) const;

    //! Returns the value of this object.
    /*!
     * \pre type() == Type::value
     */
    [[nodiscard]] double value() const;

    [[nodiscard]] std::size_t hash() const;
    [[nodiscard]] uint64_t    toRep() const;
    [[nodiscard]] const void* self() const;
    [[nodiscard]] std::size_t typeId() const;
    static StatisticObject    fromRep(uint64_t);

    bool operator==(const StatisticObject&) const  = default;
    auto operator<=>(const StatisticObject&) const = default;

private:
    template <typename T>
    static double toDouble(const T* v) {
        return static_cast<double>(*v);
    }
    struct I {
        using ObjPtr = const void*;
        explicit I(Type t) : type(t) {}
        template <typename T>
        const T* as() const {
            return static_cast<const T*>(this);
        }
        Type type;
    };
    struct V : I {
        explicit V(double (*v)(ObjPtr)) : I(Type::value), value(v) {}
        double (*value)(ObjPtr);
    };
    struct A : I {
        A(uint32_t (*sz)(ObjPtr), StatisticObject (*a)(ObjPtr, uint32_t)) : I(Type::array), size(sz), at(a) {}
        uint32_t (*size)(ObjPtr);
        StatisticObject (*at)(ObjPtr, uint32_t);
    };
    struct M : I {
        M(uint32_t (*sz)(ObjPtr), StatisticObject (*a)(ObjPtr, const char*), const char* (*k)(ObjPtr, uint32_t))
            : I(Type::map)
            , size(sz)
            , at(a)
            , key(k) {}
        uint32_t (*size)(ObjPtr);
        StatisticObject (*at)(ObjPtr, const char*);
        const char* (*key)(ObjPtr, uint32_t);
    };
    static uint32_t registerType(const I* vtab) {
        s_types_.push_back(vtab);
        return size32(s_types_) - 1;
    }
    template <typename T, double (*Fun)(const T*)>
    static uint32_t registerValue();
    template <typename T>
    static uint32_t registerMap();
    template <typename T>
    static uint32_t registerArray();
    StatisticObject(const void* obj, uint32_t type);
    explicit StatisticObject(uint64_t h);

    using RegVec = PodVector_t<const I*>;
    [[nodiscard]] const I* tid() const;
    static V               s_empty_;
    static RegVec          s_types_;
    uint64_t               handle_;
};

template <typename T>
uint32_t StatisticObject::registerArray() {
    static const struct Array_t : A {
        Array_t() : A(&Array_t::size, &Array_t::at) {}
        static uint32_t        size(ObjPtr obj) { return toU32(static_cast<const T*>(obj)->size()); }
        static StatisticObject at(ObjPtr obj, uint32_t i) { return static_cast<const T*>(obj)->at(i); }
    } vtab_s;
    static const uint32_t id = registerType(&vtab_s);
    return id;
}
template <typename T>
uint32_t StatisticObject::registerMap() {
    static const struct Map_t : M {
        Map_t() : M(&Map_t::size, &Map_t::at, &Map_t::key) {}
        static const T*        cast(ObjPtr obj) { return static_cast<const T*>(obj); }
        static uint32_t        size(ObjPtr obj) { return cast(obj)->size(); }
        static StatisticObject at(ObjPtr obj, const char* k) { return cast(obj)->at(k); }
        static const char*     key(ObjPtr obj, uint32_t i) { return cast(obj)->key(i); }
    } vtab_s;
    static const uint32_t id = registerType(&vtab_s);
    return id;
}

template <typename T, double (*Fun)(const T*)>
uint32_t StatisticObject::registerValue() {
    static const struct Value_t : V {
        Value_t() : V(&Value_t::value) {}
        static double value(ObjPtr obj) { return Fun(static_cast<const T*>(obj)); }
    } vtab_s;
    static const uint32_t id = StatisticObject::registerType(&vtab_s);
    return id;
}
//! A type that maps string keys to statistic objects.
class StatsMap {
public:
    // StatisticObject
    [[nodiscard]] uint32_t    size() const { return size32(keys_); }
    [[nodiscard]] const char* key(uint32_t i) const { return keys_.at(i).first; }
    StatisticObject           at(const char* k) const;
    // Own interface
    const StatisticObject*        find(const char* k) const;
    bool                          add(const char* k, const StatisticObject&);
    void                          push(const char* k, const StatisticObject&);
    [[nodiscard]] StatisticObject toStats() const { return StatisticObject::map(this); }

private:
    using MapType = PodVector_t<std::pair<const char*, StatisticObject>>;
    MapType keys_;
};
//! An array of statistic objects.
template <typename T, Potassco::StatisticsType ElemType = Potassco::StatisticsType::map>
class StatsVec : private PodVector_t<T*> {
public:
    StatsVec() = default;
    ~StatsVec() {
        if (own_) {
            for (auto* s : *this) { delete s; }
        }
    }
    StatsVec(const StatsVec&)            = delete;
    StatsVec& operator=(const StatsVec&) = delete;

    using base_type      = PodVector_t<T*>;                    // NOLINT
    using const_iterator = typename base_type::const_iterator; // NOLINT
    using iterator       = typename base_type::iterator;       // NOLINT
    using base_type::size;
    using base_type::operator[];
    using base_type::begin;
    using base_type::empty;
    using base_type::end;
    void growTo(uint32_t newSize) {
        if (newSize > size()) {
            this->resize(newSize);
        }
    }
    void reset() {
        for (T* s : *this) { s->reset(); }
    }
    [[nodiscard]] StatisticObject at(uint32_t i) const {
        const T* ptr = this->base_type::at(i);
        if constexpr (ElemType == Potassco::StatisticsType::map) {
            return StatisticObject::map(ptr);
        }
        else if constexpr (ElemType == Potassco::StatisticsType::array) {
            return StatisticObject::array(ptr);
        }
        else {
            static_assert(ElemType == Potassco::StatisticsType::value, "invalid element type");
            return StatisticObject::value(ptr);
        }
    }
    [[nodiscard]] StatisticObject toStats() const { return StatisticObject::array(this); }
    void                          acquire() { own_ = true; }
    void                          release() { own_ = false; }

private:
    bool own_{true};
};

//! A class for traversing, querying, and adding statistics.
/*!
 * \ingroup clingo
 */
class ClaspStatistics : public Potassco::AbstractStatistics {
public:
    ClaspStatistics();
    explicit ClaspStatistics(StatisticObject root);
    ~ClaspStatistics() override;
    ClaspStatistics(ClaspStatistics&&) = delete;

    StatsMap* makeRoot();

    // Base interface
    [[nodiscard]] Key_t       root() const override;
    [[nodiscard]] Type        type(Key_t key) const override;
    [[nodiscard]] size_t      size(Key_t key) const override;
    [[nodiscard]] bool        writable(Key_t key) const override;
    [[nodiscard]] Key_t       at(Key_t arrK, size_t index) const override;
    Key_t                     push(Key_t arr, Type type) override;
    [[nodiscard]] const char* key(Key_t mapK, size_t i) const override;
    Key_t                     get(Key_t mapK, const char* key) const override;
    bool                      find(Key_t mapK, const char* element, Key_t* outKey) const override;
    Key_t                     add(Key_t mapK, const char* name, Type type) override;
    [[nodiscard]] double      value(Key_t key) const override;
    void                      set(Key_t key, double value) override;

    Key_t changeRoot(Key_t newRoot);
    bool  removeStat(const StatisticObject&, bool recurse);
    bool  removeStat(Key_t k, bool recurse);

    // Remove unreachable stats
    void                          update();
    [[nodiscard]] StatisticObject getObject(Key_t k) const;

private:
    StatisticObject findObject(Key_t root, const char* path, Key_t* track = nullptr) const;
    struct Impl;
    std::unique_ptr<Impl> impl_;
};

struct SolverStats;
struct ProblemStats;

//! Interface for visiting statistics.
/*!
 * \ingroup facade
 */
class StatsVisitor {
public:
    enum Operation { enter, leave };
    virtual ~StatsVisitor();
    // compound
    virtual bool visitGenerator(Operation op); // default: return true
    virtual bool visitThreads(Operation op);   // default: return true
    virtual bool visitTester(Operation op);    // default: return true
    virtual bool visitHccs(Operation op);      // default: return true

    // leafs
    virtual void visitThread(uint32_t, const SolverStats& stats);
    virtual void visitHcc(uint32_t, const ProblemStats& p, const SolverStats& s);
    virtual void visitLogicProgramStats(const Asp::LpStats& stats) = 0;
    virtual void visitProblemStats(const ProblemStats& stats)      = 0;
    virtual void visitSolverStats(const SolverStats& stats)        = 0;
    virtual void visitExternalStats(const StatisticObject& stats)  = 0;
};

} // namespace Clasp
