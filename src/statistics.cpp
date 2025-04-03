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
#include <clasp/statistics.h>

#include <clasp/util/misc_types.h>

#include <potassco/error.h>

#include <cctype>
#include <cstring>
#include <stdexcept>
#include <unordered_set>

namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// StatisticObject
/////////////////////////////////////////////////////////////////////////////////////////
StatisticObject::V      StatisticObject::s_empty_(+[](const void*) { return 0.0; });
StatisticObject::RegVec StatisticObject::s_types_(1, &StatisticObject::s_empty_);

StatisticObject::StatisticObject() : handle_(0) {}
StatisticObject::StatisticObject(uint64_t h) : handle_(h) {}
StatisticObject::StatisticObject(const void* obj, uint32_t type) {
    handle_  = static_cast<uint64_t>(type) << 48;
    handle_ |= static_cast<uint64_t>(reinterpret_cast<uintptr_t>(obj));
}
const void* StatisticObject::self() const {
    static constexpr auto ptr_mask = Potassco::bit_max<uint64_t>(48);
    return reinterpret_cast<const void*>(static_cast<uintptr_t>(handle_ & ptr_mask));
}
std::size_t StatisticObject::typeId() const { return static_cast<uint32_t>(handle_ >> 48); }
auto        StatisticObject::tid() const -> const I* { return s_types_.at(static_cast<uint32_t>(handle_ >> 48)); }
auto        StatisticObject::type() const -> Type { return handle_ ? tid()->type : Type::value; }
uint32_t    StatisticObject::size() const {
    switch (type()) {
        default         : POTASSCO_ASSERT_NOT_REACHED("invalid object");
        case Type::value: return 0;
        case Type::array: return tid()->as<A>()->size(self());
        case Type::map  : return tid()->as<M>()->size(self());
    }
}
const char* StatisticObject::key(uint32_t i) const {
    POTASSCO_CHECK_PRE(type() == Type::map, "type error");
    return tid()->as<M>()->key(self(), i);
}
StatisticObject StatisticObject::at(const char* k) const {
    POTASSCO_CHECK_PRE(type() == Type::map, "type error");
    return tid()->as<M>()->at(self(), k);
}
StatisticObject StatisticObject::operator[](uint32_t i) const {
    POTASSCO_CHECK_PRE(type() == Type::array, "type error");
    return tid()->as<A>()->at(self(), i);
}
double StatisticObject::value() const {
    POTASSCO_CHECK_PRE(type() == Type::value, "type error");
    return tid()->as<V>()->value(self());
}
std::size_t     StatisticObject::hash() const { return std::hash<uint64_t>()(toRep()); }
uint64_t        StatisticObject::toRep() const { return handle_; }
StatisticObject StatisticObject::fromRep(uint64_t x) {
    StatisticObject r(x);
    POTASSCO_CHECK_PRE(r.tid() != nullptr && not Potassco::test_any(reinterpret_cast<uintptr_t>(r.self()), 3u),
                       "invalid key");
    return r;
}
/////////////////////////////////////////////////////////////////////////////////////////
// StatsMap
/////////////////////////////////////////////////////////////////////////////////////////
StatisticObject StatsMap::at(const char* k) const {
    if (const auto* o = find(k)) {
        return *o;
    }
    POTASSCO_CHECK(false, ERANGE, "StatsMap::at with key '%s'", k);
}
const StatisticObject* StatsMap::find(const char* k) const {
    auto it = std::ranges::find_if(keys_, [k](const auto& st) { return std::strcmp(st.first, k) == 0; });
    return it != keys_.end() ? &it->second : nullptr;
}
bool StatsMap::add(const char* k, const StatisticObject& o) {
    return not find(k) && (keys_.push_back(MapType::value_type(k, o)), true);
}
void StatsMap::push(const char* k, const StatisticObject& o) { keys_.push_back(MapType::value_type(k, o)); }
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspStatistics
/////////////////////////////////////////////////////////////////////////////////////////
struct ClaspStatistics::Impl {
    using KeySet    = std::unordered_set<uint64_t>;
    using StringSet = std::unordered_set<Potassco::ConstString, std::hash<Potassco::ConstString>, std::equal_to<>>;
    struct Map : StatsMap {
        static const std::size_t id_s;
    };
    struct Arr : PodVector_t<StatisticObject> {
        static const std::size_t id_s;

        [[nodiscard]] StatisticObject toStats() const { return StatisticObject::array(this); }
    };
    struct Val {
        static const std::size_t id_s;

        Val(double d) : value(d) {} // NOLINT(*-explicit-constructor)
        explicit operator double() const { return value; }
        double   value;
    };

    Impl() = default;

    ~Impl() {
        for (auto key : objects) { destroyIfWritable(key); }
    }

    Key_t add(const StatisticObject& o) { return *objects.insert(o.toRep()).first; }

    static void destroyIfWritable(Key_t k) {
        try {
            StatisticObject obj = StatisticObject::fromRep(k);
            if (size_t typeId = obj.typeId(); typeId == Map::id_s) {
                delete static_cast<const Map*>(obj.self());
            }
            else if (typeId == Arr::id_s) {
                delete static_cast<const Arr*>(obj.self());
            }
            else if (typeId == Val::id_s) {
                delete static_cast<const Val*>(obj.self());
            }
        }
        catch (const std::exception&) {
            POTASSCO_ASSERT_NOT_REACHED("unexpected exception");
        }
    }
    StatisticObject newWritable(Type type) {
        StatisticObject obj;
        switch (type) {
            case Type::value: obj = StatisticObject::value(new Val(0.0)); break;
            case Type::map  : obj = StatisticObject::map(new Map()); break;
            case Type::array: obj = StatisticObject::array(new Arr()); break;
            default         : POTASSCO_ASSERT_NOT_REACHED("unsupported statistic object type");
        }
        add(obj);
        return obj;
    }

    bool writable(Key_t k) const {
        auto typeId = StatisticObject::fromRep(k).typeId();
        return (typeId == Map::id_s || typeId == Arr::id_s || typeId == Val::id_s) && objects.contains(k);
    }

    bool remove(const StatisticObject& o) {
        if (auto it = objects.find(o.toRep()); it != objects.end() && not emptyKey(*it)) {
            destroyIfWritable(*it);
            objects.erase(it);
            return true;
        }
        return false;
    }

    StatisticObject get(Key_t k) const {
        POTASSCO_CHECK_PRE(objects.contains(k), "invalid key");
        return StatisticObject::fromRep(k);
    }

    template <class T>
    T* writable(Key_t k) const {
        StatisticObject obj = StatisticObject::fromRep(k);
        POTASSCO_CHECK_PRE(writable(k), "key not writable");
        POTASSCO_CHECK_PRE(T::id_s == obj.typeId(), "type error");
        return static_cast<T*>(const_cast<void*>(obj.self()));
    }

    void update(const StatisticObject& obj) {
        KeySet seen;
        visit(obj, seen);
        if (objects.size() != seen.size()) {
            for (auto o : objects) {
                if (not seen.contains(o)) {
                    destroyIfWritable(o);
                }
            }
            objects.swap(seen);
        }
    }

    void visit(const StatisticObject& obj, KeySet& visited) {
        if (auto it = objects.find(obj.toRep()); it == objects.end() || not visited.insert(*it).second) {
            return;
        }
        switch (obj.type()) {
            case Type::map:
                for (auto i : irange(obj)) { visit(obj.at(obj.key(i)), visited); }
                break;
            case Type::array:
                for (auto i : irange(obj)) { visit(obj[i], visited); }
                break;
            default: break;
        }
    }

    const char* string(const char* s) {
        auto view = std::string_view{s};
        auto it   = strings.find(view);
        if (it != strings.end()) {
            return it->c_str();
        }
        return strings.insert(it, Potassco::ConstString(view, Potassco::ConstString::create_unique))->c_str();
    }
    static Key_t key(const StatisticObject& obj) { return static_cast<Key_t>(obj.toRep()); }
    static bool  emptyKey(Key_t k) { return k == 0; }

    KeySet    objects;
    StringSet strings;
    Key_t     root{0};
    uint32_t  gc{0};
    uint32_t  rem{0};
};
const std::size_t ClaspStatistics::Impl::Map::id_s = StatisticObject::map(static_cast<Map*>(nullptr)).typeId();
const std::size_t ClaspStatistics::Impl::Arr::id_s = StatisticObject::array(static_cast<Arr*>(nullptr)).typeId();
const std::size_t ClaspStatistics::Impl::Val::id_s = StatisticObject::value(static_cast<Val*>(nullptr)).typeId();

ClaspStatistics::ClaspStatistics() : impl_(std::make_unique<Impl>()) {}
ClaspStatistics::ClaspStatistics(StatisticObject root) : ClaspStatistics() { impl_->root = impl_->add(root); }
ClaspStatistics::~ClaspStatistics() = default;
auto   ClaspStatistics::getObject(Key_t k) const -> StatisticObject { return impl_->get(k); }
auto   ClaspStatistics::root() const -> Key_t { return impl_->root; }
auto   ClaspStatistics::type(Key_t key) const -> Type { return getObject(key).type(); }
size_t ClaspStatistics::size(Key_t key) const { return getObject(key).size(); }
bool   ClaspStatistics::writable(Key_t key) const { return impl_->writable(key); }
auto ClaspStatistics::at(Key_t arrK, size_t index) const -> Key_t { return impl_->add(getObject(arrK)[toU32(index)]); }
auto ClaspStatistics::key(Key_t mapK, size_t i) const -> const char* { return getObject(mapK).key(toU32(i)); }
auto ClaspStatistics::get(Key_t mapK, const char* path) const -> Key_t {
    return impl_->add(not std::strchr(path, '.') ? getObject(mapK).at(path) : findObject(mapK, path));
}
bool ClaspStatistics::find(Key_t mapK, const char* element, Key_t* outKey) const {
    try {
        if (not writable(mapK) || std::strchr(element, '.')) {
            findObject(mapK, element, outKey);
            return true;
        }
        auto* map = impl_->writable<Impl::Map>(mapK);
        if (const StatisticObject* obj = map->find(element)) {
            if (outKey) {
                *outKey = impl_->add(*obj);
            }
            return true;
        }
    }
    catch (const std::exception&) { // NOLINT(*-empty-catch)
        // fallthrough
    }
    return false;
}
double ClaspStatistics::value(Key_t key) const { return getObject(key).value(); }
auto   ClaspStatistics::changeRoot(Key_t newRoot) -> Key_t {
    auto old    = impl_->root;
    impl_->root = impl_->add(getObject(newRoot));
    return old;
}
StatsMap* ClaspStatistics::makeRoot() {
    auto* root  = new Impl::Map();
    impl_->root = impl_->add(StatisticObject::map(root));
    return root;
}
bool ClaspStatistics::removeStat(const StatisticObject& obj, bool recurse) {
    bool ret = impl_->remove(obj);
    if (ret && recurse) {
        if (obj.type() == Type::map) {
            for (auto i : irange(obj)) { removeStat(obj.at(obj.key(i)), true); }
        }
        else if (obj.type() == Type::array) {
            for (auto i : irange(obj)) { removeStat(obj[i], true); }
        }
    }
    return ret;
}
bool ClaspStatistics::removeStat(Key_t k, bool recurse) {
    try {
        return removeStat(impl_->get(k), recurse);
    }
    catch (const std::logic_error&) {
        return false;
    }
}
void ClaspStatistics::update() {
    if (impl_->root) {
        impl_->update(getObject(impl_->root));
    }
}

static bool getIndex(const char* top, uint32_t& idx) {
    idx = 0;
    while (std::isdigit(static_cast<unsigned char>(*top))) {
        idx *= 10;
        idx += static_cast<unsigned>(*top++ - '0');
    }
    return not *top;
}

StatisticObject ClaspStatistics::findObject(Key_t root, const char* path, Key_t* res) const {
    auto o = getObject(root);
    auto t = o.type();
    char temp[1024];
    for (const char* parent = path; path && *path;) {
        const char* top = path;
        if (path = std::strchr(path, '.'); path != nullptr) {
            auto len = static_cast<std::size_t>(path++ - top);
            POTASSCO_ASSERT(len < 1024, "invalid key");
            top       = static_cast<const char*>(std::memcpy(temp, top, len));
            temp[len] = 0;
        }
        if (t == Type::map) {
            o = o.at(top);
        }
        else if (uint32_t pos; t == Type::array && getIndex(top, pos)) {
            o = o[pos];
        }
        else {
            POTASSCO_CHECK(false, ERANGE, "invalid path: '%s' at key '%s'", parent, top);
        }
        t = o.type();
    }
    POTASSCO_ASSERT(o.toRep() != 0);
    if (res) {
        *res = impl_->add(o);
    }
    return o;
}
auto ClaspStatistics::push(Key_t key, Type type) -> Key_t {
    auto* arr = impl_->writable<Impl::Arr>(key);
    auto  obj = impl_->newWritable(type);
    arr->push_back(obj);
    return Impl::key(obj);
}
auto ClaspStatistics::add(Key_t mapK, const char* name, Type type) -> Key_t {
    auto* map = impl_->writable<Impl::Map>(mapK);
    if (const StatisticObject* stat = map->find(name)) {
        POTASSCO_CHECK_PRE(stat->type() == type, "redefinition error");
        return Impl::key(*stat);
    }
    auto stat = impl_->newWritable(type);
    map->push(impl_->string(name), stat);
    return Impl::key(stat);
}
void ClaspStatistics::set(Key_t key, double value) {
    auto* val = impl_->writable<Impl::Val>(key);
    *val      = value;
}
/////////////////////////////////////////////////////////////////////////////////////////
// StatsVisitor
/////////////////////////////////////////////////////////////////////////////////////////
StatsVisitor::~StatsVisitor() = default;
bool StatsVisitor::visitGenerator(Operation) { return true; }
bool StatsVisitor::visitThreads(Operation) { return true; }
bool StatsVisitor::visitTester(Operation) { return true; }
bool StatsVisitor::visitHccs(Operation) { return true; }
void StatsVisitor::visitHcc(uint32_t, const ProblemStats& p, const SolverStats& s) {
    visitProblemStats(p);
    visitSolverStats(s);
}
void StatsVisitor::visitThread(uint32_t, const SolverStats& stats) { visitSolverStats(stats); }

} // namespace Clasp
