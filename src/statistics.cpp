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
#include <potassco/match_basic_types.h>
#include <potassco/utils.h>

#include <cctype>
#include <cstring>
#include <unordered_set>

namespace Clasp {
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
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspStatistics
/////////////////////////////////////////////////////////////////////////////////////////
struct ClaspStatistics::Impl {
    using Objects = PodVector_t<StatisticObject>;
    struct IndirectStatsHash {
        static constexpr auto mix = sizeof(std::size_t) == 8 ? static_cast<std::size_t>(0x9e3779b97f4a7c15ULL)
                                                             : static_cast<std::size_t>(0x9e3779b9UL);

        explicit IndirectStatsHash(const Objects* obj) : objects(obj) { POTASSCO_ASSERT(obj != nullptr); }
        auto operator()(StatisticObject o) const noexcept -> std::size_t {
            auto h1  = reinterpret_cast<std::size_t>(o.object());
            auto h2  = reinterpret_cast<std::size_t>(o.typeId());
            h1      ^= h2 + mix + (h1 << 6) + (h1 >> 2);
            return h1;
        }
        auto operator()(uint32_t idx) const noexcept -> std::size_t { return (*this)(objects->at(idx)); }
        auto operator()(uint32_t lhs, uint32_t rhs) const noexcept -> std::size_t {
            return objects->at(lhs) == objects->at(rhs);
        }
        const Objects* objects;
    };
    using Object2Key = std::unordered_set<uint32_t, IndirectStatsHash, IndirectStatsHash>;
    using Strings    = std::unordered_set<std::string>;
    // Distinguished key types - stored in different containers
    template <Type T, uint32_t N>
    using Checked_t = std::conditional_t<static_cast<uint32_t>(T) == N, std::integral_constant<uint32_t, N>, void>;
    enum class KeyType : uint32_t {
        key_val = Checked_t<Type::value, 0u>::value,
        key_arr = Checked_t<Type::array, 1u>::value,
        key_map = Checked_t<Type::map, 2u>::value,
        key_ext = 3u
    };
    //
    static constexpr auto key_shift = 62u;
    static constexpr auto keyType(Key_t key) -> KeyType { return static_cast<KeyType>(key >> key_shift); }
    static constexpr auto keyIdx(Key_t key) -> uint32_t { return static_cast<uint32_t>(key); }
    static constexpr auto writable(Key_t key) -> bool { return keyType(key) != KeyType::key_ext; }
    static constexpr auto makeKey(KeyType type, uint32_t idx) -> Key_t {
        return (static_cast<Key_t>(type) << key_shift) | idx;
    }
    // Type representing a user-created (writable) value.
    struct WritableValue {
        static constexpr auto key_type = KeyType::key_val;
        explicit              operator double() const { return d; }
        explicit              operator StatisticObject() const { return StatisticObject::value(this); }
        //
        double d = 0.0;
    };
    // Type representing a user-created (writable) map.
    struct WritableMap {
        static constexpr auto key_type = KeyType::key_map;
        explicit WritableMap(Impl& i) : self(&i) {}
        explicit           operator StatisticObject() const { return StatisticObject::map(this); }
        [[nodiscard]] auto size() const -> uint32_t { return size32(keys); }
        [[nodiscard]] auto key(uint32_t i) const -> std::string_view { return keys.at(i).first; }
        [[nodiscard]] auto at(std::string_view k) const -> StatisticObject { return self->getObject(child(k)); }
        [[nodiscard]] auto find(std::string_view k) const -> const Key_t* {
            auto it = std::ranges::find_if(keys, [k](const auto& p) { return p.first == k; });
            return it != keys.end() ? &it->second : nullptr;
        }
        [[nodiscard]] auto child(std::string_view k) const -> Key_t {
            const auto* key = find(k);
            POTASSCO_CHECK(key, ERANGE, "WritableMap::at with key '%" PRIsv "'", PRI_SV(k));
            return *key;
        }
        void add(std::string_view n, Key_t k) { keys.push_back(std::pair(n, k)); }
        using Children = PodVector_t<std::pair<std::string_view, Key_t>>;
        Impl*    self{};
        Children keys;
    };
    // Type representing a user-created (writable) array.
    struct WritableArray {
        static constexpr auto key_type = KeyType::key_arr;
        explicit WritableArray(Impl& i) : self(&i) {}
        explicit           operator StatisticObject() const { return StatisticObject::array(this); }
        [[nodiscard]] auto size() const -> uint32_t { return size32(keys); }
        [[nodiscard]] auto at(uint32_t i) const -> StatisticObject { return self->getObject(child(i)); }
        [[nodiscard]] auto child(uint32_t i) const -> Key_t { return keys.at(i); }
        void               add(Key_t key) { keys.push_back(key); }
        using Children = PodVector_t<Key_t>;
        Impl*    self{};
        Children keys;
    };

    Impl() {
        maps.push_back(WritableMap{*this});
        ext.reserve(64);
    }
    ~Impl() {
        PodVector<WritableArray>::destruct(arrays);
        PodVector<WritableMap>::destruct(maps);
    }
    void               freeze(bool b) { frozen.exchange(b == true); }
    [[nodiscard]] auto getObject(Key_t key) const -> StatisticObject {
        static constexpr auto get = [](const auto& container, Key_t k) -> StatisticObject {
            if (auto idx = keyIdx(k); idx < size32(container)) {
                return static_cast<StatisticObject>(container[idx]);
            }
            throwKey(k);
        };
        POTASSCO_CHECK_PRE(not frozen || keyType(key) != KeyType::key_ext, "statistics not (yet) accessible");
        switch (keyType(key)) {
            case KeyType::key_ext: return get(ext, key);
            case KeyType::key_map: return get(maps, key);
            case KeyType::key_arr: return get(arrays, key);
            case KeyType::key_val: return get(values, key);
        }
        POTASSCO_ASSERT_NOT_REACHED("unexpected key type");
    }
    auto addWritable(Type t) -> Key_t {
        static constexpr auto push = []<typename C>(C& cont, auto&... args) {
            using T = typename C::value_type;
            cont.reserve(8);
            auto idx = size32(cont);
            cont.push_back(T{args...});
            return makeKey(T::key_type, idx);
        };
        switch (t) {
            case Type::value: return push(values);
            case Type::array: return push(arrays, *this);
            case Type::map  : return push(maps, *this);
        }
        POTASSCO_ASSERT_NOT_REACHED("unexpected stats type");
    }
    template <typename C>
    static auto ensureWritable(const C& cont, Key_t key) -> uint32_t {
        using T = typename C::value_type;
        if (auto idx = keyIdx(key); keyType(key) == T::key_type && idx < size32(cont)) {
            return idx;
        }
        throwWrite(key, static_cast<Type>(T::key_type));
    }
    auto pushArray(Key_t arrK, Type newObject) -> Key_t {
        auto idx  = ensureWritable(arrays, arrK);
        auto newK = addWritable(newObject); // NOTE: might resize arrays!
        arrays[idx].add(newK);
        return newK;
    }
    auto addMap(Key_t mapK, std::string_view name, Type newObject) -> Key_t {
        auto idx = ensureWritable(maps, mapK);
        if (const auto* key = maps[idx].find(name); key != nullptr) {
            if (auto prevType = keyType(*key); not writable(*key) || static_cast<Type>(prevType) != newObject) {
                throwWrite(*key, newObject);
            }
            return *key;
        }
        auto newKey = addWritable(newObject); // NOTE: might resize maps!
        maps[idx].add(*strings.emplace(name).first, newKey);
        return newKey;
    }
    auto addMap(Key_t mapK, std::string_view name, const StatisticObject& object, bool skipCheck) -> Key_t {
        auto& map = maps[ensureWritable(maps, mapK)];
        if (const auto* key = skipCheck ? nullptr : map.find(name); key != nullptr) {
            POTASSCO_CHECK(object == getObject(*key), EINVAL, "unexpected object for key '%" PRIsv "'", PRI_SV(name));
            return *key;
        }
        auto newKey = makeKey(KeyType::key_ext, addExternalObject(object));
        map.add(name, newKey);
        return newKey;
    }
    void setValue(Key_t valK, double value) {
        auto idx      = ensureWritable(values, valK);
        values[idx].d = value;
    }

    template <typename C>
    auto addOrGetKey(const C& container, const StatisticObject& object) -> Key_t {
        using T = typename C::value_type;
        if (not container.empty() && object.eqTypeId(static_cast<StatisticObject>(container[0]))) {
            auto idx = static_cast<uint32_t>(static_cast<const T*>(object.object()) - container.data());
            return makeKey(T::key_type, idx);
        }
        return mapExternalObject(object);
    }
    auto addOrGetKey(const StatisticObject& object) -> Key_t {
        switch (object.type()) {
            case Type::value: return addOrGetKey(values, object);
            case Type::array: return addOrGetKey(arrays, object);
            case Type::map  : return addOrGetKey(maps, object);
        }
        POTASSCO_ASSERT_NOT_REACHED("unexpected stats type");
    }
    auto addExternalObject(const StatisticObject& object) -> uint32_t {
        auto idx = size32(ext);
        ext.push_back(object);
        return idx;
    }
    auto mapExternalObject(const StatisticObject& object) -> Key_t {
        // Eagerly assume object is not yet in the index
        auto idx = addExternalObject(object);
        if (auto [it, added] = index.emplace(idx); not added) {
            // object already exists in the index
            ext.pop_back();
            idx = *it;
        }
        return makeKey(KeyType::key_ext, idx);
    }
    auto getChildKey(Key_t key, uint32_t idx) -> Key_t {
        auto object = getObject(key);
        if (object.type() == Type::array) {
            return keyType(key) == KeyType::key_arr ? array(key).child(idx) : mapExternalObject(object[idx]);
        }
        throwType(Type::array, object.type());
    }
    auto getChildKey(Key_t key, std::string_view path) -> Key_t {
        auto object = getObject(key);
        auto type   = object.type();
        auto hasKey = true;
        if (type != Type::map) {
            throwType(Type::map, type);
        }
        static constexpr auto popNext = [](std::string_view& parent,
                                           bool              parseNum) -> std::pair<std::string_view, uint32_t> {
            auto res = std::pair{parent.substr(0, parent.find('.')), 0u};
            parent.remove_prefix(std::min(res.first.length() + 1, parent.length()));
            if (int n; parseNum) {
                auto r     = res.first;
                res.second = static_cast<uint32_t>(Potassco::matchNum(r, nullptr, &n) && n >= 0 && r.empty() ? n : -1);
            }
            return res;
        };
        for (auto p = path; not p.empty();) {
            auto [top, idx] = popNext(p, type == Type::array);
            auto error      = false;
            try {
                if (type == Type::value || (type == Type::array && idx >= object.size())) {
                    error = true;
                }
                else if (writable(key)) {
                    key    = keyType(key) == KeyType::key_map ? map(key).child(top) : array(key).child(idx);
                    object = getObject(key);
                }
                else {
                    object = type == Type::map ? object.at(top) : object[idx];
                    hasKey = false;
                }
            }
            catch (const std::exception&) {
                error = true;
            }
            if (error) {
                path = path.substr(0, static_cast<std::size_t>((top.data() + top.size()) - path.data()));
                throwPath(path, top);
            }
            type = object.type();
        }
        return hasKey ? key : addOrGetKey(object);
    }

    auto root() -> WritableMap& { return maps[0]; }
    auto array(Key_t key) -> WritableArray& { return arrays.at(keyIdx(key)); }
    auto map(Key_t key) -> WritableMap& { return maps.at(keyIdx(key)); }

    using Values = PodVector_t<WritableValue>;
    using Maps   = PodVector_t<WritableMap>;
    using Arrays = PodVector_t<WritableArray>;
    Objects    ext;     // external (non-writable) StatisticObjects not owned by this
    Maps       maps;    // writable maps
    Arrays     arrays;  // writable arrays
    Values     values;  // writable values
    Strings    strings; // added string keys used in writable maps
    Object2Key index{0u, IndirectStatsHash{&ext}, IndirectStatsHash{&ext}}; // index over ext
    SigAtomic  frozen;                                                      // whether access is currently allowed
};
ClaspStatistics::ClaspStatistics() : impl_(std::make_unique<Impl>()) {}
ClaspStatistics::~ClaspStatistics() = default;
auto ClaspStatistics::addObject(Key_t k, std::string_view name, StatisticObject o, bool skipCheck) -> Key_t {
    return impl_->addMap(k, name, o, skipCheck);
}
bool ClaspStatistics::visitExternal(std::string_view name, StatsVisitor& visitor) const {
    if (const auto* key = impl_->root().find(name); key != nullptr) {
        visitor.visitExternalStats(impl_->getObject(*key));
        return true;
    }
    return false;
}
void ClaspStatistics::freeze(bool b) { impl_->freeze(b); }
auto ClaspStatistics::root() const -> Key_t { return Impl::makeKey(Impl::KeyType::key_map, 0); }
auto ClaspStatistics::type(Key_t key) const -> Type { return impl_->getObject(key).type(); }
auto ClaspStatistics::size(Key_t key) const -> size_t { return impl_->getObject(key).size(); }
bool ClaspStatistics::writable(Key_t key) const { return Impl::writable(key); }
auto ClaspStatistics::key(Key_t mapK, size_t i) const -> std::string_view {
    return impl_->getObject(mapK).key(toU32(i));
}
auto ClaspStatistics::at(Key_t arrK, size_t index) const -> Key_t { return impl_->getChildKey(arrK, toU32(index)); }
auto ClaspStatistics::get(Key_t mapK, std::string_view path) const -> Key_t { return impl_->getChildKey(mapK, path); }
auto ClaspStatistics::push(Key_t arr, Type type) -> Key_t { return impl_->pushArray(arr, type); }
auto ClaspStatistics::add(Key_t mapK, std::string_view name, Type type) -> Key_t {
    return impl_->addMap(mapK, name, type);
}
auto ClaspStatistics::value(Key_t key) const -> double { return impl_->getObject(key).value(); }
void ClaspStatistics::set(Key_t key, double value) { impl_->setValue(key, value); }
bool ClaspStatistics::find(Key_t mapK, std::string_view element, Key_t* outKey) const {
    try {
        if (auto key = impl_->getChildKey(mapK, element); outKey) {
            *outKey = key;
        }
        return true;
    }
    catch (const std::exception&) {
        return false;
    }
}
} // namespace Clasp
