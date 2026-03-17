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
    // Distinguished key types - stored in different containers
    template <Type T, uint32_t N>
    using Checked_t = std::conditional_t<static_cast<uint32_t>(T) == N, std::integral_constant<uint32_t, N>, void>;
    enum class KeyType : uint32_t {
        key_val = Checked_t<Type::value, 0u>::value,
        key_arr = Checked_t<Type::array, 1u>::value,
        key_map = Checked_t<Type::map, 2u>::value,
        key_ext = 3u
    };
    static constexpr auto key_type_mask = 3u;
    static constexpr auto key_shift     = 2u;
    enum class Key : uint32_t {};
    static constexpr auto toN(Key k) -> uint32_t { return Potassco::to_underlying(k); }
    //
    static constexpr auto keyType(Key key) -> KeyType { return static_cast<KeyType>(toN(key) & key_type_mask); }
    static constexpr auto keyIdx(Key key) -> uint32_t { return toN(key) >> key_shift; }
    static constexpr auto writable(Key key) -> bool { return keyType(key) != KeyType::key_ext; }
    static constexpr auto makeKey(KeyType type, uint32_t idx) -> Key {
        return static_cast<Key>((idx << key_shift) | static_cast<uint32_t>(type));
    }
    static constexpr void checkRange(const StatisticObject& o, std::size_t idx) {
        if (auto os = o.size(); idx >= os) {
            throwRange(idx, os);
        }
    }
    // Type representing a user-created (writable) map.
    struct WritableMap {
        explicit WritableMap(Impl& i) : self(&i) {}
        [[nodiscard]] auto size() const -> uint32_t { return size32(keys); }
        [[nodiscard]] auto key(uint32_t i) const -> std::string_view { return keys.at(i).first; }
        [[nodiscard]] auto at(std::string_view k) const -> StatisticObject { return self->getObject(child(k)); }
        [[nodiscard]] auto find(std::string_view k) const -> const Key* {
            auto it = std::ranges::find_if(keys, [k](const auto& p) { return p.first == k; });
            return it != keys.end() ? &it->second : nullptr;
        }
        [[nodiscard]] auto child(std::string_view k) const -> Key {
            const auto* key = find(k);
            POTASSCO_CHECK(key, ERANGE, "WritableMap::at with key '%" PRIsv "'", PRI_SV(k));
            return *key;
        }
        void add(std::string_view n, Key k) { keys.push_back(std::pair(n, k)); }
        using Children = PodVector_t<std::pair<std::string_view, Key>>;
        Impl*    self{};
        Children keys;
    };
    // Type representing a user-created (writable) array.
    struct WritableArray {
        explicit WritableArray(Impl& i) : self(&i) {}
        [[nodiscard]] auto size() const -> uint32_t { return size32(keys); }
        [[nodiscard]] auto at(uint32_t i) const -> StatisticObject { return self->getObject(child(i)); }
        [[nodiscard]] auto child(uint32_t i) const -> Key { return keys.at(i); }
        uint32_t           add(Key key) {
            keys.push_back(key);
            return size32(keys) - 1;
        }
        using Children = PodVector_t<Key>;
        Impl*    self{};
        Children keys;
    };

    Impl() {
        maps.push_back(WritableMap{*this});
        ext.reserve(8);
    }
    ~Impl() {
        PodVector<WritableArray>::destruct(arrays);
        PodVector<WritableMap>::destruct(maps);
    }
    void freeze(bool b) {
        frozen.exchange(b == true);
        cache = {};
    }
    [[nodiscard]] auto getObject(Key key) const -> StatisticObject {
        static constexpr auto get = []<typename C>(const C& container, Key k) -> const typename C::value_type& {
            if (auto idx = keyIdx(k); idx < size32(container)) {
                return container[idx];
            }
            POTASSCO_FAIL(ERANGE);
        };
        switch (keyType(key)) {
            case KeyType::key_ext:
                POTASSCO_CHECK_PRE(not frozen, "statistics not (yet) accessible");
                return get(ext, key);
            case KeyType::key_map: return StatisticObject::map(&get(maps, key));
            case KeyType::key_arr: return StatisticObject::array(&get(arrays, key));
            case KeyType::key_val: return StatisticObject::value(&get(values, key));
        }
        POTASSCO_ASSERT_NOT_REACHED("unexpected key type");
    }

    auto lookup(Path_t path) -> std::pair<Key, StatisticObject> {
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
        if (path.starts_with('.')) {
            path.remove_prefix(1);
        }
        if (not path.empty() && path == cache.path) {
            return {cache.key, cache.object};
        }
        auto key    = makeKey(KeyType::key_map, 0);
        auto object = getObject(key);
        auto scan   = path;
        if (not cache.path.empty() && scan.starts_with(cache.path) && scan[cache.path.size()] == '.') {
            key    = cache.key;
            object = cache.object;
            scan.remove_prefix(cache.path.size() + 1);
        }
        for (auto p = scan; not p.empty();) {
            auto type       = object.type();
            auto [top, idx] = popNext(p, type == Type::array);
            try {
                POTASSCO_CHECK(type == Type::map || (type == Type::array && idx < object.size()), EINVAL);
                if (writable(key)) {
                    key    = keyType(key) == KeyType::key_map ? map(key).child(top) : array(key).child(idx);
                    object = getObject(key);
                }
                else {
                    object = type == Type::map ? object.at(top) : object[idx];
                }
            }
            catch (const std::exception&) {
                if (type == Type::array && idx >= object.size()) {
                    throwRange(idx, object.size());
                }
                path = path.substr(0, static_cast<std::size_t>((top.data() + top.size()) - path.data()));
                throwPath(path, top);
            }
        }
        cache.path   = path;
        cache.key    = key;
        cache.object = object;
        return {key, object};
    }
    auto lookup(Path_t path, Type expected) -> decltype(lookup(path)) {
        auto res = lookup(path);
        if (auto t = res.second.type(); t != expected) {
            throwType(expected, t);
        }
        return res;
    }

    auto ensureWritable(Path_t path, Type type, Key key) const -> uint32_t {
        if (writable(key) && getObject(key).type() == type) {
            return keyIdx(key);
        }
        throwWrite(path, type);
    }
    auto addWritable(Type t) -> Key {
        static constexpr auto push = []<typename C, typename T>(KeyType kt, C& cont, const T& elem) {
            cont.reserve(8);
            cont.push_back(elem);
            return makeKey(kt, size32(cont) - 1);
        };
        switch (t) {
            case Type::value: return push(KeyType::key_val, values, 0.0);
            case Type::array: return push(KeyType::key_arr, arrays, WritableArray{*this});
            case Type::map  : return push(KeyType::key_map, maps, WritableMap{*this});
        }
        POTASSCO_ASSERT_NOT_REACHED("unexpected stats type");
    }
    void addMap(Path_t path, std::string_view name, const StatisticObject& object, bool skipCheck) {
        auto [key, parent] = lookup(path, Type::map);
        auto& map          = maps[ensureWritable(path, Type::map, key)];
        if (const auto* sk = skipCheck ? nullptr : map.find(name); sk != nullptr) {
            POTASSCO_CHECK(not writable(*sk) && object == external(*sk), EINVAL,
                           "unexpected object for key '%" PRIsv "'", PRI_SV(name));
            return;
        }
        ext.push_back(object);
        auto newKey = makeKey(KeyType::key_ext, size32(ext) - 1);
        map.add(name, newKey);
    }
    auto addMap(Path_t path, std::string_view name, Type newObject) -> bool {
        auto [key, parent] = lookup(path, Type::map);
        auto idx           = ensureWritable(path, Type::map, key);
        if (const auto* sk = maps[idx].find(name); sk != nullptr) {
            if (auto prevType = keyType(*sk); not writable(*sk) || static_cast<Type>(prevType) != newObject) {
                throwWrite(path, newObject);
            }
            return false;
        }
        auto newKey = addWritable(newObject); // NOTE: might resize maps!
        maps[idx].add(*strings.emplace(name).first, newKey);
        return true;
    }
    auto pushArray(Path_t path, Type newObject) -> std::size_t {
        auto [key, parent] = lookup(path, Type::array);
        auto idx           = ensureWritable(path, Type::array, key);
        auto newK          = addWritable(newObject); // NOTE: might resize arrays!
        return arrays[idx].add(newK);
    }
    void setValue(Path_t path, double value) {
        auto [key, parent] = lookup(path, Type::value);
        auto idx           = ensureWritable(path, Type::value, key);
        values[idx]        = value;
    }

    auto root() -> WritableMap& { return maps[0]; }
    auto array(Key key) -> WritableArray& { return arrays.at(keyIdx(key)); }
    auto map(Key key) -> WritableMap& { return maps.at(keyIdx(key)); }
    auto external(Key key) -> StatisticObject {
        POTASSCO_CHECK_PRE(not frozen, "statistics not (yet) accessible");
        return ext.at(keyIdx(key));
    }

    using Values   = PodVector_t<double>;
    using Maps     = PodVector_t<WritableMap>;
    using Arrays   = PodVector_t<WritableArray>;
    using External = PodVector_t<StatisticObject>;
    using Strings  = std::unordered_set<std::string>;
    struct Cache {
        std::string     path;
        StatisticObject object;
        Key             key{};
    };
    External  ext;     // external (non-writable) StatisticObjects not owned by this
    Maps      maps;    // writable maps
    Arrays    arrays;  // writable arrays
    Values    values;  // writable values
    Strings   strings; // added string keys used in writable maps
    Cache     cache;
    SigAtomic frozen; // whether access is currently allowed
};
ClaspStatistics::ClaspStatistics() : impl_(std::make_unique<Impl>()) {}
ClaspStatistics::~ClaspStatistics() = default;
void ClaspStatistics::addObject(Path_t map, std::string_view name, StatisticObject o, bool skipCheck) {
    impl_->addMap(map, name, o, skipCheck);
}
void ClaspStatistics::freeze(bool b) { impl_->freeze(b); }
bool ClaspStatistics::visitExternal(std::string_view name, StatsVisitor& visitor) const {
    if (const auto* key = impl_->root().find(name); key != nullptr) {
        visitor.visitExternalStats(impl_->getObject(*key));
        return true;
    }
    return false;
}
auto ClaspStatistics::root() const -> Path_t { return std::string_view{""}; }
auto ClaspStatistics::type(Path_t path) const -> Type { return impl_->lookup(path).second.type(); }
auto ClaspStatistics::size(Path_t path) const -> size_t { return impl_->lookup(path).second.size(); }
bool ClaspStatistics::writable(Path_t path) const { return Impl::writable(impl_->lookup(path).first); }
auto ClaspStatistics::key(Path_t map, size_t i) const -> std::string_view {
    auto o = impl_->lookup(map, Type::map).second;
    Impl::checkRange(o, i);
    return o.key(toU32(i));
}
auto ClaspStatistics::push(Path_t arr, Type type) -> size_t { return impl_->pushArray(arr, type); }
auto ClaspStatistics::add(Path_t map, std::string_view name, Type type) -> bool {
    return impl_->addMap(map, name, type);
}
auto ClaspStatistics::value(Path_t path) const -> double { return impl_->lookup(path, Type::value).second.value(); }
void ClaspStatistics::set(Path_t path, double value) { impl_->setValue(path, value); }
bool ClaspStatistics::find(Path_t map, std::string_view element) const {
    try {
        std::ignore = impl_->lookup(map, Type::map);
        std::ignore = impl_->lookup(appendPath(map, element));
        return true;
    }
    catch (const std::exception&) {
        return false;
    }
}

} // namespace Clasp
