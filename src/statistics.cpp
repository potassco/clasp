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
    static auto hash(StatisticObject o) noexcept -> uint32_t {
        static constexpr auto mix  = sizeof(std::size_t) == 8 ? static_cast<std::size_t>(0x9e3779b97f4a7c15ULL)
                                                              : static_cast<std::size_t>(0x9e3779b9UL);
        auto                  h1   = reinterpret_cast<std::size_t>(o.object());
        auto                  h2   = reinterpret_cast<std::size_t>(o.typeId());
        h1                        ^= h2 + mix + (h1 << 6) + (h1 >> 2);
        return static_cast<uint32_t>(h1);
    }
    // Distinguished key types - stored in different containers
    enum class KeyType : uint32_t { key_map = 0u, key_arr = 1u, key_val = 2u, key_ext = 3u };
    struct StatsKey {
        static constexpr auto type_shift = 2u;
        static constexpr auto type_mask  = 3u;
        static constexpr auto max_key    = Potassco::bit_max<uint32_t>(30);
        explicit constexpr StatsKey(uint32_t x = 0) : rep(x) {}
        constexpr StatsKey(KeyType type, uint32_t idx) : rep((idx << 2) | Potassco::to_underlying(type)) {
            POTASSCO_ASSERT(idx <= StatsKey::max_key);
        }
        [[nodiscard]] constexpr auto type() const noexcept -> KeyType { return static_cast<KeyType>(rep & type_mask); }
        [[nodiscard]] constexpr auto idx() const noexcept -> uint32_t { return rep >> type_shift; }
        [[nodiscard]] constexpr auto writable() const noexcept -> bool { return type() != KeyType::key_ext; }

        uint32_t rep;
    };

    static constexpr void checkRange(const StatisticObject& o, std::size_t idx) {
        if (auto os = o.size(); idx >= os) {
            throwRange(idx, os);
        }
    }
    using StrId = Potassco::Id_t;
    // Type representing a user-created (writable) map.
    struct WritableMap {
        using trivially_relocatable = std::true_type; // NOLINT
        explicit WritableMap(Impl& i) : self(&i) {}
        [[nodiscard]] auto size() const -> uint32_t { return size32(keys); }
        [[nodiscard]] auto key(uint32_t i) const -> std::string_view { return self->getString(keys.at(i).first); }
        [[nodiscard]] auto at(std::string_view k) const -> StatisticObject { return self->getObject(child(k)); }
        [[nodiscard]] auto find(std::string_view k) const -> const StatsKey* {
            auto it = std::ranges::find_if(keys, [&](const auto& p) { return self->getString(p.first) == k; });
            return it != keys.end() ? &it->second : nullptr;
        }
        [[nodiscard]] auto child(std::string_view k) const -> StatsKey {
            const auto* key = find(k);
            POTASSCO_CHECK(key, ERANGE, "WritableMap::at with key '%" PRIsv "'", PRI_SV(k));
            return *key;
        }
        void add(StrId strId, StatsKey k) { keys.push_back(std::pair(strId, k)); }
        using Children = Vector_t<std::pair<StrId, StatsKey>>;
        Impl*    self{};
        Children keys;
    };
    // Type representing a user-created (writable) array.
    struct WritableArray {
        using trivially_relocatable = std::true_type; // NOLINT
        explicit WritableArray(Impl& i) : self(&i) {}
        [[nodiscard]] auto size() const -> uint32_t { return size32(keys); }
        [[nodiscard]] auto at(uint32_t i) const -> StatisticObject { return self->getObject(child(i)); }
        [[nodiscard]] auto child(uint32_t i) const -> StatsKey { return keys.at(i); }
        void               add(StatsKey key) { keys.push_back(key); }
        using Children = Vector_t<StatsKey>;
        Impl*    self{};
        Children keys;
    };

    Impl() {
        maps.push_back(WritableMap{*this});
        ext.reserve(8);
    }
    ~Impl() {
        reset(arrays);
        reset(maps);
    }
    void               freeze(bool b) { frozen.exchange(b == true); }
    [[nodiscard]] auto getObject(StatsKey key) const -> StatisticObject {
        static constexpr auto get = []<typename C>(const C& container, StatsKey k) -> const typename C::value_type& {
            if (auto idx = k.idx(); idx < size32(container)) {
                return container[idx];
            }
            throwKey(toApi(k));
        };
        POTASSCO_CHECK_PRE(not frozen || key.writable(), "statistics not (yet) accessible");
        switch (key.type()) {
            case KeyType::key_ext: return get(ext, key);
            case KeyType::key_map: return StatisticObject::map(&get(maps, key));
            case KeyType::key_arr: return StatisticObject::array(&get(arrays, key));
            case KeyType::key_val: return StatisticObject::value(&get(values, key));
        }
        POTASSCO_ASSERT_NOT_REACHED("unexpected key type");
    }
    [[nodiscard]] auto getObject(StatsKey key, Type expected) const -> StatisticObject {
        auto o = getObject(key);
        if (auto t = o.type(); t != expected) {
            throwType(expected, t);
        }
        return o;
    }
    auto addWritable(Type t) -> StatsKey {
        static constexpr auto push = []<typename C, typename T>(KeyType kt, C& cont, const T& elem) {
            cont.reserve(8);
            cont.push_back(elem);
            return StatsKey(kt, size32(cont) - 1);
        };
        switch (t) {
            case Type::value: return push(KeyType::key_val, values, 0.0);
            case Type::array: return push(KeyType::key_arr, arrays, WritableArray{*this});
            case Type::map  : return push(KeyType::key_map, maps, WritableMap{*this});
        }
        POTASSCO_ASSERT_NOT_REACHED("unexpected stats type");
    }
    void ensureWritable(Type type, StatsKey key) const {
        if (key.writable() && getObject(key).type() == type) {
            return;
        }
        throwWrite(toApi(key), type);
    }
    auto pushArray(StatsKey arrK, Type newObject) -> StatsKey {
        ensureWritable(Type::array, arrK);
        auto newK = addWritable(newObject); // NOTE: might resize arrays!
        arrays[arrK.idx()].add(newK);
        return newK;
    }
    [[nodiscard]] auto getString(StrId id) const -> std::string_view { return strings[id].view(); }
    auto               addString(std::string_view str) -> StrId { return strings.add(str).first; }
    auto               addMap(StatsKey mapK, std::string_view name, Type newObject) -> StatsKey {
        ensureWritable(Type::map, mapK);
        if (const auto* key = maps[mapK.idx()].find(name); key != nullptr) {
            ensureWritable(newObject, *key);
            return *key;
        }
        auto newKey = addWritable(newObject); // NOTE: might resize maps!
        maps[mapK.idx()].add(addString(name), newKey);
        return newKey;
    }
    auto addMap(StatsKey mapK, std::string_view name, const StatisticObject& object, bool skipCheck) -> StatsKey {
        ensureWritable(Type::map, mapK);
        auto& map = maps[mapK.idx()];
        if (const auto* key = skipCheck ? nullptr : map.find(name); key != nullptr) {
            POTASSCO_CHECK(object == getObject(*key), EINVAL, "unexpected object for key '%" PRIsv "'", PRI_SV(name));
            return *key;
        }
        auto newKey = addExternal(object, true);
        map.add(addString(name), newKey);
        return newKey;
    }
    void setValue(StatsKey valK, double value) {
        ensureWritable(Type::value, valK);
        values[valK.idx()] = value;
    }
    auto addExternal(const StatisticObject& object, bool skipMapping = false) -> StatsKey {
        auto idx = size32(ext);
        if (not skipMapping) {
            auto h = hash(object);
            auto r = extIndex.find_if(h, [&](uint32_t xId) { return ext[xId] == object; });
            if (r) {
                return {KeyType::key_ext, *r};
            }
            extIndex.add(r, h, idx);
        }
        ext.push_back(object);
        return {KeyType::key_ext, idx};
    }

    auto getChildKey(StatsKey key, uint32_t idx) -> StatsKey {
        auto object = getObject(key, Type::array);
        checkRange(object, idx);
        return key.writable() ? array(key).child(idx) : addExternal(object[idx]);
    }
    auto getChildKey(StatsKey key, std::string_view path) -> StatsKey {
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
        auto type   = Type::map;
        auto hasKey = true;
        auto object = getObject(key, type);
        for (auto p = path; not p.empty();) {
            auto [top, idx] = popNext(p, type == Type::array);
            try {
                POTASSCO_CHECK(type == Type::map || (type == Type::array && idx < object.size()), EINVAL);
                if (key.writable()) {
                    key    = type == Type::map ? map(key).child(top) : array(key).child(idx);
                    object = getObject(key);
                }
                else {
                    object = type == Type::map ? object.at(top) : object[idx];
                    hasKey = false;
                }
            }
            catch (const std::exception&) {
                path = path.substr(0, static_cast<std::size_t>((top.data() + top.size()) - path.data()));
                throwPath(path, top);
            }
            type = object.type();
        }
        return hasKey ? key : addExternal(object);
    }

    auto root() -> WritableMap& { return maps[0]; }
    auto array(StatsKey key) -> WritableArray& { return arrays.at(key.idx()); }
    auto map(StatsKey key) -> WritableMap& { return maps.at(key.idx()); }

    static auto fromApi(Key_t k) -> StatsKey {
        POTASSCO_CHECK_PRE(k - 1 <= static_cast<Key_t>(StatsKey::max_key), "invalid key");
        return StatsKey{static_cast<uint32_t>(k - 1)};
    }
    static auto toApi(StatsKey k) -> Key_t { return k.rep + 1; }

    using Values  = Vector_t<double>;
    using Maps    = Vector_t<WritableMap>;
    using Arrays  = Vector_t<WritableArray>;
    using Objects = Vector_t<StatisticObject>;
    using Index   = Potassco::DynamicIndex;
    using Strings = Potassco::OrderedStringSet;

    Objects   ext;            // external (non-writable) StatisticObjects not owned by this
    Maps      maps;           // writable maps
    Arrays    arrays;         // writable arrays
    Values    values;         // writable values
    Strings   strings{false}; // added string keys used in writable maps
    Index     extIndex;       // index over ext
    SigAtomic frozen;         // whether access is currently allowed
};
ClaspStatistics::ClaspStatistics() : impl_(std::make_unique<Impl>()) {}
ClaspStatistics::~ClaspStatistics() = default;
auto ClaspStatistics::addObject(Key_t mapK, std::string_view name, StatisticObject object, bool skipCheck) -> Key_t {
    return Impl::toApi(impl_->addMap(Impl::fromApi(mapK), name, object, skipCheck));
}
bool ClaspStatistics::visitExternal(std::string_view name, StatsVisitor& visitor) const {
    if (const auto* key = impl_->root().find(name); key != nullptr) {
        visitor.visitExternalStats(impl_->getObject(*key));
        return true;
    }
    return false;
}
void ClaspStatistics::freeze(bool b) { impl_->freeze(b); }
auto ClaspStatistics::root() const -> Key_t { return Impl::toApi(Impl::StatsKey(Impl::KeyType::key_map, 0)); }
auto ClaspStatistics::type(Key_t key) const -> Type { return impl_->getObject(Impl::fromApi(key)).type(); }
auto ClaspStatistics::size(Key_t key) const -> size_t { return impl_->getObject(Impl::fromApi(key)).size(); }
bool ClaspStatistics::writable(Key_t key) const {
    auto sk     = Impl::fromApi(key);
    std::ignore = impl_->getObject(sk);
    return sk.writable();
}
auto ClaspStatistics::key(Key_t mapK, size_t i) const -> std::string_view {
    auto o = impl_->getObject(Impl::fromApi(mapK), Type::map);
    Impl::checkRange(o, i);
    return o.key(toU32(i));
}
auto ClaspStatistics::at(Key_t arrK, size_t index) const -> Key_t {
    return Impl::toApi(impl_->getChildKey(Impl::fromApi(arrK), toU32(index)));
}
auto ClaspStatistics::get(Key_t mapK, std::string_view path) const -> Key_t {
    return Impl::toApi(impl_->getChildKey(Impl::fromApi(mapK), path));
}
auto ClaspStatistics::push(Key_t arr, Type type) -> Key_t {
    return Impl::toApi(impl_->pushArray(Impl::fromApi(arr), type));
}
auto ClaspStatistics::add(Key_t mapK, std::string_view name, Type type) -> Key_t {
    return Impl::toApi(impl_->addMap(Impl::fromApi(mapK), name, type));
}
auto ClaspStatistics::value(Key_t key) const -> double { return impl_->getObject(Impl::fromApi(key)).value(); }
void ClaspStatistics::set(Key_t key, double value) { impl_->setValue(Impl::fromApi(key), value); }
bool ClaspStatistics::find(Key_t mapK, std::string_view element, Key_t* outKey) const {
    try {
        if (auto key = impl_->getChildKey(Impl::fromApi(mapK), element); outKey) {
            *outKey = Impl::toApi(key);
        }
        return true;
    }
    catch (const std::exception&) {
        return false;
    }
}
} // namespace Clasp
