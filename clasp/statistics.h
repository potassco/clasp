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

#include <concepts>
#include <string_view>

namespace Clasp {
class StatisticObject;
//! A statistic value is any object that can be converted to a double.
template <typename T>
concept StatisticValue = requires(const T& u) { static_cast<double>(u); };
//! Specifies the interface that a type must provide to be a valid statistic map.
/*!
 * For a type T to be a statistic map, it has to provide:
 *  - a function `size()`, which returns the number of keys in the map,
 *  - a function `key(i)`, which given an index `0 <= i < size()` returns the ith key in the map,
 *  - a function `at(k)`, which given a key `k` returns the StatisticObject associated with the key.
 *
 *  \note T might throw an exception if a given index is out of bounds or a key is not present.
 */
template <typename T>
concept StatisticMap = requires(const T& u) {
    { u.size() } -> std::unsigned_integral;
    { u.key(std::declval<uint32_t>()) } -> std::convertible_to<std::string_view>;
    { u.at(std::declval<std::string_view>()) } -> std::convertible_to<StatisticObject>;
};
//! Specifies the interface that a type must provide to be a valid statistic array.
/*!
 * For a type T to be a statistic array, it has to provide:
 *  - a function `size()`, which returns the size of the array,
 *  - a function `at(i)`, which given an index `0 <= i < size()` returns the ith StatisticObject element in the array.
 *
 *  \note T might throw an exception if a given index is out of bounds.
 */
template <typename T>
concept StatisticArray = requires(const T& u) {
    { u.size() } -> std::unsigned_integral;
    { u.at(std::declval<uint32_t>()) } -> std::convertible_to<StatisticObject>;
};

//! Discriminated union representing either a single statistic value or a composite.
class StatisticObject {
public:
    using Type = Potassco::StatisticsType;
    //! Creates a Type::value object with value 0.0.
    StatisticObject() : StatisticObject(nullptr, Value::create<double, &alwaysNull>()) {}
    //! Creates a Type::value object - static_cast<double>(*obj) shall be valid.
    template <StatisticValue T>
    static auto value(const T* obj) -> StatisticObject {
        return {obj, Value::create<T, toDouble<T>>()};
    }
    //! Creates a mapped Type::value object: GetOp(obj) -> double
    template <auto GetOp, typename T>
    requires std::is_invocable_r_v<double, decltype(GetOp), const T*>
    static auto value(const T* obj) -> StatisticObject {
        return {obj, Value::create<T, GetOp>()};
    }
    //! Creates a Type::map object.
    template <StatisticMap T>
    static auto map(const T* obj) -> StatisticObject {
        return {obj, Map::create<T>()};
    }
    //! Creates a Type::array object.
    template <StatisticArray T>
    static auto array(const T* obj) -> StatisticObject {
        return {obj, Array::create<T>()};
    }
    //! Creates a Type::array object with `GetOp` as at() function.
    /*!
     * GetOp(const ContainerT::value_type&) -> StatisticObject
     */
    template <auto GetOp, typename ContainerT>
    requires std::is_invocable_r_v<StatisticObject, decltype(GetOp), const typename ContainerT::value_type&>
    static auto array(const ContainerT* obj) -> StatisticObject {
        return {obj, Array::create<ContainerT, &Array::getValueExt<ContainerT, GetOp>>()};
    }
    //! Returns the statistic type of this object.
    [[nodiscard]] constexpr auto type() const -> Type { return vtab_->type; }
    //! Returns the number of children of this object or 0 if `type() == Type::value`.
    [[nodiscard]] constexpr auto size() const -> uint32_t {
        if (auto t = type(); t == Type::value) {
            return 0u;
        }
        else {
            return (t == Type::array ? arr()->size : map()->size)(object());
        }
    }

    /*!
     * \name Map
     * \pre type() == Type::map
     */
    //@{
    //! Returns the ith key of this map.
    /*!
     * \pre i < size()
     */
    [[nodiscard]] constexpr auto key(uint32_t i) const -> std::string_view { return map()->key(object(), i); }
    //! Returns the object under the given key.
    /*!
     * \pre k in key([0;size()))
     */
    [[nodiscard]] constexpr auto at(std::string_view k) const -> StatisticObject { return map()->at(object(), k); }
    //@}

    //! Returns the object at the given index.
    /*!
     * \pre type() == Type::array
     * \pre i < size()
     */
    [[nodiscard]] constexpr auto operator[](uint32_t i) const -> StatisticObject { return arr()->at(object(), i); }

    //! Returns the value of this object.
    /*!
     * \pre type() == Type::value
     */
    [[nodiscard]] constexpr auto value() const -> double { return val()->value(object()); }

    constexpr bool operator==(const StatisticObject&) const  = default;
    constexpr auto operator<=>(const StatisticObject&) const = default;

    [[nodiscard]] constexpr auto object() const -> const void* { return obj_; }
    [[nodiscard]] constexpr auto typeId() const -> const void* { return vtab_; }
    [[nodiscard]] constexpr bool eqTypeId(const StatisticObject& other) const { return vtab_ == other.vtab_; }

private:
    static constexpr auto toDouble(const auto* v) -> double { return static_cast<double>(*v); }
    static constexpr auto alwaysNull(const double*) -> double { return 0.0; }
    template <typename T>
    static constexpr auto getSize(const void* o) -> uint32_t {
        return toU32(static_cast<const T*>(o)->size());
    }
    ///////////////////////////////////////////////////////
    // Vtable types
    ///////////////////////////////////////////////////////
    struct VtabBase {
        using ObjPtr = const void*;
        using SzFun  = auto (*)(ObjPtr) -> uint32_t;
        constexpr explicit VtabBase(Type t) : type(t) {}
        template <typename T>
        [[nodiscard]] constexpr const T* as() const {
            if (T::type == type) {
                return static_cast<const T*>(this);
            }
            Potassco::AbstractStatistics::throwType(T::type, type);
        }
        Type type;
    };
    struct Value : VtabBase {
        static constexpr auto type = Type::value;
        template <typename T, double (*Op)(const T*)>
        static auto get(ObjPtr o) -> double {
            return Op(static_cast<const T*>(o));
        }
        template <typename T, double (*Op)(const T*)>
        static const Value* create() {
            static constexpr auto vtab_s = Value{&get<T, Op>};
            return &vtab_s;
        }
        using ValFun = auto (*)(ObjPtr) -> double;
        constexpr explicit Value(ValFun v) : VtabBase(Type::value), value(v) {}
        ValFun value;
    };
    struct Array : VtabBase {
        static constexpr auto type = Type::array;
        using AtFun                = auto (*)(ObjPtr, uint32_t) -> StatisticObject;
        template <typename T>
        static constexpr auto getValue(ObjPtr o, uint32_t i) -> StatisticObject {
            return static_cast<const T*>(o)->at(i);
        }
        template <typename T, auto Op>
        static constexpr auto getValueExt(ObjPtr o, uint32_t i) -> StatisticObject {
            return Op(static_cast<const T*>(o)->at(i));
        }
        template <typename T, AtFun Op = &getValue<T>>
        static const Array* create() {
            static constexpr auto vtab_s = Array{&getSize<T>, Op};
            return &vtab_s;
        }
        constexpr Array(SzFun sz, AtFun a) : VtabBase(Type::array), size(sz), at(a) {}
        SzFun size;
        AtFun at;
    };
    struct Map : VtabBase {
        static constexpr auto type = Type::map;
        template <typename T>
        static constexpr auto getKey(ObjPtr o, uint32_t i) -> std::string_view {
            return static_cast<const T*>(o)->key(i);
        }
        template <typename T>
        static constexpr auto getValue(ObjPtr o, std::string_view k) -> StatisticObject {
            return static_cast<const T*>(o)->at(k);
        }
        template <typename T>
        static const Map* create() {
            static constexpr auto vtab_s = Map{&getSize<T>, &getKey<T>, &getValue<T>};
            return &vtab_s;
        }
        using KeyFun = auto (*)(ObjPtr, uint32_t) -> std::string_view;
        using AtFun  = auto (*)(ObjPtr, std::string_view) -> StatisticObject;
        constexpr Map(SzFun sz, KeyFun k, AtFun a) : VtabBase(Type::map), size(sz), key(k), at(a) {}
        SzFun  size;
        KeyFun key;
        AtFun  at;
    };
    [[nodiscard]] constexpr auto val() const -> const Value* { return vtab_->as<Value>(); }
    [[nodiscard]] constexpr auto arr() const -> const Array* { return vtab_->as<Array>(); }
    [[nodiscard]] constexpr auto map() const -> const Map* { return vtab_->as<Map>(); }
    ///////////////////////////////////////////////////////
    constexpr StatisticObject(const void* obj, const VtabBase* vtab) : obj_(obj), vtab_(vtab) {}
    const void*     obj_{nullptr};
    const VtabBase* vtab_{nullptr};
};

struct SolverStats;
struct ProblemStats;
class StatsVisitor;

//! A class for traversing, querying, and adding statistics.
/*!
 * \ingroup clingo
 */
class ClaspStatistics : public Potassco::AbstractStatistics {
public:
    ClaspStatistics();
    ~ClaspStatistics() override;
    ClaspStatistics(ClaspStatistics&&) = delete;

    //! Exports the given statistic object under the given name in the map with the key `mapK`.
    /*!
     * \param mapK      The map object to which `object` should be added.
     * \param name      The name under which `object` should be exported.
     * \param object    The statistic object to export.
     * \param skipCheck Whether to skip the check for a duplicate/existing name.
     * \return The key of the added statistic object.
     *
     * \note If `name` already exists in `mapK`, the behavior depends on `skipCheck`:
     *   - if `skipCheck` is false, a logic error is raised unless `object` matches with the existing object,
     *   - if `skipCheck` is true, `object` is added with a new key, but it is not reachable from `mapK`.
     */
    auto addObject(Key_t mapK, std::string_view name, StatisticObject object, bool skipCheck = false) -> Key_t;
    //! Applies the given visitor on the statistic object with the given name.
    /*!
     * If a statistic object `o` with the given name exists, calls `visitor.visitExternalStats(o)` and returns true.
     * Otherwise, the function returns false without calling any function on `visitor`.
     */
    bool visitExternal(std::string_view name, StatsVisitor& visitor) const;
    //! Freezes or thaws access to external statistic objects.
    /*!
     * After a call to `freeze(true)`, any attempt to access a non-writable statistic object will result in
     * a logic error until `freeze(false)` is called.
     */
    void freeze(bool);

    // Base interface
    [[nodiscard]] auto root() const -> Key_t override;
    [[nodiscard]] Type type(Key_t key) const override;
    [[nodiscard]] auto size(Key_t key) const -> size_t override;
    [[nodiscard]] bool writable(Key_t key) const override;
    [[nodiscard]] auto at(Key_t arrK, size_t index) const -> Key_t override;
    [[nodiscard]] auto push(Key_t arr, Type type) -> Key_t override;
    [[nodiscard]] auto key(Key_t mapK, size_t i) const -> std::string_view override;
    [[nodiscard]] auto get(Key_t mapK, std::string_view) const -> Key_t override;
    [[nodiscard]] bool find(Key_t mapK, std::string_view element, Key_t* outKey) const override;
    [[nodiscard]] auto add(Key_t mapK, std::string_view name, Type type) -> Key_t override;
    [[nodiscard]] auto value(Key_t key) const -> double override;
    void               set(Key_t key, double value) override;

private:
    struct Impl;
    std::unique_ptr<Impl> impl_;
};

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
