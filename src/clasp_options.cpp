//
// Copyright (c) 2006-present Benjamin Kaufmann
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
#include <clasp/cli/clasp_options.h>

#include <clasp/lookahead.h>
#include <clasp/minimize_constraint.h>
#include <clasp/unfounded_check.h>

#include <potassco/program_opts/errors.h>
#include <potassco/program_opts/program_options.h>
#include <potassco/program_opts/typed_value.h>

#include <potassco/error.h>

#include <cctype>
#include <cfloat>
#include <cstring>
#include <fstream>

/////////////////////////////////////////////////////////////////////////////////////////
// Helper MACROS
/////////////////////////////////////////////////////////////////////////////////////////
#define SET(x, v)           (((x) = (v)) == (v))
#define SET_LEQ(x, v, m)    (((v) <= (m)) && SET((x), (v)))
#define SET_GEQ(x, v, m)    (((v) >= (m)) && SET((x), (v)))
#define SET_OR_FILL(x, v)   (SET((x), (v)) || ((x) = 0, (x) = ~(x), true))
#define SET_OR_ZERO(x, v)   (SET((x), (v)) || SET((x), uint32_t(0)))
#define SET_R(x, v, lo, hi) (((lo) <= (v)) && ((v) <= (hi)) && SET((x), (v)))
#define TRUE(...)           ((__VA_ARGS__), true)
#define CLI_NAME(k)         POTASSCO_CONCAT(POTASSCO_STRING(k), _opt)
/////////////////////////////////////////////////////////////////////////////////////////
// Primitive types/functions for string <-> T conversions
/////////////////////////////////////////////////////////////////////////////////////////
namespace Potassco {
template <typename T>
constexpr bool extract(std::string_view& in, T& required, std::errc& err, bool comma = false) {
    if (comma && not Parse::matchOpt(in, ',')) {
        err = std::errc::invalid_argument;
        return false;
    }
    return Parse::ok(err = Potassco::extract(in, required));
}
template <typename T, typename... OptArgs>
constexpr bool extractOpt(bool comma, std::string_view& in, T& required, std::errc& err, OptArgs&... extra) {
    auto n = Potassco::extract(in, required, err, comma) ? 0u : sizeof...(OptArgs);
    std::ignore =
        ((n++ < sizeof...(OptArgs) && Parse::matchOpt(in, ',') && Parse::ok(err = Potassco::extract(in, extra))) &&
         ...);
    return Parse::ok(err);
}

namespace {
struct KeyVal {
    std::string_view key;
    int              value;
};
struct OffType {
    friend std::string&           toChars(std::string& out, const OffType&) { return out.append("no"); }
    friend std::from_chars_result fromChars(std::string_view in, const OffType&) {
        bool temp = true;
        if (auto r = extract(in, temp); r == std::errc{} && not temp) {
            return Parse::success(in, 0);
        }
        return Parse::error(in);
    }
};
constexpr OffType off = {};
struct StringRef {
    explicit StringRef(std::string& o) : out(&o) {}
    template <typename T>
    friend StringRef& operator<<(StringRef& str, const T& val) {
        if (not str.out->empty()) {
            str.out->append(1, ',');
        }
        toChars(*str.out, val);
        return str;
    }
    operator std::string&() const noexcept { return *out; }
    std::string* out;
};
template <typename EnumT>
struct Set {
    static constexpr auto entries = enumMap(std::type_identity<EnumT>{});
    explicit Set(unsigned v = 0) : val(v) {}
    [[nodiscard]] unsigned value() const { return val; }
    unsigned               val;
    friend std::string&    toChars(std::string& out, const Set& x) {
        if (auto bitset = x.val; bitset) {
            for (const auto& kv : entries) {
                if (auto ev = static_cast<unsigned>(kv.value); bitset == ev || (ev && (ev & bitset) == ev)) {
                    out.append(kv.key);
                    bitset -= ev;
                    if (bitset == 0u) {
                        return out;
                    }
                    out.append(1, ',');
                }
            }
            return toChars(out, static_cast<EnumT>(bitset));
        }
        return toChars(out, off);
    }
    // <list_of_keys>|<bitmask>
    friend std::from_chars_result fromChars(std::string_view in, Set& out) {
        unsigned n;
        EnumT    v;
        auto     orig = in;
        if (auto r = std::errc{}; Potassco::extract(in, n, r)) {
            unsigned sum = 0;
            for (const auto& [_, value] : entries) {
                sum |= static_cast<unsigned>(value);
                if (n == static_cast<unsigned>(value) || (n && Potassco::test_mask(n, sum))) {
                    out.val = n;
                    return Parse::success(in, 0);
                }
            }
            return Parse::error(orig);
        }
        else if (extract(in, v, r)) {
            do { out.val |= static_cast<unsigned>(v); } while (extract(in, v, r, true));
            return Parse::success(in, 0);
        }
        else {
            return Parse::error(in, r);
        }
    }
};

struct ArgString {
    explicit ArgString(std::string_view x) : in(x) {}
    [[nodiscard]] bool off() const { return Parse::ok(stringTo(in, Potassco::off)); }
    template <typename... R>
    requires(sizeof...(R) > 0)
    bool get(R&... args) {
        auto input  = in;
        auto res    = std::errc{};
        auto n      = sizeof...(R);
        std::ignore = ((Potassco::extract(input, args, res) && (--n == 0 || Parse::matchOpt(input, ','))) && ...);
        return res == std::errc{} && input.empty();
    }
    std::string_view in;
};
} // namespace
using namespace std::literals;
static constexpr const KeyVal* findValue(Clasp::SpanView<KeyVal> map, std::string_view in,
                                         std::string_view sep = ","sv) {
    auto key = in.substr(0, in.find_first_of(sep));
    auto it  = std::ranges::find_if(map, [&](const KeyVal& kv) { return Parse::eqIgnoreCase(key, kv.key); });
    return it != map.end() ? &*it : nullptr;
}
static std::string_view findKey(Clasp::SpanView<KeyVal> map, int x) {
    auto it = std::ranges::find(map, x, [](const KeyVal& kv) { return kv.value; });
    return it != map.end() ? it->key : std::string_view{};
}

} // namespace Potassco

namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// Enum mappings for clasp types
/////////////////////////////////////////////////////////////////////////////////////////
#define TO_STR_VIEW(x) POTASSCO_CONCAT(x, sv)
#define MAP(x, y)                                                                                                      \
    { TO_STR_VIEW(x), static_cast<int>(y) }
#define ENUM_MAP(X, ...)                                                                                               \
    static consteval auto enumMap(std::type_identity<X>) {                                                             \
        using namespace std::literals;                                                                                 \
        using enum X;                                                                                                  \
        return std::to_array<Potassco::KeyVal>({__VA_ARGS__});                                                         \
    }                                                                                                                  \
    std::from_chars_result fromChars(std::string_view in, X& out) {                                                    \
        constexpr auto entries = enumMap(std::type_identity<X>{});                                                     \
        if (const auto* it = Potassco::findValue(entries, in)) {                                                       \
            out = static_cast<X>(it->value);                                                                           \
            return Potassco::Parse::success(in, it->key.length());                                                     \
        }                                                                                                              \
        return Potassco::Parse::error(in);                                                                             \
    }                                                                                                                  \
    static std::string& toChars(std::string& out, X x) {                                                               \
        return out.append(Potassco::findKey(enumMap(std::type_identity<X>{}), static_cast<int>(x)));                   \
    }
#define OPTION(k, e, a, d, ...) a
#define CLASP_ALL_GROUPS
#define ARG_EXT(a, X) X
#define ARG(a)
#include <clasp/cli/clasp_cli_options.inl>
namespace Cli {
ENUM_MAP(ConfigKey, MAP("auto", config_default), MAP("frumpy", config_frumpy), MAP("jumpy", config_jumpy),
         MAP("tweety", config_tweety), MAP("handy", config_handy), MAP("crafty", config_crafty),
         MAP("trendy", config_trendy), MAP("many", config_many))
}
#undef MAP
#undef ENUM_MAP
#undef TO_STR_VIEW
/////////////////////////////////////////////////////////////////////////////////////////
// Conversion functions for complex clasp types
/////////////////////////////////////////////////////////////////////////////////////////
using Potassco::Parse::ok;
using namespace std::literals;
static std::string& toChars(std::string& out, const SatPreParams& p) {
    if (not p.type) {
        return toChars(out, Potassco::off);
    }
    Potassco::toChars(out, p.type);
    Potassco::KeyVal kv[5] = {{"iter="sv, static_cast<int>(p.limIters)},
                              {"occ="sv, static_cast<int>(p.limOcc)},
                              {"time="sv, static_cast<int>(p.limTime)},
                              {"frozen="sv, static_cast<int>(p.limFrozen)},
                              {"size="sv, static_cast<int>(p.limClause)}};
    for (const auto [k, n] : kv) {
        if (n > 0) {
            Potassco::toChars(out.append(1, ',').append(k), n);
        }
    }
    return out;
}
static std::from_chars_result fromChars(std::string_view in, SatPreParams& out) {
    if (auto r = fromChars(in, Potassco::off); ok(r)) {
        out = SatPreParams();
        return r;
    }
    auto r = std::errc{};
    if (uint32_t n; not Potassco::extract(in, n, r) || not SET(out.type, n)) {
        return Potassco::Parse::error(in, not ok(r) ? r : std::errc::result_out_of_range);
    }
    Potassco::KeyVal kv[5] = {{"iter", 0}, {"occ", 0}, {"time", 0}, {"frozen", 0}, {"size", 4000}};
    for (uint32_t id = 0; Potassco::Parse::matchOpt(in, ','); ++id) {
        if (const auto* val = Potassco::findValue(kv, in, ":="); val != nullptr) {
            id = static_cast<uint32_t>(val - kv);
            in.remove_prefix(val->key.length());
            Potassco::Parse::matchOpt(in, '=') || Potassco::Parse::matchOpt(in, ':');
        }
        if (id > 4 || not Potassco::extract(in, kv[id].value, r)) {
            break;
        }
    }
    SET_OR_ZERO(out.limIters, static_cast<unsigned>(kv[0].value));
    SET_OR_ZERO(out.limOcc, static_cast<unsigned>(kv[1].value));
    SET_OR_ZERO(out.limTime, static_cast<unsigned>(kv[2].value));
    SET_OR_ZERO(out.limFrozen, static_cast<unsigned>(kv[3].value));
    SET_OR_ZERO(out.limClause, static_cast<unsigned>(kv[4].value));
    return Potassco::Parse::success(in, 0);
}

static std::string& toChars(std::string& out, const OptParams& p) {
    toChars(out, static_cast<OptParams::Type>(p.type));
    if (p.type == OptParams::type_usc) {
        toChars(out.append(1, ','), static_cast<OptParams::UscAlgo>(p.algo));
        if (p.algo == OptParams::usc_k) {
            Potassco::toChars(out.append(1, ','), p.kLim);
        }
        if (p.opts) {
            toChars(out.append(1, ','), Potassco::Set<OptParams::UscOption>(p.opts));
        }
    }
    else {
        toChars(out.append(1, ','), static_cast<OptParams::BBAlgo>(p.algo));
    }
    return out;
}

static bool setOptLegacy(OptParams& out, uint32_t n) {
    if (n >= 20) {
        return false;
    }
    out.type = n < 4 ? OptParams::type_bb : OptParams::type_usc;
    out.algo = n < 4 ? n : 0;
    out.opts = 0u;
    out.kLim = 0u;
    if (n > 4) {
        n -= 4;
        if (Potassco::test_bit(n, 0)) {
            out.opts |= OptParams::usc_disjoint;
        }
        if (Potassco::test_bit(n, 1)) {
            out.opts |= OptParams::usc_succinct;
        }
        if (Potassco::test_bit(n, 2)) {
            out.algo = OptParams::usc_pmr;
        }
        if (Potassco::test_bit(n, 3)) {
            out.opts |= OptParams::usc_stratify;
        }
    }
    return true;
}
static std::from_chars_result fromChars(std::string_view in, OptParams& out) {
    auto r = std::errc{};
    if (auto n = 0u; Potassco::extract(in, n, r)) { // clasp-3.0: <n>
        return setOptLegacy(out, n) ? Potassco::Parse::success(in, 0)
                                    : Potassco::Parse::error(in, std::errc::result_out_of_range);
    }
    auto t = OptParams::type_bb;
    if (not Potassco::extract(in, t, r)) { // {bb|usc}[,<tactics>]
        return Potassco::Parse::error(in);
    }
    setOptLegacy(out, static_cast<uint32_t>(t) * 4);
    if (Potassco::Parse::matchOpt(in, ',')) {
        if (auto n = 0u; Potassco::extract(in, n, r)) { // clasp-3.2: (bb|usc),<n>
            return setOptLegacy(out, n + (static_cast<uint32_t>(t) * 4))
                       ? Potassco::Parse::success(in, 0)
                       : Potassco::Parse::error(in, std::errc::result_out_of_range);
        }
        if (OptParams::BBAlgo bb; t == OptParams::type_bb && Potassco::extract(in, bb, r)) {
            out.algo = bb;
        }
        else if (t == OptParams::type_usc) {
            auto usc  = OptParams::usc_oll;
            auto more = true;
            if (Potassco::extract(in, usc, r)) {
                auto next = in;
                if (auto n = 0u; usc == OptParams::usc_k && Potassco::extract(next, n, r, true)) {
                    SET_OR_FILL(out.kLim, n);
                    in = next;
                }
                more = Potassco::Parse::matchOpt(in, ',');
            }
            auto opts = Potassco::Set<OptParams::UscOption>{0};
            out.algo  = usc;
            if (more && (Potassco::extract(in, Potassco::off, r) || Potassco::extract(in, opts, r))) {
                out.opts = opts.value();
            }
        }
    }
    return Potassco::Parse::success(in, 0);
}

static std::string& toChars(std::string& out, ScheduleStrategy sched) {
    if (sched.disabled()) {
        return out.append("0");
    }
    if (sched.defaulted()) {
        sched = ScheduleStrategy();
    }
    auto str = Potassco::StringRef{out};
    switch (sched.type) {
        case ScheduleStrategy::sched_geom:
            return str << "x"sv << sched.base << static_cast<double>(sched.grow) << sched.len;
        case ScheduleStrategy::sched_arith:
            if (sched.grow != 0.0f) {
                return str << "+"sv << sched.base << static_cast<uint32_t>(sched.grow) << sched.len;
            }
            return str << "f"sv << sched.base;
        case ScheduleStrategy::sched_luby:
            str << "l"sv << sched.base;
            if (sched.len) {
                str << sched.len;
            }
            return out;
        default: POTASSCO_ASSERT_NOT_REACHED("toChars(ScheduleStrategy): unknown type");
    }
}
static std::string& toChars(std::string& out, const RestartSchedule& in) {
    if (in.disabled() || not in.isDynamic()) {
        return toChars(out, static_cast<const ScheduleStrategy&>(in));
    }
    Potassco::StringRef str(out.append(1, 'd'));
    str << in.base << in.grow;
    auto lbdLim = in.lbdLim();
    auto fast   = in.fastAvg();
    auto slow   = in.slowAvg();
    if (lbdLim || fast != MovingAvg::avg_sma || slow != MovingAvg::avg_sma) {
        str << lbdLim;
    }
    if (fast != MovingAvg::avg_sma || slow != MovingAvg::avg_sma) {
        str << fast;
    }
    if (fast != MovingAvg::avg_sma && in.keepAvg()) {
        str << in.keepAvg();
    }
    if (slow != MovingAvg::avg_sma) {
        str << slow;
        if (in.slowWin()) {
            str << in.slowWin();
        }
    }
    return out;
}

// <type {F|L|x|+}>,<n {1..umax}>[,<args>][,<lim>]
static std::from_chars_result fromChars(std::string_view in, ScheduleStrategy& out) {
    constexpr Potassco::KeyVal types[] = {{"f", 'f'}, {"fixed", 'f'}, {"l", 'l'}, {"luby", 'l'},
                                          {"x", 'x'}, {"*", 'x'},     {"+", '+'}, {"add", '+'}};

    const auto* type = Potassco::findValue(types, in);
    uint32_t    base = 0;
    auto        ec   = std::errc{};
    using namespace Potassco::Parse;
    if (not type || not Potassco::extract(in = in.substr(type->key.length()), base, ec, true) || base == 0) {
        return error(in);
    }
    switch (uint32_t limit = 0; static_cast<char>(type->value)) {
        default: POTASSCO_ASSERT_NOT_REACHED("unexpected schedule strategy");
        case 'f': // Fixed
            out = ScheduleStrategy::fixed(base);
            break;
        case 'l': // Luby
            if (not matchOpt(in, ',') || Potassco::extract(in, limit, ec)) {
                out = ScheduleStrategy::luby(base, limit);
            }
            break;
        case 'x': // Geometric
            if (double g = 0.0; Potassco::extractOpt(true, in, g, ec, limit)) {
                out = ScheduleStrategy::geom(base, g, limit);
            }
            break;
        case '+': // Arithmetic
            if (auto inc = 0u; Potassco::extractOpt(true, in, inc, ec, limit)) {
                out = ScheduleStrategy::arith(base, inc, limit);
            }
            break;
    }
    return ok(ec) ? success(in, 0) : error(in, ec);
}

static std::from_chars_result fromChars(std::string_view in, RestartSchedule& out) {
    if (not in.starts_with("d,") && not in.starts_with("D,")) {
        return fromChars(in, static_cast<ScheduleStrategy&>(out));
    }
    using namespace Potassco::Parse;
    in.remove_prefix(2);
    // <n>,<K>[,<args>]
    auto n    = 0u;
    auto k    = 0.0;
    auto next = in;
    auto r    = std::errc{};
    if (not Potassco::extractOpt(false, next, n, r, k) || n == 0u || k <= 0.0) {
        return error(in);
    }
    uint32_t lim = 0, sWin = 0;
    auto     fast = MovingAvg::Type::avg_sma;
    auto     slow = MovingAvg::Type::avg_sma;
    auto     keep = RestartSchedule::keep_never;
    in            = next;
    if (matchOpt(in, ',') && not Potassco::extract(in, lim, r)) {
        return error(in);
    }
    if (matchOpt(in, ',') && not Potassco::extract(in, fast, r)) {
        return error(in);
    }
    next = in;
    if (matchOpt(next, ',') && fast != MovingAvg::Type::avg_sma && Potassco::extract(next, keep, r)) {
        in = next;
    }
    if (matchOpt(in, ',') && not Potassco::extract(in, slow, r)) {
        return error(in);
    }
    if (matchOpt(in, ',') && slow != MovingAvg::Type::avg_sma && not Potassco::extract(in, sWin, r)) {
        return error(in);
    }
    out = RestartSchedule::dynamic(n, static_cast<float>(k), lim, fast, keep, slow, sWin);
    return success(in, 0);
}
namespace Asp {
using Clasp::fromChars;
using Clasp::toChars;
} // namespace Asp
namespace mt {
using Clasp::fromChars;
using Clasp::toChars;
} // namespace mt
namespace Cli {
/////////////////////////////////////////////////////////////////////////////////////////
// Option -> Key mapping
/////////////////////////////////////////////////////////////////////////////////////////
namespace {
enum OptionKey {
    meta_config = 0,
#define CLASP_CONTEXT_OPTIONS GRP(option_category_nodes_end, option_category_context_begin),
#define CLASP_GLOBAL_OPTIONS  GRP(option_category_context_end, option_category_global_begin),
#define CLASP_SOLVER_OPTIONS  GRP(option_category_global_end, option_category_solver_begin),
#define CLASP_SEARCH_OPTIONS  GRP(option_category_solver_end, option_category_search_begin),
#define CLASP_ASP_OPTIONS     GRP(option_category_search_end, option_category_asp_begin),
#define CLASP_SOLVE_OPTIONS   GRP(option_category_asp_end, option_category_solve_begin),
#define OPTION(k, e, ...)     opt_##k,
#define GROUP_BEGIN(X)        X
#define GRP(X, Y)             X, Y = X, detail_before_##Y = X - 1 // NOLINT(bugprone-macro-parentheses)
#include <clasp/cli/clasp_cli_options.inl>

#undef GRP
    option_category_solve_end,
    detail_num_options = option_category_solve_end,
    meta_tester        = detail_num_options
};
#if CLASP_HAS_THREADS
#define MANY_DESC "        many  : Use default portfolio to configure solver(s)\n"
#define MANY_ARG  "|many"
#else
#define MANY_DESC
#define MANY_ARG ""
#endif
#define KEY_INIT_DESC(desc)                                                                                            \
    desc "      <arg>: {auto|frumpy|jumpy|tweety|handy|crafty|trendy" MANY_ARG "|<file>}\n"                            \
         "        auto  : Select configuration based on problem type\n"                                                \
         "        frumpy: Use conservative defaults\n"                                                                 \
         "        jumpy : Use aggressive defaults\n"                                                                   \
         "        tweety: Use defaults geared towards asp problems\n"                                                  \
         "        handy : Use defaults geared towards large problems\n"                                                \
         "        crafty: Use defaults geared towards crafted problems\n"                                              \
         "        trendy: Use defaults geared towards industrial problems\n" MANY_DESC                                 \
         "        <file>: Use configuration file to configure solver(s)"
struct NodeKey {
    std::string_view name;
    int16_t          skBeg;
    uint16_t         skSize;
};
enum { id_root = -5, id_tester = -4, id_solve = -3, id_asp = -2, id_solver = -1, id_leaf = 0 };
struct Name2Id {
    std::string_view name;
    int              key;
    constexpr bool   operator<(const Name2Id& rhs) const { return name < rhs.name; }
    constexpr bool   operator<(std::string_view rhs) const { return name < rhs; }
};
template <unsigned N>
struct OptName {
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-member-init,google-explicit-constructor)
    constexpr OptName(char const (&s)[N]) {
        std::copy_n(s, N, buf);
        std::replace(buf, buf + N, '_', '-');
    }
    char buf[N];
};
// ReSharper disable once CppDeclaratorNeverUsed
template <OptName O>
consteval auto operator""_opt() -> Potassco::ProgramOptions::Str {
    return Potassco::ProgramOptions::Str{O.buf};
}
Name2Id g_index[detail_num_options + 1] = {{"configuration", meta_config},
#define OPTION(k, e, ...) {#k, opt_##k},
#define CLASP_ALL_GROUPS
#include <clasp/cli/clasp_cli_options.inl>

                                           {"tester", meta_tester}};
[[maybe_unused]] bool g_init_index = (std::sort(g_index, g_index + detail_num_options + 1), true);
} // namespace
/// \cond
// Valid option keys.
static_assert(detail_num_options + 1 <= 255, "too many options");
static constexpr bool isOption(int k) { return k >= option_category_nodes_end && k < detail_num_options; }
static constexpr bool isGlobalOption(int k) {
    return k >= option_category_global_begin && k < option_category_global_end;
}
static constexpr bool isTesterOption(int k) {
    return k >= option_category_nodes_end && k < option_category_search_end && not isGlobalOption(k);
}
static constexpr bool isSolverOption(int k) {
    return k >= option_category_solver_begin && k < option_category_search_end;
}
static constexpr int16_t  decodeKey(uint32_t key) { return static_cast<int16_t>(static_cast<uint16_t>(key)); }
static constexpr uint8_t  decodeMode(uint32_t key) { return static_cast<uint8_t>((key >> 24)); }
static constexpr uint8_t  decodeSolver(uint32_t key) { return static_cast<uint8_t>((key >> 16)); }
static constexpr bool     isValidId(int16_t id) { return id >= id_root && id < detail_num_options; }
static constexpr bool     isLeafId(int16_t id) { return id >= id_leaf && id < detail_num_options; }
static constexpr uint32_t makeKeyHandle(int16_t kId, uint32_t mode, uint32_t sId) {
    assert(sId <= 255 && mode <= 255);
    return (mode << 24) | (sId << 16) | static_cast<uint16_t>(kId);
}
static constexpr uint8_t mode_solver  = 1u;
static constexpr uint8_t mode_tester  = 2u;
static constexpr uint8_t mode_relaxed = 4u;
static constexpr uint8_t mode_meta    = 8u;
static constexpr bool    isTester(uint8_t mode) { return (mode & mode_tester) != 0; }
static constexpr bool    isSolver(uint8_t mode) { return (mode & mode_solver) != 0; }
static constexpr bool    isRelaxed(uint8_t mode) { return (mode & mode_relaxed) != 0; }
static constexpr bool    isSupportedOption(int opt, uint8_t mode) {
    if ((isTester(mode) && not isTesterOption(opt)) || (isSolver(mode) && not isSolverOption(opt))) {
        return false;
    }
    return isOption(opt);
}
static constexpr BasicSatConfig* active(ClaspConfig* config, uint8_t mode) {
    return not isTester(mode) ? config : config->testerConfig();
}
static constexpr const BasicSatConfig* active(const ClaspConfig* config, uint8_t mode) {
    return active(const_cast<ClaspConfig*>(config), mode);
}
static constexpr int16_t findOption(std::string_view needle, bool prefix) {
    const auto* end = g_index + detail_num_options + 1;
    const auto* it  = std::lower_bound(const_cast<const Name2Id*>(g_index), end, needle);
    auto        ret = -1;
    if (auto eqLen = needle.length() == it->name.length();
        it != end && it->name.starts_with(needle) && (eqLen || prefix)) {
        const auto* next = it + 1;
        ret              = eqLen || next == end || not next->name.starts_with(needle) ? it->key : -2;
    }
    return static_cast<int16_t>(ret);
}
static constexpr NodeKey makeNode(std::string_view name, int16_t skBeg = 0, int16_t skEnd = 0) {
    return {name, skBeg, static_cast<uint16_t>(skEnd - skBeg)};
}

static NodeKey getNode(int16_t id, std::string* help = nullptr, std::string_view* cliName = nullptr) {
    assert(isValidId(id));
    using namespace Potassco::ProgramOptions;
    auto bind = [](const char* name, std::string* helpOut, const char* desc) {
        if (helpOut) {
            *helpOut = desc;
        }
        return name;
    };
    switch (id) {
        case id_root  : return makeNode(bind("", help, "Options"), id_tester, option_category_global_end);
        case id_tester: return makeNode(bind("tester", help, "Tester Options"), id_solver, option_category_context_end);
        case id_solve:
            return makeNode(bind("solve", help, "Solve Options"), option_category_solve_begin,
                            option_category_solve_end);
        case id_asp:
            return makeNode(bind("asp", help, "Asp Options"), option_category_asp_begin, option_category_asp_end);
        case id_solver:
            return makeNode(bind("solver", help, "Solver Options"), option_category_solver_begin,
                            option_category_search_end);
        case id_leaf: return makeNode(bind("configuration", help, KEY_INIT_DESC("Initializes this configuration\n")));
#define ARG(a)        argd.a
#define ARG_EXT(a, X) argd.a
#define OPTION(k, e, a, d, x, v)                                                                                       \
    case opt_##k: {                                                                                                    \
        if (help) {                                                                                                    \
            help->clear();                                                                                             \
            ValueDesc argd;                                                                                            \
            a;                                                                                                         \
            Option("dummy", d, std::move(argd)).description(*help);                                                    \
        }                                                                                                              \
        if (cliName) {                                                                                                 \
            *cliName = CLI_NAME(k).str();                                                                              \
        }                                                                                                              \
        return makeNode(#k, 0, 0);                                                                                     \
    }
#define CLASP_ALL_GROUPS
#include <clasp/cli/clasp_cli_options.inl>

        default: return makeNode(bind("", help, ""));
    }
}
constinit const ClaspCliConfig::KeyType ClaspCliConfig::key_invalid = static_cast<ClaspCliConfig::KeyType>(-1);
constinit const ClaspCliConfig::KeyType ClaspCliConfig::key_root    = makeKeyHandle(id_root, 0, 0);
constinit const ClaspCliConfig::KeyType ClaspCliConfig::key_solver  = makeKeyHandle(id_solver, 0, 0);
constinit const ClaspCliConfig::KeyType ClaspCliConfig::key_tester  = makeKeyHandle(id_tester, mode_tester, 0);
/// \endcond
/////////////////////////////////////////////////////////////////////////////////////////
// Interface to ProgramOptions
/////////////////////////////////////////////////////////////////////////////////////////
// Converts a command-line option name to an option key.
static void cliNameToKey(std::string& out, std::string_view n) {
    out = n;
    std::ranges::replace(out, '-', '_');
}
// Type for storing one command-line option.
// Adapter for parsing a command string.
struct ClaspCliConfig::ParseContext : Potassco::ProgramOptions::ParseContext {
    using Option = Potassco::ProgramOptions::Option;
    ParseContext(ClaspCliConfig& x, const char* c, const ParsedOpts& ex, uint8_t m, uint32_t s, ParsedOpts* o)
        : Potassco::ProgramOptions::ParseContext::ParseContext(c)
        , self(&x)
        , prev(x.parseCtx_)
        , exclude(&ex)
        , out(o)
        , sId(s)
        , mode(m) {
        x.parseCtx_ = this;
    }
    ~ParseContext() override { self->parseCtx_ = this->prev; }
    [[nodiscard]] auto       state(const Option& opt) const -> OptState override;
    [[nodiscard]] static int id(const Option& opt) { return static_cast<int>(opt.id()); }
    Option*                  doGetOption(std::string_view name, FindType ft) override;
    bool                     doSetValue(Option& opt, std::string_view value) override;
    void                     doFinish(const std::exception_ptr&) override {}

    uint64_t          seen[2] = {0, 0};
    std::string       temp;
    ClaspCliConfig*   self;
    ParseContext*     prev;
    const ParsedOpts* exclude;
    ParsedOpts*       out;
    uint32_t          sId;
    uint8_t           mode;
};
auto ClaspCliConfig::ParseContext::state(const Option& opt) const -> OptState {
    if (exclude->contains(opt.name())) {
        return OptState::state_skip;
    }
    if (auto optId = id(opt); Potassco::test_bit(seen[optId / 64], optId & 63)) {
        return OptState::state_seen;
    }
    return OptState::state_open;
}

bool ClaspCliConfig::ParseContext::doSetValue(Option& opt, std::string_view value) {
    if (not opt.assign(value)) {
        return false;
    }
    auto optId = id(opt);
    Potassco::store_set_bit(seen[optId / 64], optId & 63);
    if (out) {
        out->add(opt.name());
    }
    return true;
}
Potassco::ProgramOptions::Option* ClaspCliConfig::ParseContext::doGetOption(std::string_view cmdName, FindType ft) {
    Option* res = nullptr;
    if (ft == OptionContext::find_alias) {
        POTASSCO_ASSERT(not cmdName.empty() && (cmdName.front() != '-' || cmdName.size() > 1));
        char a = cmdName[cmdName.front() == '-'];
        res    = self->opts_->find(a);
    }
    else {
        auto name = cmdName;
        if (cmdName.find('-') != std::string_view::npos) {
            cliNameToKey(temp, cmdName);
            name = temp;
        }
        int16_t opt = findOption(name, (ft & OptionContext::find_prefix) != 0);
        if (opt >= 0) {
            res = (*self->opts_)[static_cast<std::size_t>(opt)].get();
        }
        else if (opt == -2) {
            throw Potassco::ProgramOptions::AmbiguousOption{this->name(), cmdName, {}};
        }
        assert(not res || id(*res) == opt);
    }
    if (res) {
        auto optId = id(*res);
        bool meta  = (mode & mode_meta) != 0;
        if (isSupportedOption(optId, mode) || (isRelaxed(mode) && isOption(optId)) || (not isOption(optId) && meta)) {
            return res;
        }
    }
    return nullptr;
}
/////////////////////////////////////////////////////////////////////////////////////////
// Default Configs
/////////////////////////////////////////////////////////////////////////////////////////
static constexpr const char* skipWs(const char* x) {
    while (*x == ' ' || *x == '\t') { ++x; }
    return x;
}
static const char* getIdent(const char* x, std::string& to) {
    for (x = skipWs(x); std::strchr(" \t:()[]", *x) == nullptr; ++x) { to += *x; }
    return x;
}
static constexpr bool matchSep(const char*& x, char c) {
    if (x = skipWs(x); *x == c) {
        ++x;
        return true;
    }
    return false;
}
static bool appendConfig(std::string& to, const std::string& line) {
    const char* x = skipWs(line.c_str());
    const bool  p = matchSep(x, '[');
    to.append("/[", 2);
    // match name in optional square brackets
    bool ok = matchSep(x = getIdent(x, to), ']') == p;
    to.append("]\0/", 3);
    // match optional base in parentheses followed by the start of the option list
    if (ok && (not matchSep(x, '(') || matchSep((x = getIdent(x, to)), ')')) && matchSep(x, ':')) {
        to.append("\0/", 2);
        to.append(skipWs(x));
        to.erase(to.find_last_not_of(" \t") + 1);
        to.append(1, '\0');
        return true;
    }
    return false;
}
template <typename T, typename U>
static constexpr T as(U u) {
    return static_cast<T>(u);
}
ConfigIter ClaspCliConfig::getConfig(ConfigKey k) {
#define MAKE_CONFIG(n, o1, o2) "/[" n "]\0/\0/" o1 " " o2 "\0"
    switch (k) {
#define CONFIG(id, n, c, s, p)                                                                                         \
    case config_##n: return ConfigIter(MAKE_CONFIG(#n, s, c));
#define CLASP_CLI_DEFAULT_CONFIGS
#define CLASP_CLI_AUX_CONFIGS
#include <clasp/cli/clasp_cli_configs.inl>

        case config_many:
#define CONFIG(id, n, c, s, p) MAKE_CONFIG("solver." POTASSCO_STRING(id), c, p)
#define CLASP_CLI_DEFAULT_CONFIGS
#define CLASP_CLI_AUX_CONFIGS
            return {
#include <clasp/cli/clasp_cli_configs.inl>

            };
        default:
            POTASSCO_CHECK_PRE(k == config_default, "Invalid config key '%d'", (int) k);
            return {"/default\0/\0/\0"};
    }
#undef MAKE_CONFIG
}
ConfigIter ClaspCliConfig::getConfig(uint8_t key, std::string& tempMem) const {
    POTASSCO_CHECK_PRE(key <= (config_max_value + 1), "Invalid key!");
    if (key < config_max_value) {
        return getConfig(static_cast<ConfigKey>(key));
    }
    const char*   name = config_[key - config_max_value].c_str();
    std::ifstream file(name);
    POTASSCO_CHECK(file, std::errc::no_such_file_or_directory, "Could not open config file '%s'", name);
    uint32_t lineNum = 0;
    tempMem.clear();
    for (std::string line, cont; std::getline(file, line);) {
        ++lineNum;
        line.erase(0, line.find_first_not_of(" \t"));
        if (line.empty() || line[0] == '#') {
            continue;
        }
        if (*line.rbegin() == '\\') {
            *line.rbegin()  = ' ';
            cont           += line;
            continue;
        }
        if (not cont.empty()) {
            cont += line;
            cont.swap(line);
            cont.clear();
        }
        POTASSCO_CHECK(appendConfig(tempMem, line), std::errc::not_supported, "'%s@%u': Invalid configuration", name,
                       lineNum);
    }
    tempMem.append(1, '\0');
    return {tempMem.data()};
}
int ClaspCliConfig::getConfigKey(std::string_view k) {
    ConfigKey ret;
    return ok(Potassco::stringTo(k, ret)) ? ret : -1;
}
const char* ClaspCliConfig::getDefaults(ProblemType t) {
    return t == ProblemType::asp ? "--configuration=tweety" : "--configuration=trendy";
}
ConfigIter::ConfigIter(const char* x) : base_(x) {}
const char* ConfigIter::name() const { return base_ + 1; }
const char* ConfigIter::base() const { return base_ + std::strlen(base_) + 2; }
const char* ConfigIter::args() const {
    const char* x = base();
    return x + std::strlen(x) + 2;
}
bool ConfigIter::valid() const { return *base_ != 0; }
bool ConfigIter::next() {
    base_  = args();
    base_ += std::strlen(base_) + 1;
    return valid();
}
/////////////////////////////////////////////////////////////////////////////////////////
// ClaspCliConfig
/////////////////////////////////////////////////////////////////////////////////////////
ClaspCliConfig::ClaspCliConfig() : parseCtx_(nullptr), validate_(false) {
    static_assert((option_category_context_begin < option_category_solver_begin) &&
                      (option_category_solver_begin < option_category_search_begin) &&
                      (option_category_search_begin < option_category_asp_begin) &&
                      (option_category_asp_begin < option_category_solve_begin) &&
                      (option_category_solve_begin < option_category_solve_end),
                  "unexpected option order");
}
ClaspCliConfig::~ClaspCliConfig() = default;
void ClaspCliConfig::reset() {
    config_[0] = config_[1] = "";
    validate_               = false;
    ClaspConfig::reset();
}
void ClaspCliConfig::prepare(SharedContext& ctx) {
    if (testerConfig()) {
        // Force init
        ClaspCliConfig::config("tester");
    }
    if (validate_) {
        ClaspCliConfig::validate();
    }
    ClaspConfig::prepare(ctx);
}
Configuration* ClaspCliConfig::config(const char* n) {
    if (n && std::strcmp(n, "tester") == 0) {
        if (not testerConfig()) {
            setAppOpt(meta_tester, 0, {});
        }
        return testerConfig();
    }
    return ClaspConfig::config(n);
}

void ClaspCliConfig::createOptions() {
    if (opts_.get()) {
        return;
    }
    opts_ = std::make_unique<Options>();
    using namespace Potassco::ProgramOptions;
    auto optAct       = makeCustom([this](const Option& opt, std::string_view value) {
        return setCliOption(opt.name(), static_cast<int>(opt.id()), value);
    });
    auto createOption = [&optAct](int o) { return value(optAct, static_cast<uint32_t>(o)); };
    opts_->addOptions()("configuration", createOption(meta_config).defaultsTo("auto", true),
                        KEY_INIT_DESC("Set default configuration [%D]\n"));

#define CLASP_ALL_GROUPS
#define OPTION(k, e, a, d, ...) opts_->addOptions()(CLI_NAME(k), e, (createOption(opt_##k) a), d);
#define ARG(a)                  .a
#define ARG_EXT(a, X)           ARG(a)
#include <clasp/cli/clasp_cli_options.inl>

    opts_->addOptions()("tester", createOption(meta_tester).arg("<options>"), "Pass (quoted) string of %A to tester");
}
void ClaspCliConfig::addOptions(OptionContext& root) {
    createOptions();
    using namespace Potassco::ProgramOptions;
#define MAKE_GROUP(X, ...) OptionGroup("Clasp." X " Options" POTASSCO_OPTARGS(__VA_ARGS__))
    auto addOpts = [this](OptionGroup& grp, const auto& range) -> OptionGroup& {
        for (auto idx : range) { grp.addOption(opts_->operator[](idx)); }
        return grp;
    };

    auto grp = MAKE_GROUP("Config");
    grp.addOption(opts_->operator[](0));
    grp.addOption(opts_->operator[](opts_->size() - 1));
    addOpts(grp, irange<uint32_t>(option_category_global_begin, option_category_global_end));
    root.add(std::move(grp));
    grp = MAKE_GROUP("Context", desc_level_e1);
    root.add(std::move(addOpts(grp, irange<uint32_t>(option_category_context_begin, option_category_context_end))));
    grp = MAKE_GROUP("ASP", desc_level_e1);
    root.add(std::move(addOpts(grp, irange<uint32_t>(option_category_asp_begin, option_category_asp_end))));
    grp = MAKE_GROUP("Solving", desc_level_default);
    root.add(std::move(addOpts(grp, irange<uint32_t>(option_category_asp_end, toU32(opts_->size()) - 1))));
    grp = MAKE_GROUP("Search", desc_level_e1);
    addOpts(grp, irange<uint32_t>(option_category_global_end, opt_no_lookback));
    addOpts(grp, irange<uint32_t>(option_category_solver_end, opt_restarts));
    root.add(std::move(grp));
    grp = MAKE_GROUP("Lookback", desc_level_e1);
    addOpts(grp, irange<uint32_t>(opt_no_lookback, option_category_solver_end));
    addOpts(grp, irange<uint32_t>(opt_restarts, option_category_search_end));
    root.add(std::move(grp));
#undef MAKE_GROUP
}
bool ClaspCliConfig::assignDefaults(const Potassco::ProgramOptions::ParsedOptions& exclude) {
    for (const auto& it : opts_->options()) {
        const auto& o = *it;
        POTASSCO_CHECK_PRE(exclude.contains(o.name()) || it->assignDefault(),
                           "Option '%" PRIsv "': invalid default value '%" PRIsv "'\n", PRI_SV(o.name()),
                           PRI_SV(o.defaultValue()));
    }
    return true;
}
void        ClaspCliConfig::releaseOptions() { opts_ = nullptr; }
static bool matchPath(std::string_view& path, std::string_view what) {
    std::size_t wLen = what.length();
    if (not path.starts_with(what) || (path.length() > wLen && path[wLen++] != '.')) {
        return false;
    }
    path.remove_prefix(wLen);
    return true;
}
// NOLINTNEXTLINE(misc-no-recursion)
ClaspCliConfig::KeyType ClaspCliConfig::getKey(KeyType key, std::string_view name) const {
    int16_t id = decodeKey(key);
    if (name.remove_prefix(name.starts_with('.')); not isValidId(id) || name.empty()) {
        return key;
    }
    if (isLeafId(id)) {
        return key_invalid;
    }
    NodeKey nk = getNode(id);
    for (int16_t sk = nk.skBeg; sk < 0; ++sk) {
        if (matchPath(name, getNode(sk).name)) {
            KeyType ret = makeKeyHandle(sk, (sk == id_tester ? mode_tester : 0) | decodeMode(key), 0);
            if (name.empty()) {
                return ret;
            }
            return getKey(ret, name);
        }
    }
    uint8_t mode = decodeMode(key);
    if (id == id_solver) {
        if (not isSolver(mode) && std::isdigit(static_cast<unsigned char>(name.front()))) {
            uint32_t solverId;
            if (auto ret = Potassco::fromChars(name, solverId); ret.ec == std::errc{}) {
                return getKey(
                    makeKeyHandle(id, mode | mode_solver, std::min(solverId, static_cast<uint32_t>(UINT8_MAX))),
                    ret.ptr);
            }
        }
        mode |= mode_solver;
    }
    int16_t opt = findOption(name, false);
    // the remaining name must be a valid option in our subkey range
    if (opt < 0 || opt < nk.skBeg || opt >= static_cast<int16_t>(nk.skBeg + nk.skSize)) {
        return key_invalid;
    }
    return makeKeyHandle(opt, mode, decodeSolver(key));
}

ClaspCliConfig::KeyType ClaspCliConfig::getArrKey(KeyType k, unsigned i) const {
    int16_t id = decodeKey(k);
    if (id != id_solver || isSolver(decodeMode(k)) || i >= solve.supportedSolvers()) {
        return key_invalid;
    }
    return makeKeyHandle(id, decodeMode(k) | mode_solver, i);
}
int ClaspCliConfig::getKeyInfo(KeyType k, int* nSubkeys, int* arrLen, std::string* help, int* nValues) const {
    int16_t id = decodeKey(k);
    if (not isValidId(id)) {
        return -1;
    }
    int  args = 0;
    auto x    = help || nSubkeys ? getNode(id, help) : NodeKey{};
    if (nSubkeys) {
        *nSubkeys = x.skSize;
        ++args;
    }
    if (arrLen) {
        *arrLen = -1;
        if (id == id_solver && not isSolver(decodeMode(k))) {
            const auto* c = active(this, decodeMode(k));
            *arrLen       = c ? static_cast<int>(c->numSolver()) : 0;
        }
        ++args;
    }
    if (help) {
        ++args;
    }
    if (nValues) {
        *nValues = isLeafId(id) ? static_cast<int>(not isTester(decodeMode(k)) || testerConfig() != nullptr) : -1;
        ++args;
    }
    return args;
}
bool ClaspCliConfig::isLeafKey(KeyType k) { return isLeafId(decodeKey(k)); }
// NOLINTNEXTLINE(readability-convert-member-functions-to-static)
std::string_view ClaspCliConfig::getSubkey(KeyType k, uint32_t i) const {
    int16_t id = decodeKey(k);
    if (not isValidId(id) || isLeafId(id)) {
        return {};
    }
    auto nk = getNode(id);
    if (i >= nk.skSize) {
        return {};
    }
    return getNode(static_cast<int16_t>(static_cast<int32_t>(i) + nk.skBeg)).name;
}
int ClaspCliConfig::getValue(KeyType key, std::string& out) const {
    try {
        const UserConfig* base = active(this, decodeMode(key));
        int16_t           o    = decodeKey(key);
        int               r    = isLeafId(o) && base ? 1 : -1;
        out.clear();
        if (r > 0 && isOption(o)) {
            POTASSCO_ASSERT(base == this || isTesterOption(o));
            uint32_t            sId    = decodeSolver(key);
            const SolverParams* solver = &base->solver(sId);
            const SolveParams*  search = &base->search(sId);
            // helper macros used in get
            using Potassco::off;
            using Potassco::Set;
            using Potassco::toString;
#define FUN(x)                                                                                                         \
    if (Potassco::StringRef x(out); false)                                                                             \
        ;                                                                                                              \
    else
#define GET(...)       out = toString(__VA_ARGS__)
#define GET_IF(c, ...) out = ((c) ? toString(__VA_ARGS__) : toString(off))
            switch (static_cast<OptionKey>(o)) {
                default: POTASSCO_ASSERT(false, "invalid option");
#define OPTION(k, e, a, h, _, GET)                                                                                     \
    case opt_##k: {                                                                                                    \
        GET;                                                                                                           \
    } break;
#define CLASP_ALL_GROUPS
#include <clasp/cli/clasp_cli_options.inl>
            }
#undef FUN
#undef GET
#undef GET_IF
        }
        else if (r > 0 && o == meta_config) {
            if (base->cliConfig < config_max_value) {
                toChars(out, static_cast<ConfigKey>(base->cliConfig));
            }
            else {
                out.append(config_[base == testerConfig()]);
            }
        }
        return r > 0 ? static_cast<int>(out.length()) : r;
    }
    catch (...) {
        return -2;
    }
}
std::string ClaspCliConfig::getValue(std::string_view path) const {
    std::string temp;
    POTASSCO_CHECK_PRE(getValue(getKey(key_root, path), temp) >= 0, "Invalid key: '%" PRIsv "'", PRI_SV(path));
    return temp;
}
bool ClaspCliConfig::hasValue(std::string_view path) const {
    int nVals;
    return getKeyInfo(getKey(key_root, path), nullptr, nullptr, nullptr, &nVals) == 1 && nVals > 0;
}

int ClaspCliConfig::setValue(KeyType key, std::string_view value) {
    int16_t id = decodeKey(key);
    if (not isLeafId(id)) {
        return -1;
    }
    try {
        uint8_t mode = decodeMode(key);
        validate_    = true;
        prepared     = false;
        if (isTester(mode)) {
            addTesterConfig();
        }
        if (isOption(id)) {
            return setOption(id, mode, decodeSolver(key), value);
        }
        int sz = setAppOpt(id, mode, value);
        if (sz <= 0) {
            return 0;
        }
        std::string m;
        UserConfig* act  = active(this, mode);
        ConfigIter  it   = getConfig(act->cliConfig, m);
        act->hasConfig   = 0;
        mode            |= mode_relaxed;
        act->resize(1, 1);
        for (uint32_t sId = 0; it.valid(); it.next()) {
            if (not setConfig(it, mode, sId, ParsedOpts(), nullptr)) {
                return 0;
            }
            if (++sId == static_cast<uint32_t>(sz)) {
                break;
            }
            mode |= mode_solver;
        }
        if (sz < 65 && static_cast<uint32_t>(sz) > act->numSolver()) {
            for (uint32_t sId = act->numSolver(), mod = sId, end = static_cast<uint32_t>(sz); sId != end; ++sId) {
                SolverParams& solver = act->addSolver(sId);
                SolveParams&  search = act->addSearch(sId);
                (solver = act->solver(sId % mod)).setId(sId);
                search = act->search(sId % mod);
            }
        }
        act->hasConfig = 1;
        return 1;
    }
    catch (...) {
        return -2;
    }
}

bool ClaspCliConfig::setValue(std::string_view path, std::string_view value) {
    int ret = setValue(getKey(key_root, path), value);
    POTASSCO_CHECK_PRE(ret >= 0,
                       (ret == -1 ? "Invalid or incomplete key: '%" PRIsv "'" : "Value error in key: '%" PRIsv "'"),
                       PRI_SV(path));
    return ret != 0;
}
int ClaspCliConfig::setOption(int option, uint8_t setMode, uint32_t sId, std::string_view _val_) {
    if (not isSupportedOption(option, setMode)) {
        return isRelaxed(setMode) ? 1 : -1;
    }
    BasicSatConfig* base   = active(this, setMode);
    SolverParams*   solver = isSolverOption(option) ? &base->addSolver(sId) : nullptr;
    SolveParams*    search = isSolverOption(option) ? &base->addSearch(sId) : nullptr;
    // action and helper macros used in set macros
    using Potassco::Set;
    using Potassco::stringTo;
    int ret = 1;
    try {
        unsigned _n;
        bool     _b;
#define FUN(x)           for (Potassco::ArgString x{_val_};;)
#define STORE(obj)       return ok(stringTo((_val_), obj));
#define STORE_LEQ(x, y)  return ok(stringTo(_val_, _n)) && SET_LEQ(x, _n, y);
#define STORE_FLAG(x)    return ok(stringTo(_val_, _b)) && SET(x, static_cast<unsigned>(_b));
#define STORE_OR_FILL(x) return ok(stringTo(_val_, _n)) && SET_OR_FILL(x, _n);
#define STORE_U(E, x)                                                                                                  \
    {                                                                                                                  \
        E _e;                                                                                                          \
        return ok(stringTo((_val_), _e)) && SET(x, static_cast<unsigned>(_e));                                         \
    }

        switch (static_cast<OptionKey>(option)) {
            default: POTASSCO_ASSERT(false, "invalid option");
#define OPTION(k, e, a, d, SET, ...)                                                                                   \
    case opt_##k: {                                                                                                    \
        SET;                                                                                                           \
    } break;
#define CLASP_ALL_GROUPS
#include <clasp/cli/clasp_cli_options.inl>
        }
#undef FUN
#undef STORE
#undef STORE_LEQ
#undef STORE_FLAG
#undef STORE_OR_FILL
#undef STORE_U
    }
    catch (...) {
        ret = 0;
    }
    return ret;
}
bool ClaspCliConfig::setCliOption(std::string_view name, int option, std::string_view value) {
    uint8_t  mode = parseCtx_ ? parseCtx_->mode : 0;
    uint32_t sId  = parseCtx_ ? parseCtx_->sId : 0;
    int      ret  = isOption(option) ? setOption(option, mode, sId, value) : setAppOpt(option, mode, value);
    POTASSCO_CHECK(ret != -1, std::errc::invalid_argument, "unexpected option '%" PRIsv "' in command-line",
                   PRI_SV(name));
    return ret > 0;
}
int ClaspCliConfig::setAppOpt(int o, uint8_t mode, std::string_view value) {
    if (o == meta_config) {
        auto sz = static_cast<unsigned>(INT32_MAX);
        auto r  = std::errc{};
        if (auto cfg = config_default; Potassco::extractOpt(false, value, cfg, r, sz)) {
            active(this, mode)->cliConfig = static_cast<uint8_t>(cfg);
        }
        else {
            std::string config{value};
            POTASSCO_CHECK(std::ifstream(config).is_open(), std::errc::no_such_file_or_directory,
                           "Could not open config file '%s'", config.c_str());
            config_[isTester(mode)]       = std::move(config);
            active(this, mode)->cliConfig = config_max_value + isTester(mode);
        }
        return Clasp::saturate_cast<int>(sz);
    }
    if (o == meta_tester && not isTester(mode)) {
        addTesterConfig();
        ParsedOpts ex;
        bool       ret = setConfig("<tester>", value, mode_tester | mode_meta, 0, ParsedOpts(), &ex);
        return ret && finalizeAppConfig(mode_tester, finalizeParsed(mode_tester, ex, ex), ProblemType::asp, true);
    }
    return -1; // invalid option
}
bool ClaspCliConfig::setAppDefaults(ConfigKey config, uint8_t mode, const ParsedOpts& seen, ProblemType t) {
    if (t != ProblemType::asp && not seen.contains(getOptionName(opt_sat_prepro))) {
        POTASSCO_CHECK_PRE(setOption(opt_sat_prepro, mode, 0, "2,iter=20,occ=25,time=120"));
    }
    if (not isTester(mode) && config == config_many && t == ProblemType::asp) {
        POTASSCO_CHECK_PRE(seen.contains(getOptionName(opt_eq)) || setOption(opt_eq, mode, 0, "3"));
        POTASSCO_CHECK_PRE(seen.contains(getOptionName(opt_trans_ext)) || setOption(opt_trans_ext, mode, 0, "dynamic"));
    }
    if (config != config_nolearn && active(this, mode)->solver(0).search == SolverParams::no_learning) {
        POTASSCO_CHECK_PRE(setConfig(getConfig(config_nolearn), mode | mode_relaxed, 0, seen, nullptr));
    }
    return true;
}

bool ClaspCliConfig::setConfig(const char* name, std::string_view args, uint8_t mode, uint32_t sId,
                               const ParsedOpts& exclude, ParsedOpts* out) {
    createOptions();
    ParseContext ctx(*this, name, exclude, mode, sId, out);
    parseCommandString(ctx, args, nullptr, Potassco::ProgramOptions::command_line_allow_flag_value);
    return true;
}
bool ClaspCliConfig::setConfig(const ConfigIter& config, uint8_t mode, uint32_t sId, const ParsedOpts& exclude,
                               ParsedOpts* out) {
    if (*config.base()) {
        ConfigKey baseK = config_default;
        POTASSCO_CHECK_PRE(ok(Potassco::stringTo(config.base(), baseK)), "%s: '%s': Invalid base config!",
                           config.name(), config.base());
        if (ConfigIter base = getConfig(baseK);
            not setConfig(base.name(), base.args(), mode | mode_solver, sId, exclude, out)) {
            return false;
        }
    }
    return setConfig(config.name(), config.args(), mode, sId, exclude, out);
}
bool ClaspCliConfig::setConfig(std::span<const char*> args, ProblemType t) {
    std::string cmdString;
    for (const auto* x : args) { cmdString.append(not cmdString.empty(), ' ').append(x); }
    Potassco::ProgramOptions::ParsedOptions exclude, parsed;
    reset();
    return setConfig("setConfig", cmdString, mode_meta, 0, exclude, &parsed) && assignDefaults(parsed) &&
           finalize(parsed, t, true);
}
bool ClaspCliConfig::validate() {
    UserConfiguration*  arr[3] = {this, testerConfig(), nullptr};
    UserConfiguration** c      = arr;
    const char*         ctx    = *c == this ? "config" : "tester";
    const char*         err    = nullptr;
    do {
        for (uint32_t i : irange((*c)->numSolver())) {
            POTASSCO_CHECK_PRE((err = Clasp::Cli::validate((*c)->solver(i), (*c)->search(i))) == nullptr, "<%s>.%u: %s",
                               ctx, i, err);
        }
    } while (*++c);
    validate_ = false;
    return true;
}

bool ClaspCliConfig::finalize(const ParsedOpts& x, ProblemType t, bool defs) {
    ParsedOpts temp;
    return finalizeAppConfig(0, finalizeParsed(0, x, temp), t, defs) &&
           finalizeAppConfig(mode_tester, ParsedOpts(), ProblemType::asp, true);
}

void ClaspCliConfig::addDisabled(ParsedOpts& parsed) { finalizeParsed(0, parsed, parsed); }

std::string_view ClaspCliConfig::getOptionName(int o) const {
    POTASSCO_ASSERT(isOption(o));
    if (opts_.get()) {
        return opts_->operator[](static_cast<std::size_t>(o))->name();
    }
    std::string_view cliName;
    std::ignore = getNode(static_cast<int16_t>(o), nullptr, &cliName);
    return cliName;
}

const ClaspCliConfig::ParsedOpts& ClaspCliConfig::finalizeParsed(uint8_t mode, const ParsedOpts& parsed,
                                                                 ParsedOpts& exclude) const {
    const ParsedOpts* ret = &parsed;
    if (active(this, mode)->search(0).reduce.fReduce() == 0 && parsed.contains(getOptionName(opt_deletion))) {
        if (ret != &exclude) {
            exclude = parsed;
        }
        exclude.add(getOptionName(opt_del_cfl));
        exclude.add(getOptionName(opt_del_max));
        exclude.add(getOptionName(opt_del_grow));
        ret = &exclude;
    }
    return *ret;
}

bool ClaspCliConfig::finalizeAppConfig(uint8_t mode, const ParsedOpts& parsed, ProblemType t, bool defs) {
    UserConfig* config = active(this, mode);
    if (not config || config->hasConfig) {
        return true;
    }
    auto    defSolver = config->solver(0);
    auto    defSearch = config->search(0);
    uint8_t c         = config->cliConfig;
    if (c == config_many && solve.numSolver() == 1) {
        c = config_default;
    }
    if (c == config_default) {
        if (defSolver.search == SolverParams::no_learning) {
            c = config_nolearn;
        }
        else if (isTester(mode)) {
            c = config_tester_default;
        }
        else if (solve.numSolver() == 1 || not solve.defaultPortfolio()) {
            c = static_cast<uint8_t>(t == ProblemType::asp ? config_asp_default : config_sat_default);
        }
        else {
            c = config_many;
        }
    }
    if (defs && not setAppDefaults(static_cast<ConfigKey>(c), mode, parsed, t)) {
        return false;
    }
    std::string m;
    ConfigIter  conf  = getConfig(c, m);
    mode             |= mode_relaxed;
    const char *ctx = isTester(mode) ? "tester" : "config", *err = nullptr;
    for (uint32_t i = 0; i != solve.numSolver() && conf.valid(); ++i) {
        SolverParams& solver = (config->addSolver(i) = defSolver).setId(i);
        SolveParams&  search = (config->addSearch(i) = defSearch);
        if (not setConfig(conf, mode, i, parsed, nullptr)) {
            return false;
        }
        POTASSCO_CHECK_PRE((err = Clasp::Cli::validate(solver, search)) == nullptr, "<%s>.%s : %s", ctx, conf.name(),
                           err);
        conf.next();
        mode |= mode_solver;
    }
    config->hasConfig = 1;
    return true;
}

const char* validate(const SolverParams& solver, const SolveParams& search) {
    const ReduceParams& reduce = search.reduce;
    if (solver.search == SolverParams::no_learning) {
        if (isLookbackHeuristic(solver.heuId)) {
            return "Heuristic requires lookback strategy!";
        }
        if (not search.restart.disabled()) {
            return "'no-lookback': restart options disabled!";
        }
        if (not reduce.cflSched.disabled() || (not reduce.growSched.disabled() && not reduce.growSched.defaulted()) ||
            search.reduce.fReduce() != 0) {
            return "'no-lookback': deletion options disabled!";
        }
    }
    bool hasSched = not reduce.cflSched.disabled() || not reduce.growSched.disabled() || reduce.maxRange != UINT32_MAX;
    if (hasSched && reduce.fReduce() == 0.0f && not reduce.growSched.defaulted()) {
        return "'no-deletion': deletion strategies disabled!";
    }
    if (not hasSched && reduce.fReduce() != 0.0f && not reduce.growSched.defaulted()) {
        return "'deletion': deletion strategy required!";
    }
    return nullptr;
}
} // namespace Cli
} // namespace Clasp
