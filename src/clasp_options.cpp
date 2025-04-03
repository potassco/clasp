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
#define ITE(c, a, b)        (!!(c) ? (a) : (b))
/////////////////////////////////////////////////////////////////////////////////////////
// Primitive types/functions for string <-> T conversions
/////////////////////////////////////////////////////////////////////////////////////////
namespace Potassco {
namespace {
struct KeyVal {
    const char* key;
    int         value;
};
struct OffType {
    friend std::string&           toChars(std::string& out, const OffType&) { return out.append("no"); }
    friend std::from_chars_result fromChars(std::string_view in, const OffType&) {
        bool temp = true;
        if (auto r = fromChars(in, temp); r.ec == std::errc{} && not temp) {
            return r;
        }
        return {std::data(in), std::errc::invalid_argument};
    }
};
constexpr OffType off = {};
struct StringRef {
    explicit StringRef(std::string& o) : out(&o) {}
    template <class T>
    friend StringRef& operator<<(StringRef& str, const T& val) {
        if (not str.out->empty()) {
            str.out->append(1, ',');
        }
        toChars(*str.out, val);
        return str;
    }
    std::string* out;
};
template <typename EnumT>
struct Set {
    explicit Set(unsigned v = 0) : val(v) {}
    [[nodiscard]] unsigned value() const { return val; }
    unsigned               val;
    friend std::string&    toChars(std::string& out, const Set& x) {
        if (unsigned bitset = x.val; bitset) {
            for (const auto& kv : enumMap(static_cast<EnumT*>(nullptr))) {
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
        if (auto r = Potassco::extract(in, n); Parse::ok(r)) {
            unsigned sum = 0;
            for (const auto& [_, value] : enumMap(static_cast<EnumT*>(nullptr))) {
                sum |= static_cast<unsigned>(value);
                if (n == static_cast<unsigned>(value) || (n && Potassco::test_mask(n, sum))) {
                    out.val = n;
                    return Parse::success(in, 0);
                }
            }
            return Parse::error(orig);
        }
        else if (r = extract(in, v); Parse::ok(r)) {
            do {
                out.val |= static_cast<unsigned>(v);
            } while (Parse::matchOpt(in, ',') && Parse::ok(r = extract(in, v)));
            return Parse::success(in, 0);
        }
        else {
            return Parse::error(in, r);
        }
    }
};

struct ArgString {
    explicit ArgString(const char* x) : in(x) {}
    ~ArgString() noexcept(false) {
        POTASSCO_CHECK(not ok() || in.empty() || off(), std::errc::invalid_argument,
                       "unexpected extra data in argument");
    }
    [[nodiscard]] bool ok() const { return in.data() != nullptr; }
    [[nodiscard]] bool off() const { return ok() && Parse::ok(stringTo(in, Potassco::off)); }
    [[nodiscard]] bool empty() const { return ok() && in.empty(); }
    operator const void*() const { return in.data(); } // NOLINT
    [[nodiscard]] char peek() const {
        auto r = in.substr(in.starts_with(skip));
        return not r.empty() ? r.front() : static_cast<char>(0);
    }
    template <class T>
    ArgString& get(T& x) {
        if (ok()) {
            if (auto r = fromChars(in.substr(in.starts_with(skip)), x); Parse::ok(r)) {
                in.remove_prefix(static_cast<std::size_t>(r.ptr - in.data()));
            }
            else {
                in = {nullptr, 0};
            }
            skip = ',';
        }
        return *this;
    }
    template <typename T>
    friend ArgString& operator>>(ArgString& arg, T& x) {
        return arg.get(x);
    }
    std::string_view in;
    char             skip{0};
    template <typename T>
    struct Opt {
        explicit Opt(T& x) : obj(&x) {}
        T*                obj;
        friend ArgString& operator>>(ArgString& arg, const Opt& x) { return not arg.empty() ? arg.get(*x.obj) : arg; }
    };
};
} // namespace
template <typename T>
static constexpr ArgString::Opt<T> opt(T& x) {
    return ArgString::Opt<T>(x);
}
using namespace std::literals;
static const KeyVal* findValue(Clasp::SpanView<KeyVal> map, std::string_view in, std::size_t* len,
                               std::string_view sep = ","sv) {
    auto          key    = in.substr(0, in.find_first_of(sep));
    const KeyVal* needle = nullptr;
    std::size_t   pop    = 0;
    for (const auto& kv : map) {
        if (Parse::eqIgnoreCase(key.data(), kv.key, key.length()) && not kv.key[key.length()]) {
            needle = &kv;
            pop    = key.length();
            break;
        }
    }
    if (len) {
        *len = pop;
    }
    return needle;
}
static const char* findKey(Clasp::SpanView<KeyVal> map, int x) {
    for (const auto& [key, value] : map) {
        if (value == x) {
            return key;
        }
    }
    return "";
}

} // namespace Potassco

namespace Clasp {
/////////////////////////////////////////////////////////////////////////////////////////
// Errors
/////////////////////////////////////////////////////////////////////////////////////////
using OptionError = Potassco::ProgramOptions::ContextError;
using ValueError  = Potassco::ProgramOptions::ValueError;
POTASSCO_ATTR_NORETURN void failOption(OptionError::Type type, const std::string& ctx, const std::string& opt,
                                       const std::string& desc = "") {
    using namespace Potassco::ProgramOptions;
    switch (type) {
        case OptionError::unknown_option  : throw UnknownOption(ctx, opt);
        case OptionError::ambiguous_option: throw AmbiguousOption(ctx, opt, desc);
        default                           : throw ContextError(ctx, type, opt, desc);
    }
}

POTASSCO_ATTR_NORETURN void failValue(ValueError::Type type, const std::string& ctx, const std::string& opt,
                                      const std::string& value) {
    using namespace Potassco::ProgramOptions;
    throw ValueError(ctx, type, opt, value);
}
/////////////////////////////////////////////////////////////////////////////////////////
// Enum mappings for clasp types
/////////////////////////////////////////////////////////////////////////////////////////
#define MAP(x, y)                                                                                                      \
    { static_cast<const char*>(x), static_cast<int>(y) }
#define DEFINE_ENUM_MAPPING(X, ...)                                                                                    \
    static Clasp::SpanView<Potassco::KeyVal> enumMap(const X*) {                                                       \
        static const Potassco::KeyVal map[] = {__VA_ARGS__};                                                           \
        return {map, sizeof(map) / sizeof(map[0])};                                                                    \
    }                                                                                                                  \
    std::from_chars_result fromChars(std::string_view in, X& out) {                                                    \
        auto len = std::size_t(0);                                                                                     \
        auto ec  = std::errc::invalid_argument;                                                                        \
        if (const auto* it = Potassco::findValue(enumMap(&out), in, &len)) {                                           \
            out = static_cast<X>(it->value);                                                                           \
            ec  = std::errc{};                                                                                         \
        }                                                                                                              \
        return {in.data() + len, ec};                                                                                  \
    }                                                                                                                  \
    static std::string& toChars(std::string& out, X x) {                                                               \
        return out.append(Potassco::findKey(enumMap(&x), static_cast<int>(x)));                                        \
    }
#define OPTION(k, e, a, d, ...) a
#define CLASP_ALL_GROUPS
#define ARG_EXT(a, X) X
#define ARG(a)
#define NO_ARG
#include <clasp/cli/clasp_cli_options.inl>
namespace Cli {
DEFINE_ENUM_MAPPING(ConfigKey, MAP("auto", config_default), MAP("frumpy", config_frumpy), MAP("jumpy", config_jumpy),
                    MAP("tweety", config_tweety), MAP("handy", config_handy), MAP("crafty", config_crafty),
                    MAP("trendy", config_trendy), MAP("many", config_many))
}
#undef MAP
#undef DEFINE_ENUM_MAPPING
/////////////////////////////////////////////////////////////////////////////////////////
// Conversion functions for complex clasp types
/////////////////////////////////////////////////////////////////////////////////////////
using Potassco::Parse::ok;
static std::string& toChars(std::string& out, const SatPreParams& p) {
    if (not p.type) {
        return toChars(out, Potassco::off);
    }
    Potassco::toChars(out, p.type);
    if (auto n = p.limIters) {
        Potassco::toChars(out.append(",iter="), n);
    }
    if (auto n = p.limOcc) {
        Potassco::toChars(out.append(",occ="), n);
    }
    if (auto n = p.limTime) {
        Potassco::toChars(out.append(",time="), n);
    }
    if (auto n = p.limFrozen) {
        Potassco::toChars(out.append(",frozen="), n);
    }
    if (auto n = p.limClause) {
        Potassco::toChars(out.append(",size="), n);
    }
    return out;
}
static std::from_chars_result fromChars(std::string_view in, SatPreParams& out) {
    if (auto r = fromChars(in, Potassco::off); ok(r)) {
        out = SatPreParams();
        return r;
    }
    uint32_t n;
    if (auto r = Potassco::extract(in, n); not ok(r) || not SET(out.type, n)) {
        return Potassco::Parse::error(in, not ok(r) ? r : std::errc::result_out_of_range);
    }
    Potassco::KeyVal kv[5] = {{"iter", 0}, {"occ", 0}, {"time", 0}, {"frozen", 0}, {"size", 4000}};
    for (uint32_t id = 0; Potassco::Parse::matchOpt(in, ','); ++id) {
        std::size_t len;
        if (const auto* val = Potassco::findValue(kv, in, &len, ":="); val != nullptr) {
            id = static_cast<uint32_t>(val - kv);
            in.remove_prefix(len);
            Potassco::Parse::matchOpt(in, '=') || Potassco::Parse::matchOpt(in, ':');
        }
        if (id > 4 || not ok(Potassco::extract(in, kv[id].value))) {
            break;
        }
    }
    SET_OR_ZERO(out.limIters, unsigned(kv[0].value));
    SET_OR_ZERO(out.limOcc, unsigned(kv[1].value));
    SET_OR_ZERO(out.limTime, unsigned(kv[2].value));
    SET_OR_ZERO(out.limFrozen, unsigned(kv[3].value));
    SET_OR_ZERO(out.limClause, unsigned(kv[4].value));
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
    unsigned        n;
    OptParams::Type t;
    if (auto r = Potassco::extract(in, n); ok(r)) { // clasp-3.0: <n>
        return setOptLegacy(out, n) ? Potassco::Parse::success(in, 0)
                                    : Potassco::Parse::error(in, std::errc::result_out_of_range);
    }
    if (auto r = Potassco::extract(in, t); not ok(r)) { // {bb|usc}[,<tactics>]
        return Potassco::Parse::error(in);
    }
    setOptLegacy(out, static_cast<uint32_t>(t) * 4);
    if (Potassco::Parse::matchOpt(in, ',')) {
        if (auto r = Potassco::extract(in, n); ok(r)) { // clasp-3.2: (bb|usc),<n>
            return setOptLegacy(out, n + (static_cast<uint32_t>(t) * 4))
                       ? Potassco::Parse::success(in, 0)
                       : Potassco::Parse::error(in, std::errc::result_out_of_range);
        }
        if (OptParams::BBAlgo bb; t == OptParams::type_bb && ok(Potassco::extract(in, bb))) {
            out.algo = bb;
        }
        else if (t == OptParams::type_usc) {
            auto usc  = OptParams::usc_oll;
            auto more = true;
            if (ok(Potassco::extract(in, usc))) {
                auto next = in;
                if (usc == OptParams::usc_k && Potassco::Parse::matchOpt(next, ',') && ok(Potassco::extract(next, n))) {
                    SET_OR_FILL(out.kLim, n);
                    in = next;
                }
                more = Potassco::Parse::matchOpt(in, ',');
            }
            Potassco::Set<OptParams::UscOption> opts(0);
            out.algo = usc;
            if (more && (ok(Potassco::extract(in, Potassco::off)) || ok(Potassco::extract(in, opts)))) {
                out.opts = opts.value();
            }
        }
    }
    return Potassco::Parse::success(in, 0);
}

static std::string& toChars(std::string& out, const ScheduleStrategy& sched) {
    using Potassco::toChars;
    if (sched.defaulted()) {
        return toChars(out, ScheduleStrategy());
    }
    if (sched.disabled()) {
        return out.append("0");
    }
    auto t = out.size();
    out.append("f,");
    toChars(out, sched.base);
    switch (sched.type) {
        case ScheduleStrategy::sched_geom:
            out[t] = 'x';
            return toChars(out.append(1, ','), std::make_pair(static_cast<double>(sched.grow), sched.len));
        case ScheduleStrategy::sched_arith:
            if (sched.grow != 0.0f) {
                out[t] = '+';
                return toChars(out.append(1, ','), std::make_pair(static_cast<uint32_t>(sched.grow), sched.len));
            }
            out[t] = 'f';
            return out;
        case ScheduleStrategy::sched_luby:
            out[t] = 'l';
            if (sched.len) {
                return toChars(out.append(1, ','), sched.len);
            }
            return out;
        default: POTASSCO_ASSERT_NOT_REACHED("toChars(ScheduleStrategy): unknown type");
    }
}
static std::string& toChars(std::string& out, const RestartSchedule& in) {
    if (in.disabled() || not in.isDynamic()) {
        return toChars(out, static_cast<const ScheduleStrategy&>(in));
    }
    using Potassco::toChars;
    toChars(out.append("d,"), std::make_pair(in.base, in.grow));
    auto lbdLim = in.lbdLim();
    auto fast   = in.fastAvg();
    auto slow   = in.slowAvg();
    if (lbdLim || fast != MovingAvg::avg_sma || slow != MovingAvg::avg_sma) {
        toChars(out.append(1, ','), lbdLim);
    }
    if (fast != MovingAvg::avg_sma || slow != MovingAvg::avg_sma) {
        toChars(out.append(1, ','), fast);
    }
    if (fast != MovingAvg::avg_sma && in.keepAvg()) {
        toChars(out.append(1, ','), static_cast<RestartSchedule::Keep>(in.keepAvg()));
    }
    if (slow != MovingAvg::avg_sma) {
        toChars(out.append(1, ','), slow);
        if (in.slowWin()) {
            toChars(out.append(1, ','), in.slowWin());
        }
    }
    return out;
}

// <type {F|L|x|+}>,<n {1..umax}>[,<args>][,<lim>]
static std::from_chars_result fromChars(std::string_view in, ScheduleStrategy& out) {
    constexpr Potassco::KeyVal types[] = {{"f", 'f'}, {"fixed", 'f'}, {"l", 'l'}, {"luby", 'l'},
                                          {"x", 'x'}, {"*", 'x'},     {"+", '+'}, {"add", '+'}};

    std::size_t len  = 0;
    const auto* type = Potassco::findValue(types, in, &len);
    uint32_t    base = 0;
    using namespace Potassco::Parse;
    if (not type || not matchOpt(in = in.substr(len), ',') || not ok(Potassco::extract(in, base)) || base == 0) {
        return error(in);
    }
    std::errc ec = {};
    switch (static_cast<char>(type->value)) {
        default: POTASSCO_ASSERT_NOT_REACHED("unexpected schedule strategy");
        case 'f': // Fixed
            out = ScheduleStrategy::fixed(base);
            break;
        case 'l': // Luby
            if (uint32_t lim = 0; not matchOpt(in, ',') || ok(ec = Potassco::extract(in, lim))) {
                out = ScheduleStrategy::luby(base, lim);
            }
            break;
        case 'x': // Geometric
            ec = std::errc::invalid_argument;
            if (std::pair<double, uint32_t> arg(0, 0); matchOpt(in, ',') && ok(ec = Potassco::extract(in, arg))) {
                out = ScheduleStrategy::geom(base, arg.first, arg.second);
            }
            break;
        case '+': // Arithmetic
            ec = std::errc::invalid_argument;
            if (std::pair<uint32_t, uint32_t> arg(0, 0); matchOpt(in, ',') && ok(ec = Potassco::extract(in, arg))) {
                out = ScheduleStrategy::arith(base, arg.first, arg.second);
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
    std::pair<uint32_t, double> req(0, 0);
    auto                        next = in;
    if (not ok(Potassco::extract(next, req)) || req.first == 0 || req.second <= 0.0) {
        return error(in);
    }
    uint32_t lim = 0, sWin = 0;
    auto     fast = MovingAvg::Type::avg_sma;
    auto     slow = MovingAvg::Type::avg_sma;
    auto     keep = RestartSchedule::keep_never;
    in            = next;
    if (matchOpt(in, ',') && not ok(Potassco::extract(in, lim))) {
        return error(in);
    }
    if (matchOpt(in, ',') && not ok(Potassco::extract(in, fast))) {
        return error(in);
    }
    next = in;
    if (matchOpt(next, ',') && fast != MovingAvg::Type::avg_sma && ok(Potassco::extract(next, keep))) {
        in = next;
    }
    if (matchOpt(in, ',') && not ok(Potassco::extract(in, slow))) {
        return error(in);
    }
    if (matchOpt(in, ',') && slow != MovingAvg::Type::avg_sma && not ok(Potassco::extract(in, sWin))) {
        return error(in);
    }
    out = RestartSchedule::dynamic(req.first, static_cast<float>(req.second), lim, fast, keep, slow, sWin);
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
    const char* name;
    const char* desc;
    int16_t     skBeg;
    uint16_t    skSize;
};
enum { id_root = -5, id_tester = -4, id_solve = -3, id_asp = -2, id_solver = -1, id_leaf = 0 };
struct Name2Id {
    const char* name;
    int         key;
    bool        operator<(const Name2Id& rhs) const { return *this < rhs.name; }
    bool        operator<(const char* rhs) const { return std::strcmp(name, rhs) < 0; }
};
Name2Id g_index[detail_num_options + 1] = {{"configuration", meta_config},
#define OPTION(k, e, ...) {#k, opt_##k},
#define CLASP_ALL_GROUPS
#include <clasp/cli/clasp_cli_options.inl>

                                           {"tester", meta_tester}};
[[maybe_unused]] bool g_init_index = (std::sort(g_index, g_index + detail_num_options + 1), true);
} // namespace
/// \cond
// Valid option keys.
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
static constexpr uint8_t         mode_solver  = 1u;
static constexpr uint8_t         mode_tester  = 2u;
static constexpr uint8_t         mode_relaxed = 4u;
static constexpr uint8_t         mode_meta    = 8u;
static constexpr bool            isTester(uint8_t mode) { return (mode & mode_tester) != 0; }
static constexpr bool            isSolver(uint8_t mode) { return (mode & mode_solver) != 0; }
static constexpr BasicSatConfig* active(ClaspConfig* config, uint8_t mode) {
    return not isTester(mode) ? config : config->testerConfig();
}
static constexpr const BasicSatConfig* active(const ClaspConfig* config, uint8_t mode) {
    return active(const_cast<ClaspConfig*>(config), mode);
}
static constexpr int16_t findOption(const char* needle, bool prefix) {
    const Name2Id* end = g_index + detail_num_options + 1;
    const Name2Id* it  = std::lower_bound(const_cast<const Name2Id*>(g_index), end, needle);
    int            ret = -1;
    if (it != end) {
        std::size_t len = std::strlen(needle);
        if (std::strncmp(it->name, needle, len) == 0 && (not it->name[len] || prefix)) {
            const Name2Id* next = it + 1;
            ret = not it->name[len] || next == end || std::strncmp(next->name, needle, len) != 0 ? it->key : -2;
        }
    }
    return static_cast<int16_t>(ret);
}
static constexpr NodeKey makeNode(const char* name, const char* desc, int16_t skBeg = 0, int16_t skEnd = 0) {
    NodeKey n = {name, desc, skBeg, static_cast<uint16_t>(skEnd - skBeg)};
    return n;
}
static NodeKey getNode(int16_t id) {
    assert(isValidId(id));
    switch (id) {
        case id_root  : return makeNode("", "Options", id_tester, option_category_global_end);
        case id_tester: return makeNode("tester", "Tester Options", id_solver, option_category_context_end);
        case id_solve:
            return makeNode("solve", "Solve Options", option_category_solve_begin, option_category_solve_end);
        case id_asp: return makeNode("asp", "Asp Options", option_category_asp_begin, option_category_asp_end);
        case id_solver:
            return makeNode("solver", "Solver Options", option_category_solver_begin, option_category_search_end);
        case id_leaf: return makeNode("configuration", KEY_INIT_DESC("Initializes this configuration\n"));
#define OPTION(k, e, a, d, x, v)                                                                                       \
    case opt_##k: return makeNode(#k, d);
#define CLASP_ALL_GROUPS
#include <clasp/cli/clasp_cli_options.inl>

        default: return makeNode("", "");
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
// Converts option key to command-line option name.
static void keyToCliName(std::string& out, const char* n, const char* ext) {
    out.clear();
    for (const char* x; (x = std::strchr(n, '_')) != nullptr; n = ++x) {
        out.append(n, static_cast<std::size_t>(x - n));
        out.append(1, '-');
    }
    out.append(n).append(ext);
}
// Converts command-line option name to option key.
static void cliNameToKey(std::string& out, const char* n) {
    out.clear();
    for (const char* x; (x = std::strchr(n, '-')) != nullptr; n = ++x) {
        out.append(n, static_cast<std::size_t>(x - n));
        out.append(1, '_');
    }
    out.append(n);
}
// Type for storing one command-line option.
// Adapter for parsing a command string.
struct ClaspCliConfig::ParseContext : Potassco::ProgramOptions::ParseContext {
    using OptPtr = Potassco::ProgramOptions::SharedOptPtr;
    ParseContext(ClaspCliConfig& x, const char* c, const ParsedOpts* ex, uint8_t m, uint32_t s, ParsedOpts* o)
        : self(&x)
        , prev(x.parseCtx_)
        , config(c)
        , exclude(ex)
        , out(o)
        , sId(s)
        , mode(m) {
        x.parseCtx_ = this;
    }
    ~ParseContext() override { self->parseCtx_ = this->prev; }
    OptPtr            getOption(const char* name, FindType ft) override;
    OptPtr            getOption(int, const char* key) override { failOption(OptionError::unknown_option, config, key); }
    void              addValue(const OptPtr& key, const std::string& value) override;
    uint64_t          seen[2] = {0, 0};
    std::string       temp;
    ClaspCliConfig*   self;
    ParseContext*     prev;
    const char*       config;
    const ParsedOpts* exclude;
    ParsedOpts*       out;
    uint32_t          sId;
    uint8_t           mode;
};
class ClaspCliConfig::ProgOption : public Potassco::ProgramOptions::Value {
public:
    ProgOption(ClaspCliConfig& c, int o) : config_(&c), option_(o) {}
    bool doParse(const std::string& opt, const std::string& value) override {
        uint8_t  mode = config_->parseCtx_ ? config_->parseCtx_->mode : 0;
        uint32_t sId  = config_->parseCtx_ ? config_->parseCtx_->sId : 0;
        int      ret  = isOption(option_) ? config_->setOption(option_, mode, sId, value.c_str())
                                          : config_->setAppOpt(option_, mode, value.c_str());
        if (ret == -1) {
            failOption(OptionError::unknown_option, not isTester(mode) ? "<clasp>" : "<tester>", opt);
        }
        return ret > 0;
    }
    [[nodiscard]] int option() const { return option_; }

private:
    ClaspCliConfig* config_;
    int             option_;
};
void ClaspCliConfig::ParseContext::addValue(const OptPtr& key, const std::string& value) {
    using namespace Potassco::ProgramOptions;
    if (not exclude->contains(key->name())) {
        auto*     v  = static_cast<ProgOption*>(key->value());
        auto      s  = v->state();
        int       id = v->option();
        uint64_t& xs = seen[id / 64];
        uint64_t  m  = static_cast<uint64_t>(1u) << (id & 63);
        if ((xs & m) != 0 && not v->isComposing()) {
            failValue(ValueError::multiple_occurrences, config, key->name(), value);
        }
        if (not v->parse(key->name(), value, s)) {
            failValue(ValueError::invalid_value, config, key->name(), value);
        }
        if (out) {
            out->add(key->name());
        }
        xs |= m;
    }
}
Potassco::ProgramOptions::SharedOptPtr ClaspCliConfig::ParseContext::getOption(const char* cmdName, FindType ft) {
    auto              end = self->opts_->end(), it = end;
    OptionError::Type error = OptionError::unknown_option;
    bool              meta  = (mode & mode_meta) != 0;
    if (ft == OptionContext::find_alias) {
        char a = cmdName[*cmdName == '-'];
        for (it = self->opts_->begin(); it != end && it->get()->alias() != a; ++it) { ; }
    }
    else {
        const char* name = cmdName;
        if (std::strchr(cmdName, '-') != nullptr) {
            cliNameToKey(temp, cmdName);
            name = temp.c_str();
        }
        int16_t opt = findOption(name, (ft & OptionContext::find_prefix) != 0);
        if (opt >= 0) {
            it = self->opts_->begin() + opt;
        }
        else if (opt == -2) {
            error = OptionError::ambiguous_option;
        }
        assert(it == end || static_cast<const ProgOption*>(it->get()->value())->option() == opt);
    }
    if (it != end && (meta || isOption(static_cast<const ProgOption*>(it->get()->value())->option()))) {
        return *it;
    }
    failOption(error, config, cmdName);
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
    // match optional base in parentheses followed by start of option list
    if (ok && (not matchSep(x, '(') || matchSep((x = getIdent(x, to)), ')')) && matchSep(x, ':')) {
        to.append("\0/", 2);
        to.append(skipWs(x));
        to.erase(to.find_last_not_of(" \t") + 1);
        to.append(1, '\0');
        return true;
    }
    return false;
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
int ClaspCliConfig::getConfigKey(const char* k) {
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
            setAppOpt(meta_tester, 0, "");
        }
        return testerConfig();
    }
    return ClaspConfig::config(n);
}

ClaspCliConfig::ProgOption* ClaspCliConfig::createOption(int o) { return new ProgOption(*this, o); }

void ClaspCliConfig::createOptions() {
    if (opts_.get()) {
        return;
    }
    opts_ = std::make_unique<Options>();
    using namespace Potassco::ProgramOptions;
    opts_->addOptions()("configuration", createOption(meta_config)->defaultsTo("auto")->state(Value::value_defaulted),
                        KEY_INIT_DESC("Set default configuration [%D]\n"));
    std::string cmdName;
#define CLASP_ALL_GROUPS
#define OPTION(k, e, a, d, ...)                                                                                        \
    keyToCliName(cmdName, #k, e);                                                                                      \
    opts_->addOptions()(cmdName.c_str(), static_cast<ProgOption*>(createOption(opt_##k) a), d);
#define ARG(a)        ->a
#define ARG_EXT(a, X) ARG(a)
#define NO_ARG
#include <clasp/cli/clasp_cli_options.inl>

    opts_->addOptions()("tester", createOption(meta_tester)->arg("<options>"), "Pass (quoted) string of %A to tester");
}
void ClaspCliConfig::addOptions(OptionContext& root) {
    createOptions();
    using namespace Potassco::ProgramOptions;
    OptionGroup configOpts("Clasp.Config Options");
    OptionGroup ctxOpts("Clasp.Context Options", Potassco::ProgramOptions::desc_level_e1);
    OptionGroup solving("Clasp.Solving Options");
    OptionGroup aspOpts("Clasp.ASP Options", Potassco::ProgramOptions::desc_level_e1);
    OptionGroup search("Clasp.Search Options", Potassco::ProgramOptions::desc_level_e1);
    OptionGroup lookback("Clasp.Lookback Options", Potassco::ProgramOptions::desc_level_e1);
    configOpts.addOption(*opts_->begin());
    configOpts.addOption(*(opts_->end() - 1));
    for (const auto& o : std::ranges::subrange(opts_->begin() + 1, opts_->end() - 1)) {
        if (int oId = static_cast<ProgOption*>(o->value())->option(); isGlobalOption(oId)) {
            configOpts.addOption(o);
        }
        else if (oId < option_category_context_end) {
            ctxOpts.addOption(o);
        }
        else if (oId < option_category_search_end) {
            if (oId < opt_no_lookback || (oId >= option_category_solver_end && oId < opt_restarts)) {
                search.addOption(o);
            }
            else {
                lookback.addOption(o);
            }
        }
        else if (oId < option_category_asp_end) {
            aspOpts.addOption(o);
        }
        else {
            solving.addOption(o);
        }
    }

    root.add(configOpts).add(ctxOpts).add(aspOpts).add(solving).add(search).add(lookback);
    root.addAlias("number", root.find("models"));        // remove on next version
    root.addAlias("opt-sat", root.find("parse-maxsat")); // remove on next version
}
bool ClaspCliConfig::assignDefaults(const Potassco::ProgramOptions::ParsedOptions& exclude) {
    for (const auto& it : *opts_) {
        const Potassco::ProgramOptions::Option& o = *it;
        POTASSCO_CHECK_PRE(exclude.contains(o.name()) || o.assignDefault(), "Option '%s': invalid default value '%s'\n",
                           o.name().c_str(), o.value()->defaultsTo());
    }
    return true;
}
void        ClaspCliConfig::releaseOptions() { opts_ = nullptr; }
static bool matchPath(const char*& path, const char* what) {
    std::size_t wLen = std::strlen(what);
    if (strncmp(path, what, wLen) != 0 || (path[wLen] && path[wLen++] != '.')) {
        return false;
    }
    path += wLen;
    return true;
}
// NOLINTNEXTLINE(misc-no-recursion)
ClaspCliConfig::KeyType ClaspCliConfig::getKey(KeyType key, const char* name) const {
    int16_t id = decodeKey(key);
    if (not isValidId(id) || not name || !*name || (*name == '.' && !*++name)) {
        return key;
    }
    if (isLeafId(id)) {
        return key_invalid;
    }
    NodeKey nk = getNode(id);
    for (int16_t sk = nk.skBeg; sk < 0; ++sk) {
        if (matchPath(name, getNode(sk).name)) {
            KeyType ret = makeKeyHandle(sk, (sk == id_tester ? mode_tester : 0) | decodeMode(key), 0);
            if (!*name) {
                return ret;
            }
            return getKey(ret, name);
        }
    }
    uint8_t mode = decodeMode(key);
    if (id == id_solver) {
        if (not isSolver(mode) && std::isdigit(static_cast<unsigned char>(*name))) {
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
    // remaining name must be a valid option in our subkey range
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
int ClaspCliConfig::getKeyInfo(KeyType k, int* nSubkeys, int* arrLen, const char** help, int* nValues) const {
    int16_t id  = decodeKey(k);
    int     ret = 0;
    if (not isValidId(id)) {
        return -1;
    }
    if (isLeafId(id)) {
        if (nSubkeys && ++ret) {
            *nSubkeys = 0;
        }
        if (arrLen && ++ret) {
            *arrLen = -1;
        }
        if (nValues && ++ret) {
            *nValues = static_cast<int>(not isTester(decodeMode(k)) || testerConfig() != nullptr);
        }
        if (help && ++ret) {
            *help = getNode(id).desc;
        }
        return ret;
    }
    NodeKey x = getNode(id);
    if (nSubkeys && ++ret) {
        *nSubkeys = x.skSize;
    }
    if (nValues && ++ret) {
        *nValues = -1;
    }
    if (help && ++ret) {
        *help = x.desc;
    }
    if (arrLen && ++ret) {
        *arrLen = -1;
        if (id == id_solver && not isSolver(decodeMode(k))) {
            const UserConfig* c = active(this, decodeMode(k));
            *arrLen             = c ? static_cast<int>(c->numSolver()) : 0;
        }
    }
    return ret;
}
bool ClaspCliConfig::isLeafKey(KeyType k) { return isLeafId(decodeKey(k)); }
// NOLINTNEXTLINE(readability-convert-member-functions-to-static)
const char* ClaspCliConfig::getSubkey(KeyType k, uint32_t i) const {
    int16_t id = decodeKey(k);
    if (not isValidId(id) || isLeafId(id)) {
        return nullptr;
    }
    auto nk = getNode(id);
    if (i >= nk.skSize) {
        return nullptr;
    }
    return getNode(static_cast<int16_t>(static_cast<int32_t>(i) + nk.skBeg)).name;
}
int ClaspCliConfig::getValue(KeyType key, std::string& out) const {
    try {
        const UserConfig* base = active(this, decodeMode(key));
        int16_t           o    = decodeKey(key);
        int               r    = isLeafId(o) && base ? 1 : -1;
        if (r > 0 && isOption(o)) {
            POTASSCO_ASSERT(base == this || isTesterOption(o));
            uint32_t            sId    = decodeSolver(key);
            const SolverParams* solver = &base->solver(sId);
            const SolveParams*  search = &base->search(sId);
            // helper macros used in get
            using Potassco::off;
            using Potassco::Set;
            using Potassco::toString;
#define GET_FUN(x)                                                                                                     \
    if (Potassco::StringRef x(out); false)                                                                             \
        ;                                                                                                              \
    else
#define GET(...)       out = toString(__VA_ARGS__)
#define GET_IF(c, ...) out = ITE((c), toString(__VA_ARGS__), toString(off))
            switch (static_cast<OptionKey>(o)) {
                default: POTASSCO_ASSERT(false, "invalid option");
#define OPTION(k, e, a, h, _, GET)                                                                                     \
    case opt_##k: {                                                                                                    \
        GET;                                                                                                           \
    } break;
#define CLASP_ALL_GROUPS
#include <clasp/cli/clasp_cli_options.inl>
            }
#undef GET_FUN
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
int ClaspCliConfig::getValue(KeyType key, char* buffer, std::size_t bufSize) const {
    std::string temp;
    int         ret = getValue(key, temp);
    if (ret <= 0) {
        return ret;
    }
    if (buffer && bufSize) {
        std::size_t n = temp.length() >= bufSize ? bufSize - 1 : temp.length();
        std::memcpy(buffer, temp.c_str(), n * sizeof(char));
        buffer[n] = 0;
    }
    return static_cast<int>(temp.length());
}
std::string ClaspCliConfig::getValue(const char* path) const {
    std::string temp;
    POTASSCO_CHECK_PRE(getValue(getKey(key_root, path), temp) >= 0, "Invalid key: '%s'", path);
    return temp;
}
bool ClaspCliConfig::hasValue(const char* path) const {
    int nVals;
    return getKeyInfo(getKey(key_root, path), nullptr, nullptr, nullptr, &nVals) == 1 && nVals > 0;
}

int ClaspCliConfig::setValue(KeyType key, const char* value) {
    int16_t id = decodeKey(key);
    if (not isLeafId(id)) {
        return -1;
    }
    try {
        uint8_t mode = decodeMode(key);
        validate_    = true;
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

bool ClaspCliConfig::setValue(const char* path, const char* value) {
    int ret = setValue(getKey(key_root, path), value);
    POTASSCO_CHECK_PRE(ret >= 0, (ret == -1 ? "Invalid or incomplete key: '%s'" : "Value error in key: '%s'"), path);
    return ret != 0;
}

int ClaspCliConfig::setOption(int option, uint8_t setMode, uint32_t sId, const char* _val_) {
    if (not _val_ || (isTester(setMode) && not isTesterOption(option)) ||
        (isSolver(setMode) && not isSolverOption(option))) {
        return setMode & mode_relaxed ? 1 : -1;
    }
    BasicSatConfig* base   = active(this, setMode);
    SolverParams*   solver = isSolverOption(option) ? &base->addSolver(sId) : nullptr;
    SolveParams*    search = isSolverOption(option) ? &base->addSearch(sId) : nullptr;
    // action & helper macros used in set
    using Potassco::opt;
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

int ClaspCliConfig::setAppOpt(int o, uint8_t mode, const char* val) {
    if (o == meta_config) {
        std::pair<ConfigKey, uint32_t> defC(config_default, INT_MAX);
        if (ok(Potassco::stringTo(val, defC))) {
            active(this, mode)->cliConfig = static_cast<uint8_t>(defC.first);
        }
        else {
            POTASSCO_CHECK(std::ifstream(val).is_open(), std::errc::no_such_file_or_directory,
                           "Could not open config file '%s'", val);
            config_[isTester(mode)]       = val;
            active(this, mode)->cliConfig = config_max_value + isTester(mode);
        }
        return Clasp::saturate_cast<int>(defC.second);
    }
    if (o == meta_tester && not isTester(mode)) {
        addTesterConfig();
        ParsedOpts ex;
        bool       ret = setConfig("<tester>", val, mode_tester | mode_meta, 0, ParsedOpts(), &ex);
        return ret && finalizeAppConfig(mode_tester, finalizeParsed(mode_tester, ex, ex), ProblemType::asp, true);
    }
    return -1; // invalid option
}
bool ClaspCliConfig::setAppDefaults(ConfigKey config, uint8_t mode, const ParsedOpts& seen, ProblemType t) {
    std::string mem;
    if (t != ProblemType::asp && not seen.contains(getOptionName(opt_sat_prepro, mem))) {
        POTASSCO_CHECK_PRE(setOption(opt_sat_prepro, mode, 0, "2,iter=20,occ=25,time=120"));
    }
    if (not isTester(mode) && config == config_many && t == ProblemType::asp) {
        POTASSCO_CHECK_PRE(seen.contains(getOptionName(opt_eq, mem)) || setOption(opt_eq, mode, 0, "3"));
        POTASSCO_CHECK_PRE(seen.contains(getOptionName(opt_trans_ext, mem)) ||
                           setOption(opt_trans_ext, mode, 0, "dynamic"));
    }
    if (config != config_nolearn && active(this, mode)->solver(0).search == SolverParams::no_learning) {
        POTASSCO_CHECK_PRE(setConfig(getConfig(config_nolearn), mode | mode_relaxed, 0, seen, nullptr));
    }
    return true;
}

bool ClaspCliConfig::setConfig(const char* name, const char* args, uint8_t mode, uint32_t sId,
                               const ParsedOpts& exclude, ParsedOpts* out) {
    createOptions();
    ParseContext ctx(*this, name, &exclude, mode, sId, out);
    parseCommandString(args, ctx, Potassco::ProgramOptions::command_line_allow_flag_value);
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

const std::string& ClaspCliConfig::getOptionName(int o, std::string& mem) const {
    POTASSCO_ASSERT(isOption(o));
    if (opts_.get()) {
        return (opts_->begin() + o)->get()->name();
    }
    keyToCliName(mem, getNode(static_cast<int16_t>(o)).name, "");
    return mem;
}

const ClaspCliConfig::ParsedOpts& ClaspCliConfig::finalizeParsed(uint8_t mode, const ParsedOpts& parsed,
                                                                 ParsedOpts& exclude) const {
    const ParsedOpts* ret = &parsed;
    std::string       mem;
    if (active(this, mode)->search(0).reduce.fReduce() == 0 && parsed.contains(getOptionName(opt_deletion, mem))) {
        if (ret != &exclude) {
            exclude = parsed;
        }
        exclude.add(getOptionName(opt_del_cfl, mem));
        exclude.add(getOptionName(opt_del_max, mem));
        exclude.add(getOptionName(opt_del_grow, mem));
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

bool ClaspCliConfig::setAppConfig(const std::string& args, ProblemType t) {
    Potassco::ProgramOptions::ParsedOptions exclude;
    reset();
    return setConfig("setConfig", args.c_str(), mode_meta, 0, exclude, &exclude) && assignDefaults(exclude) &&
           finalize(exclude, t, true);
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
