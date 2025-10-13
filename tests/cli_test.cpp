//
// Copyright (c) 2014-present Benjamin Kaufmann
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
#include "lpcompare.h"

#include <clasp/clasp_facade.h>
#include <clasp/cli/clasp_options.h>
#include <clasp/cli/clasp_output.h>
#include <clasp/lookahead.h>
#include <clasp/unfounded_check.h>

#include <potassco/program_opts/errors.h>
#include <potassco/program_opts/program_options.h>

#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers_exception.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#if __has_include(<unistd.h>)
#include <unistd.h>
#endif

#include <cstdio>
#include <fstream>

namespace Clasp {
static bool operator==(const ScheduleStrategy& lhs, const ScheduleStrategy& rhs) {
    return lhs.type == rhs.type && lhs.base == rhs.base && lhs.len == rhs.len && lhs.grow == rhs.grow;
}
namespace Cli::Test {
namespace {
struct OptionTest {
    void traverseKey(std::vector<std::string>& keys, ClaspCliConfig::KeyType k, std::string accu) const {
        if (k == ClaspCliConfig::key_invalid) {
            throw std::runtime_error("Invalid key");
        }
        if (ClaspCliConfig::isLeafKey(k)) {
            keys.push_back(accu);
        }
        else {
            if (not accu.empty()) {
                accu += '.';
            }
            auto pop = accu.size();
            auto i   = 0u;
            for (std::string_view x{}; not(x = config.getSubkey(k, i)).empty(); ++i, accu.resize(pop)) {
                accu += x;
                traverseKey(keys, config.getKey(k, x), accu);
            }
        }
    }
    [[nodiscard]] bool isValidOption(std::string_view k) const {
        return ClaspCliConfig::isLeafKey(config.getKey(ClaspCliConfig::key_root, k));
    }
    [[nodiscard]] bool hasOption(std::string_view o, const std::vector<std::string>& keys, bool tester) const {
        return contains(keys, o) || (tester && not isValidOption(o));
    }
    ClaspCliConfig config;
    std::string    val;
};

class TmpFile {
public:
    TmpFile() : TmpFile(false) {}
    ~TmpFile() { unlink(); }
    TmpFile(TmpFile&&) = delete;
    static auto named() -> TmpFile { return TmpFile(true); }

    [[nodiscard]] auto* rep() const { return file_; }

    static constexpr auto complete = 1u;
    static unsigned       lineOff(int n) { return static_cast<unsigned>(n) << 1u; }

    [[nodiscard]] bool matchOutput(std::string_view what, unsigned options = 0) {
        auto out     = readAll();
        auto lineOff = static_cast<std::size_t>(static_cast<int>(options >> 1u));
        auto outView = std::string_view{out};
        while (not outView.empty() && not what.empty()) {
            auto ep       = what.find('\n');
            auto nextLine = what.substr(0, ep + (ep != std::string_view::npos));
            auto source   = outView;
            if (not matchImpl(source, nextLine.substr(std::min(nextLine.size(), lineOff)))) {
                break;
            }
            outView = source;
            what.remove_prefix(nextLine.size());
        }
        if (not what.empty()) {
            UNSCOPED_INFO("needle: " << what << "  context: " << outView);
            return false;
        }
        if (Potassco::test_mask(options, complete) && not outView.empty()) {
            UNSCOPED_INFO("extra: " << outView);
            return false;
        }
        return true;
    }

    void discardOutput() { std::ignore = readAll(); }

    [[nodiscard]] auto name() const -> const char* { return name_.c_str(); }
    void               close() {
        if (auto* f = std::exchange(file_, nullptr); f) {
            fclose(f);
        }
    }
    void unlink() {
        close();
        if (not name_.empty()) {
            std::remove(name_.c_str());
            name_.clear();
        }
    }

    friend TmpFile& operator<<(TmpFile& ts, std::string_view what) {
        POTASSCO_CHECK(ts.file_, std::errc::bad_file_descriptor, "file not open");
        std::fwrite(what.data(), 1, what.size(), ts.file_);
        return ts;
    }

private:
    POTASSCO_WARNING_PUSH()
    POTASSCO_WARNING_IGNORE_MSVC(4996)
    POTASSCO_WARNING_IGNORE_CLANG("-Wdeprecated-declarations")
    explicit TmpFile(bool requireName) : file_(nullptr) {
        if (not requireName) {
            file_ = tmpfile();
        }
        else {
            file_ = makeTemp(name_);
        }
        POTASSCO_CHECK(file_, std::errc::no_such_file_or_directory, "Failed to create temporary file");
    }
    template <typename T = char>
    static FILE* makeTemp(std::string& nameOut) {
        FILE* res = nullptr;
        if constexpr (requires { mkstemp(std::declval<T*>()); }) {
            T name[16] = "cli_test.XXXXXX";
            if (auto fd = mkstemp(name); fd >= 0) {
                nameOut = name;
                res     = fdopen(fd, "w+");
            }
        }
        else {
            T name[L_tmpnam];
            for (int i = 0; not res && i < 10 && std::tmpnam(name); ++i) {
                nameOut = name;
                res     = std::fopen(name, "w+x");
            }
        }
        return res;
    }
    POTASSCO_WARNING_POP()
    [[nodiscard]] std::string readAll() {
        fseek(file_, pos_, SEEK_SET);
        std::string           ret;
        static constexpr auto block_size = 128;
        for (auto off = static_cast<std::size_t>(0);; off += block_size) {
            ret.resize(ret.size() + block_size);
            if (auto c = fread(ret.data() + off, 1, block_size, file_); c != block_size) {
                POTASSCO_CHECK(feof(file_), std::errc::bad_file_descriptor, "failed to read from file");
                ret.resize(ret.size() - (block_size - c));
                pos_ = ftell(file_);
                return ret;
            }
        }
    }
    [[nodiscard]] static bool matchImpl(std::string_view& in, std::string_view what) {
        std::size_t wp = 0;
        while (not in.empty() && wp < what.size()) {
            char lhs = in.front();
            char rhs = what[wp];
            if (std::isdigit(static_cast<unsigned char>(lhs)) && rhs == 'T' &&
                what.substr(wp + 1).starts_with(".TTTs")) {
                auto next = in.substr(std::min(in.find_first_not_of("0123456789"), in.size()));
                if (next.starts_with('.')) {
                    next.remove_prefix(1);
                    in   = next.substr(std::min(next.find_first_not_of("0123456789"), next.size()));
                    wp  += 5;
                    rhs  = what[wp];
                }
                lhs = not in.empty() ? in.front() : '\0';
            }
            in.remove_prefix(lhs == rhs || wp == 0);
            if (lhs == rhs) {
                ++wp;
            }
            else {
                wp = 0;
            }
        }
        return wp == what.size();
    }
    std::string name_;
    FILE*       file_;
    long        pos_{0};
};

} // namespace

TEST_CASE("Cat Atom parsing and printing", "[cli]") {
    using CatAtom = TextOutput::CatAtom;
    using namespace std::literals;

    auto formatAtom = [](CatAtom& atom, const auto& val) {
        Potassco::BasicCharBuffer buffer;
        atom.formatTo(buffer, val);
        return std::string(buffer.view());
    };
    SECTION("empty") {
        CatAtom atom;
        REQUIRE_FALSE(atom.hasAtom());
        REQUIRE_FALSE(atom.hasVar());
        REQUIRE(formatAtom(atom, "foo"sv) == "foo"sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "10"sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-10"sv);
    }
    SECTION("minimal") {
        auto atom = CatAtom::fromString("%0");
        REQUIRE_FALSE(atom.hasAtom());
        REQUIRE_FALSE(atom.hasVar());
        REQUIRE(formatAtom(atom, "foo"sv) == "foo"sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "10"sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-10"sv);
    }
    SECTION("comp09") {
        auto atom = CatAtom::fromString("%0.");
        REQUIRE(atom.hasAtom());
        REQUIRE(atom.hasVar());
        REQUIRE(formatAtom(atom, "foo"sv) == "foo."sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "10."sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-10."sv);
    }
    SECTION("constant") {
        auto atom = CatAtom::fromString("x1");
        REQUIRE(atom.hasAtom());
        REQUIRE(atom.hasVar());
        REQUIRE(formatAtom(atom, "foo"sv) == "x1"sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "x1"sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-x1"sv);
    }
    SECTION("prefix") {
        auto atom = CatAtom::fromString("pre%0");
        REQUIRE(atom.hasAtom());
        REQUIRE(atom.hasVar());
        REQUIRE(formatAtom(atom, "foo"sv) == "prefoo"sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "pre10"sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-pre10"sv);
    }
    SECTION("postfix") {
        auto atom = CatAtom::fromString("%0post");
        REQUIRE(atom.hasAtom());
        REQUIRE(atom.hasVar());
        REQUIRE(formatAtom(atom, "foo"sv) == "foopost"sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "10post"sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-10post"sv);
    }
    SECTION("predicate") {
        auto atom = CatAtom::fromString("x(%0)");
        REQUIRE(atom.hasAtom());
        REQUIRE(atom.hasVar());
        REQUIRE(formatAtom(atom, "foo"sv) == "x(foo)"sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "x(10)"sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-x(10)"sv);
    }
    SECTION("complex") {
        auto atom = CatAtom::fromString("foo(%%0,%0,bla)");
        REQUIRE(atom.hasAtom());
        REQUIRE(atom.hasVar());
        REQUIRE(formatAtom(atom, "atom"sv) == "foo(%0,atom,bla)"sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "foo(%0,10,bla)"sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-foo(%0,10,bla)"sv);
    }
    SECTION("atom-only") {
        auto atom = CatAtom::fromString("_atom(%0):");
        REQUIRE(atom.hasAtom());
        REQUIRE_FALSE(atom.hasVar());
        REQUIRE(formatAtom(atom, "atom"sv) == "_atom(atom)"sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "10"sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-10"sv);
    }
    SECTION("var-only") {
        auto atom = CatAtom::fromString(":_x(%0)");
        REQUIRE_FALSE(atom.hasAtom());
        REQUIRE(atom.hasVar());
        REQUIRE(formatAtom(atom, "atom"sv) == "atom"sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "_x(10)"sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-_x(10)"sv);
    }
    SECTION("both") {
        auto atom = CatAtom::fromString("atom(%0):var(%0)");
        REQUIRE(atom.hasAtom());
        REQUIRE(atom.hasVar());
        REQUIRE(formatAtom(atom, "foo"sv) == "atom(foo)"sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "var(10)"sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-var(10)"sv);
    }
    SECTION("escape") {
        auto atom = CatAtom::fromString(R"(foo(%0%%0%s)\:bar)");
        REQUIRE(atom.hasAtom());
        REQUIRE(atom.hasVar());
        REQUIRE(formatAtom(atom, "atom"sv) == "foo(atom%0%s):bar"sv);
        REQUIRE(formatAtom(atom, posLit(10)) == "foo(10%0%s):bar"sv);
        REQUIRE(formatAtom(atom, negLit(10)) == "-foo(10%0%s):bar"sv);
    }

    SECTION("valid") {
        CHECK_NOTHROW(CatAtom::fromString("%"));
        CHECK_NOTHROW(CatAtom::fromString("foo%"));
        CHECK_NOTHROW(CatAtom::fromString("foo%d"));
        CHECK_NOTHROW(CatAtom::fromString("foo%s"));
        CHECK_NOTHROW(CatAtom::fromString("foo%%0%0"));
        CHECK_NOTHROW(CatAtom::fromString("foo%%%0"));
        CHECK_NOTHROW(CatAtom::fromString("atom:var:"));
    }
    SECTION("errors") {
        auto messageContains = [](const std::string& s) {
            return Catch::Matchers::MessageMatches(Catch::Matchers::ContainsSubstring(s));
        };
        CHECK_THROWS_MATCHES(CatAtom::fromString("foo\nbar"), std::invalid_argument,
                             messageContains("new line not allowed"));
        CHECK_THROWS_MATCHES(CatAtom::fromString("foo(%0,%0)"), std::invalid_argument,
                             messageContains("too many arguments"));
        CHECK_THROWS_MATCHES(CatAtom::fromString("foo(%%%0,%0)"), std::invalid_argument,
                             messageContains("too many arguments"));
        CHECK_THROWS_MATCHES(CatAtom::fromString("atom:var:extra"), std::invalid_argument,
                             messageContains("too many separators"));
    }
}
TEST_CASE_METHOD(OptionTest, "Cli option parsing", "[cli]") {
    SECTION("test dom-mod option") {
        REQUIRE("no" == config.getValue("solver.dom_mod"));
        REQUIRE(config.setValue("solver.dom_mod", "1"));
        REQUIRE("level" == config.getValue("solver.dom_mod"));
        REQUIRE(config.setValue("solver.dom_mod", "true"));
        REQUIRE("level,pos" == config.getValue("solver.dom_mod"));

        REQUIRE(config.setValue("solver.dom_mod", "false,scc,opt"));
        REQUIRE("level,neg,scc,opt" == config.getValue("solver.dom_mod"));

        REQUIRE_FALSE(config.setValue("solver.dom_mod", "0,scc"));
        REQUIRE(config.setValue("solver.dom_mod", "0"));
        REQUIRE("no" == config.getValue("solver.dom_mod"));
    }
    SECTION("test stats option") {
        REQUIRE("0" == config.getValue("stats"));
        SECTION("success") {
            using Spec = std::pair<std::string, std::string>;
            auto ok    = GENERATE(Spec{"1", "1"}, Spec{"no", "0"}, Spec{"2,1", "2,1"});
            CAPTURE(ok.first);
            REQUIRE(config.setValue("stats", ok.first));
            REQUIRE(config.getValue("stats") == ok.second);
        }
        SECTION("error") {
            auto err = GENERATE("0,", "3", "1,3", "0,2", "0,0");
            CAPTURE(err);
            REQUIRE_FALSE(config.setValue("stats", err));
        }
    }
    SECTION("test project option") {
        REQUIRE("no" == config.getValue("solve.project"));
        REQUIRE(config.solve.project == 0u);
        REQUIRE(config.setValue("solve.project", "auto,0"));
        REQUIRE("auto,0" == config.getValue("solve.project"));
        REQUIRE(config.solve.project);
        REQUIRE(config.setValue("solve.project", "project,2"));
        REQUIRE("project,2" == config.getValue("solve.project"));
        REQUIRE(config.solve.project == 5);

        REQUIRE(config.setValue("solve.project", "1"));
        REQUIRE("auto,0" == config.getValue("solve.project"));
        REQUIRE(config.solve.project == 1);

        REQUIRE(config.setValue("solve.project", "auto,2"));
        REQUIRE("auto,2" == config.getValue("solve.project"));
        REQUIRE(config.solve.project == 5);

        REQUIRE(config.setValue("solve.project", "4"));
        REQUIRE("auto,2" == config.getValue("solve.project"));
        REQUIRE(config.solve.project == 5);

        REQUIRE(config.setValue("solve.project", "6"));
        REQUIRE("auto,3" == config.getValue("solve.project"));
        REQUIRE(config.solve.project == 7);

        REQUIRE(config.setValue("solve.project", "7"));
        REQUIRE("auto,3" == config.getValue("solve.project"));
        REQUIRE(config.solve.project == 7);

        REQUIRE(config.setValue("solve.project", "0"));
        REQUIRE("no" == config.getValue("solve.project"));
        REQUIRE(config.solve.project == 0u);
    }
    SECTION("test lookahead option") {
        auto lookahead = config.getKey(ClaspCliConfig::key_root, "solver.lookahead");
        REQUIRE(config.setValue(lookahead, "no,0") == 0);
        REQUIRE(config.setValue(lookahead, "body,0") > 0);
        REQUIRE((config.solver(0).lookType == VarType::body && config.solver(0).lookOps == 0));
        REQUIRE(config.setValue(lookahead, "hybrid,umax") > 0);
        REQUIRE((config.solver(0).lookType == VarType::hybrid && config.solver(0).lookOps == 0));
        REQUIRE(config.setValue(lookahead, "no") > 0);
        REQUIRE((not Lookahead::isType(config.solver(0).lookType) && config.solver(0).lookOps == 0));
    }
    SECTION("test heuristic option") {
        auto heuristic = config.getKey(ClaspCliConfig::key_root, "solver.heuristic");
        REQUIRE(0 == config.setValue(heuristic, "vsidsS"));
        REQUIRE(1 == config.setValue(heuristic, "vsids"));
        REQUIRE((config.solver(0).heuId == HeuristicType::vsids && config.solver(0).heuristic.param == 0));
        REQUIRE(1 == config.setValue(heuristic, "vmtf,12"));
        REQUIRE((config.solver(0).heuId == HeuristicType::vmtf && config.solver(0).heuristic.param == 12));
        REQUIRE(1 == config.setValue(heuristic, "Berkmin"));
        REQUIRE((config.solver(0).heuId == HeuristicType::berkmin && config.solver(0).heuristic.param == 0));

        heuristic = config.getKey(ClaspCliConfig::key_solver, "score_other");
        REQUIRE(1 == config.setValue(heuristic, "all"));
        REQUIRE(config.solver(0).heuristic.other == HeuParams::other_all);
    }
    SECTION("test strengthen option") {
        auto strengthen = config.getKey(ClaspCliConfig::key_root, "solver.strengthen");
        REQUIRE(1 == config.setValue(strengthen, "no"));
        REQUIRE(config.solver(0).ccMinAntes == SolverStrategies::no_antes);
        REQUIRE(0 == config.setValue(strengthen, "no,1"));

        REQUIRE(1 == config.setValue(strengthen, "recursive"));
        REQUIRE(config.solver(0).ccMinAntes == SolverStrategies::all_antes);
        REQUIRE(config.solver(0).ccMinRec == SolverStrategies::cc_recursive);

        REQUIRE(1 == config.setValue(strengthen, "local,binary"));
        REQUIRE(config.solver(0).ccMinAntes == SolverStrategies::binary_antes);
        REQUIRE(config.solver(0).ccMinRec == SolverStrategies::cc_local);

        REQUIRE(0 == config.setValue(strengthen, "recs"));
    }
    SECTION("test contraction option") {
        auto contraction = config.getKey(ClaspCliConfig::key_root, "solver.contraction");
        REQUIRE(1 == config.setValue(contraction, "no"));
        REQUIRE(1 == config.setValue(contraction, "0"));

        REQUIRE(0 == config.setValue(contraction, "0,allUip"));
        REQUIRE(1 == config.setValue(contraction, "1,decisionSeq"));
    }
    SECTION("test loop option") {
        auto loops = config.getKey(ClaspCliConfig::key_root, "solver.loops");
        REQUIRE(1 == config.setValue(loops, "no"));
        REQUIRE(config.solver(0).loopRep == DefaultUnfoundedCheck::only_reason);
        loops = config.getKey(ClaspCliConfig::key_root, "solver.1.loops");
        REQUIRE(1 == config.setValue(loops, "shared"));
        REQUIRE(config.solver(1).loopRep == DefaultUnfoundedCheck::shared_reason);
    }
    SECTION("test deletion option") {
        auto deletion = config.getKey(ClaspCliConfig::key_root, "solver.deletion");
        REQUIRE(1 == config.setValue(deletion, "0"));
        REQUIRE(config.search(0).reduce.strategy.fReduce == 0);
        REQUIRE(0 == config.setValue(deletion, "0,10"));
        REQUIRE(1 == config.setValue(deletion, "ipSort"));
        REQUIRE(config.search(0).reduce.strategy.algo == ReduceStrategy::reduce_sort);
        REQUIRE(config.search(0).reduce.strategy.fReduce == 75);
        REQUIRE(config.search(0).reduce.strategy.score == 0);

        REQUIRE(1 == config.setValue(deletion, "sort,50"));
        REQUIRE(config.search(0).reduce.strategy.algo == ReduceStrategy::reduce_stable);
        REQUIRE(config.search(0).reduce.strategy.fReduce == 50);
        REQUIRE(config.search(0).reduce.strategy.score == 0);

        REQUIRE(1 == config.setValue(deletion, "basic,90,lbd"));
        REQUIRE(config.search(0).reduce.strategy.algo == ReduceStrategy::reduce_linear);
        REQUIRE(config.search(0).reduce.strategy.fReduce == 90);
        REQUIRE(config.search(0).reduce.strategy.score == 1);

        REQUIRE(0 == config.setValue(deletion, "basic,102"));
    }
    SECTION("test share option") {
        auto share = config.getKey(ClaspCliConfig::key_root, "share");
        REQUIRE(1 == config.setValue(share, "no"));
        REQUIRE(config.shareMode == ContextParams::share_no);

        REQUIRE(1 == config.setValue(share, "problem"));
        REQUIRE(config.shareMode == ContextParams::share_problem);

        REQUIRE(1 == config.setValue(share, "LEARNT"));
        REQUIRE(config.shareMode == ContextParams::share_learnt);
    }
    SECTION("test short simp option") {
        auto key = config.getKey(ClaspCliConfig::key_root, "short_simp_mode");
        REQUIRE(config.getValue(key, val) == 2);
        REQUIRE(val == "no");

        for (auto [x, y] : {std::pair{ContextParams::simp_learnt, "learnt"}, std::pair{ContextParams::simp_all, "all"},
                            std::pair{ContextParams::simp_no, "no"}}) {
            CAPTURE(y);
            REQUIRE(1 == config.setValue(key, y));
            REQUIRE(config.shortSimp == x);
            config.getValue(key, val);
            REQUIRE(val == y);
        }
    }
    SECTION("test trans-ext option") {
        auto tr = config.getKey(ClaspCliConfig::key_root, "asp.trans_ext");
        REQUIRE(1 == config.setValue(tr, "no"));
        REQUIRE(config.asp.erMode == Asp::LogicProgram::mode_native);
        REQUIRE(1 == config.setValue(tr, "scc"));
        REQUIRE(config.asp.erMode == Asp::LogicProgram::mode_transform_scc);
        tr = config.getKey(ClaspCliConfig::key_root, "tester.asp.trans_ext");
        REQUIRE(ClaspCliConfig::key_invalid == tr);
        REQUIRE(config.setValue(tr, "scc") == -1);
        REQUIRE_THROWS_AS(config.setValue("tester.asp.trans_ext", "scc"), std::logic_error);
    }
    SECTION("test sort-atom option") {
        auto tr = config.getKey(ClaspCliConfig::key_root, "asp.sort_atoms");
        REQUIRE(1 == config.setValue(tr, "no"));
        REQUIRE(config.asp.sortAtom == Asp::LogicProgram::sort_native);
        REQUIRE(1 == config.setValue(tr, "natural"));
        REQUIRE(config.asp.sortAtom == Asp::LogicProgram::sort_natural);
        REQUIRE(config.getValue("asp.sort_atoms") == "natural");
        REQUIRE(1 == config.setValue(tr, "arity"));
        REQUIRE(config.asp.sortAtom == Asp::LogicProgram::sort_arity);
        REQUIRE(1 == config.setValue(tr, "full"));
        REQUIRE(config.asp.sortAtom == Asp::LogicProgram::sort_arity_natual);
        REQUIRE(config.getValue("asp.sort_atoms") == "full");
    }
    SECTION("test enum-mode option") {
        auto        eMode = config.getKey(ClaspCliConfig::key_root, "solve.enum_mode");
        std::string help;
        REQUIRE(config.getKeyInfo(eMode, nullptr, nullptr, &help, nullptr) == 1);
        REQUIRE(help.find("[%D]") == std::string::npos);
        CAPTURE(help.substr(0, help.find('\n')));
        REQUIRE(help.starts_with("Configure enumeration algorithm [auto]"));
        REQUIRE(1 == config.setValue(eMode, "brave"));
        REQUIRE(config.solve.enumMode == EnumOptions::enum_brave);
        REQUIRE(0 == config.setValue(eMode, "consequences"));

        REQUIRE(config.setValue("solve.opt_mode", "ignore"));
        REQUIRE(config.solve.optMode == MinimizeMode::ignore);

        REQUIRE_THROWS_AS(config.setValue("tester.solve.enum_mode", "brave"), std::logic_error);
    }
    SECTION("test opt-strategy option") {
        auto oStrat = config.getKey(ClaspCliConfig::key_root, "solver.opt_strategy");
        REQUIRE(config.getValue("solver.opt_strategy") == "bb,lin");
        REQUIRE(1 == config.setValue(oStrat, "bb"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "bb,lin"));
        REQUIRE(1 == config.setValue(oStrat, "bb,INC"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "bb,inc"));
        REQUIRE((config.solver(0).opt.type == 0u && config.solver(0).opt.algo == OptParams::bb_inc));
        REQUIRE(0 == config.setValue(oStrat, "bb,foo"));

        REQUIRE(1 == config.setValue(oStrat, "usc"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,oll"));
        REQUIRE((config.solver(0).opt.type == OptParams::type_usc));
        REQUIRE(1 == config.setValue(oStrat, "usc,k"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,k,0"));
        REQUIRE(config.solver(0).opt.type == OptParams::type_usc);
        REQUIRE((config.solver(0).opt.algo == OptParams::usc_k && config.solver(0).opt.kLim == 0));

        REQUIRE(1 == config.setValue(oStrat, "usc,k,4"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,k,4"));
        REQUIRE(config.solver(0).opt.type == OptParams::type_usc);
        REQUIRE((config.solver(0).opt.algo == OptParams::usc_k && config.solver(0).opt.kLim == 4));

        REQUIRE(0 == config.setValue(oStrat, "usc,foo"));

        REQUIRE(1 == config.setValue(oStrat, "usc,oll,3"));
        REQUIRE(config.solver(0).opt.opts == 3u);
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,oll,disjoint,succinct"));
        REQUIRE(1 == config.setValue(oStrat, "usc,oll,stratify,disjoint"));
        REQUIRE(config.solver(0).opt.opts == uint32_t(OptParams::usc_disjoint | OptParams::usc_stratify));
        REQUIRE(1 == config.setValue(oStrat, "usc,oll,0"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,oll"));
        REQUIRE(0 == config.setValue(oStrat, "usc,oll,1,2"));

        auto uShrink = config.getKey(ClaspCliConfig::key_root, "solver.opt_usc_shrink");
        REQUIRE((config.getValue(uShrink, val) > 0 && val == "no"));
        REQUIRE(1 == config.setValue(uShrink, "exp"));
        REQUIRE((config.getValue(uShrink, val) > 0 && val == "exp,10"));
        REQUIRE(1 == config.setValue(uShrink, "bin,12"));
        REQUIRE((config.getValue(uShrink, val) > 0 && val == "bin,12"));
    }
    SECTION("test opt-strategy legacy option") {
        auto oStrat = config.getKey(ClaspCliConfig::key_root, "solver.opt_strategy");
        // clasp-3.0:
        REQUIRE(1 == config.setValue(oStrat, "1"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "bb,hier"));
        REQUIRE(1 == config.setValue(oStrat, "5"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,oll,disjoint"));
        // clasp-3.1
        REQUIRE(1 == config.setValue(oStrat, "bb,1"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "bb,hier"));
        REQUIRE(1 == config.setValue(oStrat, "usc,7"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,pmres,disjoint,succinct"));
        // clasp-3.2:
        REQUIRE(1 == config.setValue(oStrat, "usc,15"));
        REQUIRE((config.getValue(oStrat, val) > 0 && val == "usc,pmres,disjoint,succinct,stratify"));
    }
    SECTION("test solve-limit option") {
        auto limit = config.getKey(ClaspCliConfig::key_root, "solve.solve_limit");
        REQUIRE(1 == config.setValue(limit, "0"));
        REQUIRE(config.getValue(limit, val) > 0);
        REQUIRE("0,umax" == val);
        REQUIRE(config.solve.limit.conflicts == 0);
        REQUIRE(config.solve.limit.enabled());

        REQUIRE(1 == config.setValue(limit, "no"));
        REQUIRE(config.getValue(limit, val) > 0);
        REQUIRE(config.solve.limit.conflicts == UINT64_MAX);
        REQUIRE("umax,umax" == val);
        REQUIRE_FALSE(config.solve.limit.enabled());

        SECTION("success") {
            using Spec = std::pair<std::string, std::string>;
            auto ok    = GENERATE(Spec{"1", "1,umax"}, Spec{"no", "umax,umax"}, Spec{"10,20", "10,20"});
            CAPTURE(ok.first);
            REQUIRE(1 == config.setValue(limit, ok.first));
            REQUIRE(config.getValue(limit, val) > 0);
            REQUIRE(val == ok.second);
        }
        SECTION("error") {
            auto err = GENERATE("0,", "no,1", "no,0", "no,no");
            CAPTURE(err);
            REQUIRE_FALSE(config.setValue("solve.solve_limit", err));
        }
    }

    SECTION("test opt-mode option") {
        REQUIRE(config.getValue("solve.opt_mode") == "opt");
        REQUIRE(config.setValue("solve.opt_mode", "optN"));
        REQUIRE(config.getValue("solve.opt_mode") == "optN");

        REQUIRE(config.setValue("solve.opt_mode", "enum,100"));
        REQUIRE(config.getValue("solve.opt_mode") == "enum,100");
        REQUIRE(config.setValue("solve.opt_mode", "opt,50,20"));
        REQUIRE(config.getValue("solve.opt_mode") == "opt,50,20");

        REQUIRE(config.setValue("solve.opt_mode", "ignore"));
        REQUIRE(config.getValue("solve.opt_mode") == "ignore");

        REQUIRE(config.setValue("solve.opt_mode", "opt,50,20"));
        REQUIRE_FALSE(config.setValue("solve.opt_mode", "enum,a,b"));
        REQUIRE(config.getValue("solve.opt_mode") == "opt,50,20");
    }

    SECTION("test dynamic restart option") {
        REQUIRE(config.getValue("solver.restarts") == "x,100,1.5,0");
        REQUIRE_FALSE(config.setValue("solver.restarts", "D,100"));
        REQUIRE_FALSE(config.setValue("solver.restarts", "D,0"));

        REQUIRE(config.setValue("solver.restarts", "D,50,0.8"));
        REQUIRE(config.getValue("solver.restarts") == "d,50,0.8");

        REQUIRE(config.setValue("solver.restarts", "D,100,0.9,20"));
        REQUIRE(config.getValue("solver.restarts") == "d,100,0.9,20");
        REQUIRE(config.search(0).restart.rsSched.isDynamic());
        REQUIRE(config.search(0).restart.rsSched.lbdLim() == 20);

        REQUIRE(config.setValue("solver.restarts", "D,100,0.9,0,es,r"));
        REQUIRE(config.getValue("solver.restarts") == "d,100,0.9,0,es,r");
        const auto& rs = config.search(0).restart.rsSched;
        REQUIRE(rs.isDynamic());
        REQUIRE(rs.lbdLim() == 0);
        REQUIRE(rs.fastAvg() == MovingAvg::Type::avg_ema_smooth);
        REQUIRE(rs.keepAvg() == RestartSchedule::keep_restart);

        REQUIRE(config.setValue("solver.restarts", "D,100,0.9,255,ls,rb,e,1234"));
        REQUIRE(config.getValue("solver.restarts") == "d,100,0.9,255,ls,br,e,1234");
        REQUIRE(rs.isDynamic());
        REQUIRE(rs.lbdLim() == 255);
        REQUIRE(rs.fastAvg() == MovingAvg::Type::avg_ema_log_smooth);
        REQUIRE(rs.keepAvg() == RestartSchedule::keep_always);
        REQUIRE(rs.slowAvg() == MovingAvg::Type::avg_ema);
        REQUIRE(rs.slowWin() == 1234);

        REQUIRE_FALSE(config.setValue("solver.restarts", "D,100,0.9,255,ls,rb,e,1234,12"));

        REQUIRE(config.setValue("solver.restarts", "D,50,0.8,0,ls,es,10000"));
        REQUIRE(config.getValue("solver.restarts") == "d,50,0.8,0,ls,es,10000");
        REQUIRE(rs.isDynamic());
        REQUIRE(rs.lbdLim() == 0);
        REQUIRE(rs.fastAvg() == MovingAvg::Type::avg_ema_log_smooth);
        REQUIRE(rs.keepAvg() == RestartSchedule::keep_never);
        REQUIRE(rs.slowAvg() == MovingAvg::Type::avg_ema_smooth);
        REQUIRE(rs.slowWin() == 10000);
    }

    SECTION("test block restart option") {
        auto r = Potassco::initFpuPrecision();
        REQUIRE(r != UINT32_MAX);
        POTASSCO_SCOPE_EXIT({ Potassco::restoreFpuPrecision(r); });
        REQUIRE(config.getValue("solver.block_restarts") == "no");
        REQUIRE_FALSE(config.setValue("solver.block_restarts", "0,1.3"));

        REQUIRE(config.setValue("solver.block_restarts", "5000"));
        REQUIRE(config.getValue("solver.block_restarts") == "5000,1.4,10000,e");
        auto b = config.search(0).restart.block;
        REQUIRE(b.window == 5000);
        REQUIRE(b.first == 10000);
        REQUIRE(b.fscale == 140u);
        REQUIRE(b.scale() == 1.4);
        REQUIRE(b.avg == uint32_t(MovingAvg::Type::avg_ema));

        REQUIRE_FALSE(config.setValue("solver.block_restarts", "5000,0.8"));
        REQUIRE_FALSE(config.setValue("solver.block_restarts", "5000,5.1"));

        REQUIRE(config.setValue("solver.block_restarts", "10000,1.1,0,d"));
        b = config.search(0).restart.block;
        REQUIRE(b.window == 10000);
        REQUIRE(b.fscale == 110u);
        REQUIRE(b.scale() == 1.1);
        REQUIRE(b.first == 0);
        REQUIRE(b.avg == uint32_t(MovingAvg::Type::avg_sma));
    }

    SECTION("test visids progress option") {
        REQUIRE(config.getValue("solver.vsids_progress") == "no");

        REQUIRE(config.setValue("solver.vsids_progress", "80"));
        REQUIRE(config.getValue("solver.vsids_progress") == "80,1,5000");
        REQUIRE(config.solver(0).heuristic.decay.init == 80);
        REQUIRE(config.solver(0).heuristic.decay.bump == 1);
        REQUIRE(config.solver(0).heuristic.decay.freq == 5000);
        REQUIRE(config.setValue("solver.vsids_progress", "no"));
        REQUIRE(config.solver(0).heuristic.decay.init == 0);
        REQUIRE(config.solver(0).heuristic.decay.bump == 0);
        REQUIRE(config.solver(0).heuristic.decay.freq == 0);

        REQUIRE_FALSE(config.setValue("solver.vsids_progress", "80,101"));
    }

    SECTION("test partial-check option") {
        REQUIRE(config.getValue("solver.partial_check") == "0");
        REQUIRE_NOTHROW(config.setValue("solver.partial_check", "50"));
        REQUIRE(config.getValue("solver.partial_check") == "50,0");
        REQUIRE(config.search(0).fwdCheck.highPct == 50);
        REQUIRE(config.search(0).fwdCheck.highStep == 0);
        REQUIRE(config.search(0).fwdCheck.disable == 0);
        REQUIRE_NOTHROW(config.setValue("solver.partial_check", "no"));
        REQUIRE(config.search(0).fwdCheck.highPct == 0);
        REQUIRE(config.search(0).fwdCheck.highStep == 0);
        REQUIRE(config.search(0).fwdCheck.disable == 1);
        REQUIRE(config.getValue("solver.partial_check") == "no");

        REQUIRE_NOTHROW(config.setValue("solver.partial_check", "0"));
        REQUIRE(config.search(0).fwdCheck.highPct == 0);
        REQUIRE(config.search(0).fwdCheck.highStep == 0);
        REQUIRE(config.search(0).fwdCheck.disable == 0);
        REQUIRE(config.getValue("solver.partial_check") == "0");

        REQUIRE_NOTHROW(config.setValue("solver.partial_check", "10,20"));
        REQUIRE(config.search(0).fwdCheck.highPct == 10);
        REQUIRE(config.search(0).fwdCheck.highStep == 20);
        REQUIRE(config.search(0).fwdCheck.disable == 0);
        REQUIRE(config.getValue("solver.partial_check") == "10,20");
    }
    SECTION("test opt-stop option") {
        SumVec exp;
        REQUIRE(config.getValue("solve.opt_stop") == "no");
        REQUIRE(config.solve.optStop.empty());

        REQUIRE(config.setValue("solve.opt_stop", "10,17"));
        REQUIRE(config.getValue("solve.opt_stop") == "10,17");
        exp.push_back(10);
        exp.push_back(17);
        REQUIRE(config.solve.optStop == exp);

        REQUIRE(config.setValue("solve.opt_stop", "-4"));
        REQUIRE(config.getValue("solve.opt_stop") == "-4");
        exp.assign(1, -4);
        REQUIRE(config.solve.optStop == exp);

        REQUIRE(config.setValue("solve.opt_stop", "off"));
        REQUIRE(config.getValue("solve.opt_stop") == "no");
        REQUIRE(config.solve.optStop.empty());

        REQUIRE(config.setValue("solve.opt_stop", "0"));
        REQUIRE(config.getValue("solve.opt_stop") == "0");
        exp.assign(1, 0);
        REQUIRE(config.solve.optStop == exp);
    }
}

TEST_CASE_METHOD(OptionTest, "Cli options", "[cli]") {
    SECTION("Config ctor") {
        REQUIRE(config.numSolver() == 1);
        REQUIRE(config.testerConfig() == 0);
        REQUIRE_FALSE(config.solve.limit.enabled());
    }
    SECTION("test program options") {
        using namespace Potassco::ProgramOptions;
        OptionContext ctx;
        OptionGroup   ignore("basic");
        ctx.add(ignore);
        config.addOptions(ctx);
        const auto& cfgGrp = ctx.group("Clasp.Config Options");
        REQUIRE(cfgGrp.size() == 5);
        REQUIRE(cfgGrp.find("tester"));
        REQUIRE(cfgGrp.find('s'));
        REQUIRE(ctx.option("config", OptionContext::find_prefix).assign("frumpy"));
        REQUIRE(config.getValue("configuration") == "frumpy");
        REQUIRE(config.cliConfig == ConfigKey::config_frumpy);

        const auto& ctxGroup = ctx.group("Clasp.Context Options");
        REQUIRE(ctxGroup.size() == 4);
        REQUIRE(ctxGroup.find("sat-prepro"));
        REQUIRE(ctx.option("learn-explicit").assign(""));
        REQUIRE(config.getValue("learn_explicit") == "1");
        REQUIRE(config.context().shortMode == ContextParams::short_explicit);

        const auto& aspGroup = ctx.group("Clasp.ASP Options");
        REQUIRE(aspGroup.size() == 9);
        REQUIRE(aspGroup.find("eq"));
        REQUIRE(aspGroup.find("dlp-old-map"));
        REQUIRE(ctx.option("eq").assign("17"));
        REQUIRE(config.asp.iters == 17);

        const auto& solvingGroup = ctx.group("Clasp.Solving Options");
#if CLASP_HAS_THREADS
        REQUIRE(solvingGroup.size() == 10);
        REQUIRE(solvingGroup.find('t'));
#else
        REQUIRE(solvingGroup.size() == 6);
#endif
        REQUIRE(solvingGroup.find("opt-stop"));
        REQUIRE(solvingGroup.find('e'));
        REQUIRE(ctx.option("opt-mode").assign("optN"));
        REQUIRE(config.solve.optMode == MinimizeMode::enum_opt);

        const auto& searchGroup = ctx.group("Clasp.Search Options");
        REQUIRE(searchGroup.size() == 25);
        REQUIRE(searchGroup.find("opt-strategy"));
        REQUIRE(searchGroup.find("rand-prob"));
        REQUIRE(ctx.option("heuristic").assign("berkmin"));
        REQUIRE(config.solver(0).heuId == HeuristicType::berkmin);

        const auto& lookbackGroup = ctx.group("Clasp.Lookback Options");
        REQUIRE(lookbackGroup.size() == 23);
        REQUIRE(lookbackGroup.find("no-lookback"));
        REQUIRE(lookbackGroup.find('r'));
        REQUIRE(lookbackGroup.find('d'));
        REQUIRE(ctx.option("del-on-restart").assign("39"));
        REQUIRE(config.search(0).reduce.strategy.fRestart == 39);

        std::stringstream help;
        ctx.setActiveDescLevel(desc_level_e3);
        help << ctx;
        auto pCfg = help.str().find(cfgGrp.caption());
        auto pCtx = help.str().find(ctxGroup.caption());
        auto pAsp = help.str().find(aspGroup.caption());
        auto pSlv = help.str().find(solvingGroup.caption());
        auto pSrc = help.str().find(searchGroup.caption());
        auto pLbk = help.str().find(lookbackGroup.caption());
        CAPTURE(help.str());
        REQUIRE(pCfg < pCtx);
        REQUIRE(pCtx < pAsp);
        REQUIRE(pAsp < pSlv);
        REQUIRE(pSlv < pSrc);
        REQUIRE(pSrc < pLbk);
        REQUIRE(pLbk != std::string::npos);
    }
    SECTION("test get value") {
        SECTION("path") {
            auto v = config.getValue("configuration");
            REQUIRE(v == "auto");
        }
        SECTION("key and string") {
            auto k = config.getKey(ClaspCliConfig::key_root, "configuration");
            REQUIRE(k != ClaspCliConfig::key_invalid);

            std::string v;
            REQUIRE(config.getValue(k, v) == 4);
            REQUIRE(v == "auto");
            REQUIRE(config.getValue(k, v) == 4);
            REQUIRE(v == "auto");
        }
    }
    SECTION("test get values") {
        std::string out;
        REQUIRE(config.getValue(config.getKey(ClaspCliConfig::key_tester, "configuration"), out) == -1);
        config.setValue("configuration", "tweety");
        REQUIRE(config.getValue("configuration") == "tweety");

        REQUIRE(config.getValue("solver.heuristic") == "vsids,92");
        REQUIRE(config.getValue("solver.strengthen") == "recursive,all,yes");
        REQUIRE(config.getValue("solver.deletion") == "basic,50,activity");
        REQUIRE(config.getValue("solver.restarts") == "l,60");
        REQUIRE(config.getValue("solver.loops") == "shared");
        REQUIRE(config.getValue("solver.partial_check") == "0");

        REQUIRE(config.getValue("sat_prepro") == "no");

        std::vector<std::string> leafs;
        traverseKey(leafs, ClaspCliConfig::key_root, "");
        for (const auto& leaf : leafs) {
            if (config.hasValue(leaf)) {
                val = config.getValue(leaf);
                CAPTURE(leaf);
                CAPTURE(val);
                REQUIRE(config.setValue(leaf, val));
            }
        }
        config.setValue("sat_prepro", "2,20,25");
        REQUIRE(std::strcmp(config.getValue("sat_prepro").c_str(), "2,iter=20,occ=25,size=4000") == 0);
        config.reset();
        std::string x = config.getValue("solver.del_cfl");
        REQUIRE((x == "no" || x == "0"));
        x = config.getValue("solver.del_grow");

        REQUIRE(config.setValue("solver.del_grow", x));
        x = config.getValue("solve.opt_mode");
        REQUIRE(x == "opt");
        config.setValue("solve.opt_mode", "opt,122");
        REQUIRE(config.getValue("solve.opt_mode") == "opt,122");
        config.setValue("solver.del_init", "3,100,200");
        REQUIRE(config.getValue("solver.del_init") == "3,100,200");

        REQUIRE_FALSE(config.hasValue("tester.learn_explicit"));
        config.setValue("tester.learn_explicit", "1");
        REQUIRE(config.hasValue("tester.learn_explicit"));

        REQUIRE_THROWS_AS(config.getValue("enum"), std::logic_error);
        REQUIRE_THROWS_AS(config.getValue("tester.solve.opt_mode"), std::logic_error);
    }
    SECTION("test set value") {
        auto k = config.getKey(ClaspCliConfig::key_root, "configuration");
        REQUIRE(config.setValue(k, {}) == -2);
        REQUIRE(config.setValue(ClaspCliConfig::key_root, "1") == -1);
    }
    SECTION("test init from argv") {
        REQUIRE(config.solve.numSolver() == 1);
        REQUIRE(config.solve.numModels != 0);
        const char*            argv[] = {"-n0", "--save-progress=20", "--stats", "--tester=--config=frumpy"};
        std::span<const char*> args{argv};
        REQUIRE(args.size() == 4);
        config.setConfig(args, ProblemType::asp);
        REQUIRE(config.getValue("configuration") == "auto");
        REQUIRE(config.getValue("asp.eq") == "3");
        REQUIRE(config.getValue("asp.trans_ext") == "dynamic");
        REQUIRE(config.solve.numSolver() == 1);
        REQUIRE(config.numSolver() == 1);
        REQUIRE(config.solve.numModels == 0);
        REQUIRE(config.solver(0).saveProgress == 20);
        REQUIRE(config.testerConfig());
        REQUIRE(config.testerConfig()->numSolver() == 1);
        REQUIRE(config.getValue("tester.configuration") == "frumpy");
    }
    SECTION("test init error duplicate") {
        const char* argv[] = {"-n0", "--save-progress=20", "--stats", "--save-progress=30"};
        REQUIRE_THROWS_AS(config.setConfig(argv, ProblemType::asp), Potassco::ProgramOptions::ValueError);
    }
    SECTION("test init invalid tester option") {
        const char* argv[] = {"-n0", "--tester=--eq=3"};
        REQUIRE_THROWS_AS(config.setConfig(argv, ProblemType::asp), Potassco::ProgramOptions::ContextError);
    }
    SECTION("test init sat defaults") {
        SECTION("sat-pre is added") {
            const char* argv[] = {"--config=frumpy"};
            config.setConfig(argv, ProblemType::sat);
            REQUIRE(config.getValue("sat_prepro") == "2,iter=20,occ=25,time=120,size=4000");
        }
        SECTION("explicit sat-pre wins") {
            SECTION("with keys") {
                const char* argv[] = {"--config=frumpy --sat-pre=2,iter=40,occ=50,time=300"};
                config.setConfig(argv, ProblemType::sat);
            }
            SECTION("without keys") {
                const char* argv[] = {"--config=frumpy --sat-pre=2,40,50,300"};
                config.setConfig(argv, ProblemType::sat);
            }
            REQUIRE(config.getValue("sat_prepro") == "2,iter=40,occ=50,time=300,size=4000");
        }
    }
    SECTION("test init") {
        auto initGen  = config.getKey(ClaspCliConfig::key_root, "configuration");
        auto initTest = config.getKey(ClaspCliConfig::key_tester, "configuration");
        REQUIRE((ClaspCliConfig::isLeafKey(initGen) && ClaspCliConfig::isLeafKey(initTest) && initTest != initGen));
        int         nSub, nArr, nVal;
        std::string help;
        config.getKeyInfo(initGen, &nSub, &nArr, &help, &nVal);
        REQUIRE((nSub == 0 && nArr == -1 && nVal == 1 && help.find("frumpy") != std::string::npos));
        help = "";
        nArr = -2;
        config.getKeyInfo(initTest, &nSub, &nArr, &help, &nVal);
        REQUIRE((nSub == 0 && nArr == -1 && nVal == 0 && help.find("tweety") != std::string::npos));

        REQUIRE(config.setValue("configuration", "many"));
        REQUIRE(config.numSolver() > 1);
        REQUIRE(config.testerConfig() == 0);
        REQUIRE(config.setValue("tester.configuration", "tweety"));
        REQUIRE(config.testerConfig() != 0);
        REQUIRE(config.testerConfig()->hasConfig);
        config.getKeyInfo(initTest, nullptr, nullptr, nullptr, &nVal);
        REQUIRE(nVal == 1);

        REQUIRE(config.solver(1).id == 1);
        REQUIRE(config.solver(0).heuId == HeuristicType::vsids);
        config.setValue("configuration", "frumpy");
        REQUIRE(config.solver(0).heuId == HeuristicType::berkmin);
        REQUIRE(config.numSolver() == 1);
    }
    SECTION("test init from file") {
        auto temp = TmpFile::named();
        temp << "# A test config\n";
        temp << "[t0]: --models=0 --heuristic=Berkmin --restarts=x,100,1.5\n";
        temp.close();
        config.setValue("configuration", temp.name());

        REQUIRE(config.getValue("configuration") == temp.name());
        REQUIRE(config.solve.numModels == 0);
        REQUIRE(config.solver(0).heuId == HeuristicType::berkmin);
        REQUIRE(config.search(0).restart.rsSched == ScheduleStrategy::geom(100, 1.5));
        temp.unlink();
        REQUIRE(config.setValue(config.getKey(ClaspCliConfig::key_root, "configuration"), temp.name()) == -2);
    }
    SECTION("test init from file fails") {
        auto temp = TmpFile::named();
        temp << "# A test config\n";
        temp << "[t0]: --models=0 ";
        SECTION("on duplicate") {
            temp << "--heuristic=Berkmin --heuristic=Vsids\n";
            temp.close();
            CHECK_THROWS_AS(config.setValue("configuration", temp.name()), std::logic_error);
        }
        SECTION("on invalid") {
            temp << "--heuristic=Berlin\n";
            temp.close();
            CHECK_THROWS_AS(config.setValue("configuration", temp.name()), std::logic_error);
        }
    }
    SECTION("test init from file applies base") {
        auto temp = TmpFile::named();
        temp << "# A test config\n";
        SECTION("valid") {
            temp << "[t0](trendy): --models=0 --heuristic=Berkmin\n";
            temp.close();
            REQUIRE(config.getValue("solver.otfs") == "0");
            config.setValue("configuration", temp.name());
            REQUIRE(config.getValue("configuration") == temp.name());
            CHECK(config.getValue("solver.otfs") == "2");
        }
        SECTION("invalid") {
            temp << "[t0](invalidBase): --models=0 --heuristic=Berkmin --restarts=x,100,1.5\n";
            temp.close();
            CHECK_THROWS_AS(config.setValue("configuration", temp.name()), std::logic_error);
        }
    }
    SECTION("test init with invalid file") {
        auto temp = TmpFile::named();
        SECTION("invalid option") {
            temp << "[fail]: --config=many\n";
            temp.close();
            CHECK_THROWS_AS(config.setValue("configuration", temp.name()), std::logic_error);
            CHECK(config.validate());
        }
        SECTION("invalid config") {
            temp << "[fail]: --no-lookback --heuristic=Berkmin\n";
            temp.close();
            CHECK(config.setValue("configuration", temp.name()));
            CHECK_THROWS_AS(config.validate(), std::logic_error);
            SharedContext ctx;
            CHECK_THROWS_AS(config.prepare(ctx), std::logic_error);
        }
    }

    SECTION("test init ignore deletion if disabled") {
        const char* argv[] = {"--config=tweety --deletion=no"};
        config.setConfig(argv, ProblemType::asp);
        REQUIRE(config.getValue("configuration") == "tweety");
        REQUIRE(config.getValue("solver.0.deletion") == "no");
        REQUIRE(config.getValue("solver.0.del_cfl") == "0");
        REQUIRE(config.getValue("solver.0.del_grow") == "no");
        REQUIRE(config.getValue("solver.0.del_max") == "umax,0");
    }
    SECTION("test ambiguous option") {
        const char* argv[] = {"--del=no"};
        REQUIRE_THROWS_AS(config.setConfig(argv, ProblemType::asp), Potassco::ProgramOptions::AmbiguousOption);
    }

    SECTION("test string interface") {
        config.setValue("configuration", "auto,6");
        REQUIRE(config.numSolver() == 6);
        REQUIRE(config.solve.numSolver() == 1);
        REQUIRE((config.setValue("asp.eq", "0") && config.asp.iters == 0));
        REQUIRE((config.setValue("solver.0.heuristic", "berkmin") && config.solver(0).heuId == HeuristicType::berkmin));

        REQUIRE(config.getValue("asp.eq") == "0");
        REQUIRE(config.getValue("solver.0.heuristic").find("berkmin") == 0);

        REQUIRE(config.validate());
        REQUIRE(config.setValue("tester.configuration", "frumpy"));
        REQUIRE((config.testerConfig() && config.testerConfig()->numSolver() == 1));
        REQUIRE(config.setValue("tester.configuration", "many,6"));
        REQUIRE((config.testerConfig() && config.testerConfig()->numSolver() == config.numSolver()));

        REQUIRE_THROWS_AS(config.setValue("foo.bar", "123"), std::logic_error);
        REQUIRE_THROWS_AS(config.setValue("tester.eq", "1"), std::logic_error);
        REQUIRE_THROWS_AS(config.setValue("solver.2", "1"), std::logic_error);

        REQUIRE_THROWS_AS(config.getValue("foo.bar"), std::logic_error);
        REQUIRE_THROWS_AS(config.getValue("tester.eq"), std::logic_error);
        REQUIRE_THROWS_AS(config.getValue("solver.0"), std::logic_error);
    }
    SECTION("test master solver is implicit") {
        REQUIRE(config.getValue("solver.heuristic") == "auto,0");
        REQUIRE((config.setValue("solver.heuristic", "berkmin") && config.solver(0).heuId == HeuristicType::berkmin));
        REQUIRE_FALSE(config.hasConfig);
        REQUIRE(config.getValue("configuration") == "auto");
    }
    SECTION("test solver is implicitly created") {
        // solver option
        REQUIRE(config.setValue("solver.1.heuristic", "berkmin"));
        REQUIRE(config.numSolver() == 2);
        REQUIRE(config.solver(1).heuId == HeuristicType::berkmin);
        // search option
        REQUIRE(config.setValue("solver.2.restarts", "+,100,10"));
        REQUIRE(config.numSearch() == 3);
        REQUIRE(config.search(2).restart.rsSched == ScheduleStrategy::arith(100, 10));
        REQUIRE(config.numSolver() == 3);

        REQUIRE(config.setValue("solver.17.heuristic", "unit"));
        REQUIRE(config.numSolver() == 18);
        for (uint32_t i : irange(config.numSolver())) { REQUIRE(i == config.solver(i).id); }
    }
    SECTION("test get does not create solver") {
        REQUIRE(config.numSolver() == 1);
        REQUIRE(config.setValue("solver.heuristic", "berkmin"));
        auto k = config.getKey(ClaspCliConfig::key_solver, "1.heuristic");
        REQUIRE(k != ClaspCliConfig::key_invalid);
        REQUIRE(config.numSolver() == 1);
        SECTION("by key") {
            CHECK(config.getValue(k, val) > 0);
            CHECK(val == config.getValue("solver.heuristic"));
        }
        SECTION("by path") { CHECK(config.getValue("solver.1.heuristic") == config.getValue("solver.heuristic")); }
    }
    SECTION("test tester is implicitly created") {
        REQUIRE(config.setValue("tester.learn_explicit", "1"));
        REQUIRE((config.testerConfig() != nullptr && config.testerConfig()->shortMode == 1));
        REQUIRE_FALSE(config.testerConfig()->hasConfig);
        REQUIRE(config.getValue("tester.configuration") == "auto");
        REQUIRE(config.testerConfig()->satPre.type == 0);
        REQUIRE(config.config("tester"));
        REQUIRE(config.testerConfig()->satPre.type == 0);
        REQUIRE_FALSE(config.testerConfig()->hasConfig);
    }
}

TEST_CASE_METHOD(OptionTest, "Cli options keys", "[cli]") {
    SECTION("test enumerate") {
        std::vector<std::string> keys;
        traverseKey(keys, ClaspCliConfig::key_root, "");
        REQUIRE(contains(keys, "configuration"));
        REQUIRE(contains(keys, "tester.configuration"));
        bool tester = false;
        for (std::string grp;;) {
#define OPTION(k, e, a, d, x, ...) REQUIRE(hasOption(grp + #k, keys, tester));
#define GROUP_BEGIN(X)             grp += (X);
#define GROUP_END(X)               grp.erase(grp.find(X));
#define CLASP_CONTEXT_OPTIONS      ""
#define CLASP_GLOBAL_OPTIONS       ""
#define CLASP_SOLVE_OPTIONS        "solve."
#define CLASP_ASP_OPTIONS          "asp."
#define CLASP_SOLVER_OPTIONS       "solver."
#define CLASP_SEARCH_OPTIONS       "solver."
#include <clasp/cli/clasp_cli_options.inl>

            if (tester) {
                break;
            }
            tester = true;
            grp    = "tester.";
        }
    }

    SECTION("test query") {
        int         nSubkeys, arrLen, nValues;
        std::string help;
        REQUIRE(config.getKeyInfo(ClaspCliConfig::key_root, &nSubkeys, &arrLen, &help, &nValues) == 4);
        REQUIRE((nSubkeys > 0 && arrLen == -1 && not help.empty() && nValues == -1 &&
                 ClaspCliConfig::isLeafKey(ClaspCliConfig::key_root) == false));

        REQUIRE(config.getKeyInfo(ClaspCliConfig::key_solver, &nSubkeys, &arrLen, &help, &nValues) == 4);
        REQUIRE((nSubkeys > 0 && arrLen >= 0 && not help.empty() && nValues == -1 &&
                 ClaspCliConfig::isLeafKey(ClaspCliConfig::key_root) == false));

        auto s1 = config.getKey(ClaspCliConfig::key_solver, "1");
        REQUIRE(s1 != ClaspCliConfig::key_invalid);
        int nSolverKeys = nSubkeys;
        REQUIRE(config.getKeyInfo(s1, &nSubkeys, &arrLen, &help, &nValues) == 4);
        REQUIRE((nSubkeys == nSolverKeys && arrLen == -1));

        REQUIRE(config.getKey(ClaspCliConfig::key_solver, "heuristic") != ClaspCliConfig::key_invalid);
        REQUIRE(config.getKey(s1, ".heuristic") != ClaspCliConfig::key_invalid);
        REQUIRE(config.getKey(ClaspCliConfig::key_solver, ".") == ClaspCliConfig::key_solver);
        REQUIRE(config.getKey(ClaspCliConfig::key_solver, "") == ClaspCliConfig::key_solver);
        REQUIRE(config.getKey(ClaspCliConfig::key_solver, "asp") == ClaspCliConfig::key_invalid);

        REQUIRE(config.getKey(ClaspCliConfig::key_root, "stats") != ClaspCliConfig::key_invalid);
        REQUIRE(config.getKey(ClaspCliConfig::key_tester, "stats") == ClaspCliConfig::key_invalid);
        REQUIRE(config.getKey(ClaspCliConfig::key_root, "tester") != ClaspCliConfig::key_invalid);
        REQUIRE(config.getKey(ClaspCliConfig::key_tester, "tester") == ClaspCliConfig::key_invalid);

        auto tester = config.getKey(ClaspCliConfig::key_root, "tester");
        REQUIRE(tester == ClaspCliConfig::key_tester);
        REQUIRE(config.getKey(tester, "asp") == ClaspCliConfig::key_invalid);

        auto heuS0 = config.getKey(ClaspCliConfig::key_solver, "heuristic");
        auto heuS1 = config.getKey(s1, "heuristic");
        auto heuT  = config.getKey(ClaspCliConfig::key_tester, "solver.heuristic");

        REQUIRE((heuS0 != heuS1 && heuS0 != heuT && heuS1 != heuT));

        REQUIRE(config.getKey(heuS0, "restarts") == ClaspCliConfig::key_invalid);

        REQUIRE(config.getKeyInfo(heuS0, nullptr, nullptr, &help, nullptr) == 1);
        REQUIRE(help.find("decision heuristic") != std::string::npos);
    }
    SECTION("test query array") {
        REQUIRE(config.getArrKey(ClaspCliConfig::key_root, 0) == ClaspCliConfig::key_invalid);
        auto s0 = config.getArrKey(ClaspCliConfig::key_solver, 0);
        REQUIRE(s0 != ClaspCliConfig::key_invalid);
        REQUIRE(s0 != ClaspCliConfig::key_solver);
        REQUIRE(config.getArrKey(ClaspCliConfig::key_solver, 64) == ClaspCliConfig::key_invalid);

        auto st0 = config.getArrKey(config.getKey(ClaspCliConfig::key_tester, "solver"), 0);
        REQUIRE((s0 != st0 && st0 != ClaspCliConfig::key_invalid));
        if (Clasp::SolveOptions::supportedSolvers() > 1) {
            auto s5 = config.getArrKey(ClaspCliConfig::key_solver, 5);
            config.setValue(config.getKey(s5, "heuristic"), "unit");
            REQUIRE(config.solver(5).heuId == HeuristicType::unit);
        }
    }
}

#if CLASP_HAS_THREADS
TEST_CASE_METHOD(OptionTest, "Cli mt options", "[cli][mt]") {
    SECTION("test config from argv") {
        REQUIRE(config.numSolver() == 1);
        REQUIRE(config.solve.numSolver() == 1);
        REQUIRE(config.solve.numModels != 0);
        const char* argv[] = {"-n0",     "--parallel-mode",         "4", "--save-progress=20",
                              "--stats", "--tester=--config=frumpy"};
        config.setConfig(argv, ProblemType::asp);
        REQUIRE(config.getValue("configuration") == "auto");
        REQUIRE(config.getValue("asp.eq") == "3");
        REQUIRE(config.getValue("asp.trans_ext") == "dynamic");
        REQUIRE(config.solve.numSolver() == 4);
        REQUIRE(config.numSolver() == 4);
        REQUIRE(config.solve.numModels == 0);
        for (uint32_t i : irange(config.numSolver())) { REQUIRE(config.solver(i).saveProgress == 20); }
        REQUIRE(config.testerConfig());
        REQUIRE(config.testerConfig()->numSolver() == 1);
        REQUIRE(config.testerConfig()->hasConfig);
        REQUIRE(config.getValue("tester.configuration") == "frumpy");
    }
    SECTION("test init from file") {
        auto temp = TmpFile::named();
        temp << "[t0]: --models=0 --parallel-mode=4 --heuristic=Berkmin --restarts=x,100,1.5\n"
             << "[t1](tweety): --heuristic=Vsids,98 --restarts=L,128\n"
             << "t2   (jumpy): --heuristic=Vmtf --restarts=D,100,0.7\n"
             << "[t3]: --heuristic=None --restarts=F,1000\n";
        temp.close();
        config.setValue("configuration", temp.name());

        REQUIRE(config.getValue("configuration") == temp.name());
        REQUIRE_THROWS_AS(config.getValue("tester.configuration"), std::logic_error);
        REQUIRE_THROWS_AS(config.getValue("tester.learn_explicit"), std::logic_error);
        REQUIRE(config.solve.numModels == 0);
        REQUIRE(config.solver(0).heuId == HeuristicType::berkmin);
        REQUIRE(config.search(0).restart.rsSched == ScheduleStrategy::geom(100, 1.5));
        REQUIRE(config.solve.numSolver() == 4);
        REQUIRE(config.numSolver() == 4);
        REQUIRE(config.solver(1).heuId == HeuristicType::vsids);
        REQUIRE(config.solver(2).heuId == HeuristicType::vmtf);
        REQUIRE(config.solver(3).heuId == HeuristicType::none);
        REQUIRE(config.search(1).restart.rsSched == ScheduleStrategy::luby(128));
        REQUIRE(config.search(2).restart.rsSched.isDynamic());
        REQUIRE(config.search(2).restart.base() == 100);
        REQUIRE(config.search(2).restart.rsSched.k() == 0.7f);
        REQUIRE(config.search(2).restart.rsSched.lbdLim() == 0);
        REQUIRE(config.search(3).restart.rsSched == ScheduleStrategy::fixed(1000));

        config.setValue("tester.configuration", temp.name());
        REQUIRE(config.getValue("tester.configuration") == temp.name());
        temp.unlink();
        REQUIRE(config.setValue(config.getKey(ClaspCliConfig::key_root, "configuration"), temp.name()) == -2);
        REQUIRE(config.setValue(config.getKey(ClaspCliConfig::key_tester, "configuration"), temp.name()) == -2);
    }
    SECTION("test parallel-mode option") {
        auto pMode = config.getKey(ClaspCliConfig::key_root, "solve.parallel_mode");
        REQUIRE(0 == config.setValue(pMode, "0"));
        REQUIRE(uint32_t(1) == config.solve.algorithm.threads);
        REQUIRE(SolveOptions::Algorithm::mode_compete == config.solve.algorithm.mode);
        REQUIRE(config.solve.numSolver() == 1);

        REQUIRE(1 == config.setValue(pMode, "10"));
        REQUIRE(uint32_t(10) == config.solve.algorithm.threads);
        REQUIRE(SolveOptions::Algorithm::mode_compete == config.solve.algorithm.mode);
        REQUIRE(config.solve.numSolver() == 10);

        REQUIRE(1 == config.setValue(pMode, "10,split"));
        REQUIRE(uint32_t(10) == config.solve.algorithm.threads);
        REQUIRE(SolveOptions::Algorithm::mode_split == config.solve.algorithm.mode);
        REQUIRE(config.solve.numSolver() == 10);

        REQUIRE(0 == config.setValue(pMode, "65"));
    }
    SECTION("test distribute option") {
        auto distribute = config.getKey(ClaspCliConfig::key_root, "solve.distribute");
        REQUIRE(1 == config.setValue(distribute, "0"));
        REQUIRE(0 == config.setValue(distribute, "0,1"));
        REQUIRE(1 == config.setValue(distribute, "conflict"));
        REQUIRE(Distributor::Policy::conflict == config.solve.distribute.types);
        REQUIRE(4 == config.solve.distribute.lbd);

        REQUIRE(1 == config.setValue(distribute, "loop,2"));
        REQUIRE(Distributor::Policy::loop == config.solve.distribute.types);
        REQUIRE(2 == config.solve.distribute.lbd);

        REQUIRE(1 == config.setValue(distribute, "all,2,123"));
        REQUIRE(config.getValue("solve.distribute") == "all,global,2,123");
        REQUIRE(Distributor::Policy::all == config.solve.distribute.types);
        REQUIRE(2 == config.solve.distribute.lbd);
        REQUIRE(123 == config.solve.distribute.size);
    }
    SECTION("test integrate option") {
        auto integrate = config.getKey(ClaspCliConfig::key_root, "solve.integrate");

        REQUIRE(0 == config.setValue(integrate, "0"));
        REQUIRE(0 == config.setValue(integrate, "no"));

        REQUIRE(1 == config.setValue(integrate, "active"));
        REQUIRE(SolveOptions::Integration::filter_heuristic == config.solve.integrate.filter);
        REQUIRE(1024 == config.solve.integrate.grace);
        REQUIRE(SolveOptions::Integration::topo_all == config.solve.integrate.topo);

        REQUIRE(1 == config.setValue(integrate, "unsat,100"));
        REQUIRE(SolveOptions::Integration::filter_sat == config.solve.integrate.filter);
        REQUIRE(100 == config.solve.integrate.grace);
        REQUIRE(SolveOptions::Integration::topo_all == config.solve.integrate.topo);

        REQUIRE(1 == config.setValue(integrate, "gp,200,cubeX"));
        REQUIRE(SolveOptions::Integration::filter_gp == config.solve.integrate.filter);
        REQUIRE(200 == config.solve.integrate.grace);
        REQUIRE(SolveOptions::Integration::topo_cubex == config.solve.integrate.topo);

        REQUIRE(1 == config.setValue(integrate, "gp,77,cube"));
        REQUIRE(SolveOptions::Integration::filter_gp == config.solve.integrate.filter);
        REQUIRE(77 == config.solve.integrate.grace);
        REQUIRE(SolveOptions::Integration::topo_cube == config.solve.integrate.topo);
    }
}
#endif

TEST_CASE_METHOD(TmpFile, "TextOutput", "[cli]") {
    using namespace std::literals;
    ClaspFacade libclasp;
    ClaspConfig config;
    config.satPre.type     = 2;
    config.solve.numModels = 1;
    std::string input      = "/some/directory/some/file.asp";
    auto&       asp        = libclasp.startAsp(config);
    static_cast<void>(asp);
    Clasp::Test::lpAdd(asp, "{x1,x2,x3,x4,x5}. #minimize{x1,not x2, not x3, x4, x5}.");
    TextOutput::Options opts;
    opts.verbosity = 1;
    REQUIRE(Potassco::enableAnsiColorSupport(rep()) == std::errc::inappropriate_io_control_operation);
    SECTION("banner") {
        SECTION("asp") {
            TextOutput out(rep(), opts);
            out.start("test_solver", "1.0", Potassco::toSpan(input));
            REQUIRE(matchOutput("test_solver version 1.0\n"
                                "Reading from /some/directory/some/file.asp\n"));
        }
        SECTION("sat") {
            opts.format = TextOutput::format_sat09;
            TextOutput out(rep(), opts);
            out.start("test_solver", "1.0", Potassco::toSpan(input));
            REQUIRE(matchOutput("c test_solver version 1.0\n"
                                "c Reading from /some/directory/some/file.asp\n"));
        }
        SECTION("quiet") {
            opts.verbosity = 0;
            TextOutput out(rep(), opts);
            out.start("test_solver", "1.0", Potassco::toSpan(input));
            REQUIRE(matchOutput(""));
        }
    }
    SECTION("Model") {
        libclasp.prepare();
        struct TheoryAtoms : OutputTable::Theory {
            const char* first(const Model&) override {
                idx = UINT32_MAX;
                return next();
            }
            const char*              next() override { return ++idx < size32(data) ? data[idx].c_str() : nullptr; }
            std::vector<std::string> data;
            uint32_t                 idx{0};
        } ta;
        ta.data.emplace_back("atom1");
        ta.data.emplace_back("atom2");
        libclasp.ctx.output.add(ta);
        REQUIRE(libclasp.solve(std::vector{posLit(2), posLit(3), posLit(5)}).sat());
        auto* m = libclasp.summary().model();
        REQUIRE(m);
        TextOutput out(rep(), opts);
        enum class Custom { none, before, after, only };
        auto pos    = GENERATE(Custom::none, Custom::before, Custom::after, Custom::only);
        auto prefix = "Answer: 1 (Time: T.TTTs)\n";
        auto custom = "custom(1) custom(2)\n";
        auto clasp  = "";
        auto suffix = "Optimization: 1\n";
        auto expect = [&](Custom p) {
            switch (p) {
                default            : return std::string(prefix).append(clasp).append(suffix);
                case Custom::before: return std::string(prefix).append(custom).append(clasp).append(suffix);
                case Custom::after : return std::string(prefix).append(clasp).append(custom).append(suffix);
                case Custom::only  : return std::string(prefix).append(custom).append(suffix);
            }
        };
        if (pos != Custom::none) {
            out.setModelPrinter([&](TextOutput& to, const SharedContext& ctx, const Model& model) {
                REQUIRE(&to == &out);
                REQUIRE(&ctx == &libclasp.ctx);
                REQUIRE(pos != Custom::none);
                if (pos == Custom::before) {
                    fprintf(rep(), "%s\n", custom);
                    to.printModelValues(ctx, model);
                    return;
                }
                if (pos == Custom::after) {
                    to.printModelValues(ctx, model);
                }
                fprintf(rep(), "%s\n", custom);
            });
        }
        CAPTURE(pos);
        SECTION("names") {
            libclasp.ctx.output.add("x1", posLit(1), 1);
            libclasp.ctx.output.add("x2", posLit(2), 2);
            libclasp.ctx.output.add("x3", posLit(3), 3);
            libclasp.ctx.output.add("x4", posLit(4), 4);
            libclasp.ctx.output.add("x5", posLit(5), 5);
            clasp = "atom1 atom2 x2 x3 x5\n";
        }
        SECTION("vars") {
            libclasp.ctx.output.setVarRange({1, 6});
            clasp = "atom1 atom2 -1 2 3 -4 5\n";
        }
        CAPTURE(clasp);
        out.model(*libclasp.ctx.master(), *m);
        REQUIRE(matchOutput(expect(pos)));
    }
    SECTION("Unsat") {
        REQUIRE(libclasp.solve().sat());
        libclasp.ctx.minimizeNoCreate()->incLower(0, 1);
        Model      m{*libclasp.summary().model()};
        TextOutput out(rep(), opts);
        REQUIRE(m.ctx);
        m.lower = m.ctx->lowerBound();
        m.lb    = 1;
        REQUIRE(m.lower.active());
        m.costs = {};
        out.unsat(*libclasp.ctx.master(), m);
        REQUIRE(matchOutput("Progression : [     1;inf] (Time: T.TTTs)\n"));

        auto upperBound = static_cast<Wsum_t>(10);
        m.costs         = Potassco::toSpan(upperBound);
        out.unsat(*libclasp.ctx.master(), m);
        REQUIRE(matchOutput("Progression : [ 1;10] (Error: 9.0000 Time: T.TTTs)\n"));
    }
    SECTION("summary") {
        REQUIRE(libclasp.solve().sat());
        TextOutput           out(rep(), opts);
        ClaspFacade::Summary summary{};
        summary.init(libclasp);
        summary.totalTime     = 12.34;
        summary.cpuTime       = 11.23;
        summary.solveTime     = 10.08;
        summary.step          = 3;
        auto*               m = const_cast<Model*>(summary.model());
        std::vector<Wsum_t> costs{10, 20, 30};
        m->costs = costs;
        m->opt   = 0;

        static constexpr auto makeResult = [](SolveResult::Res res, bool ex, int sig = 0) {
            SolveResult r{};
            r.flags = res;
            if (ex) {
                r.flags |= static_cast<uint8_t>(SolveResult::ext_exhaust);
            }
            if (sig) {
                r.signal  = sig;
                r.flags  |= static_cast<uint8_t>(SolveResult::ext_interrupt);
            }
            return r;
        };
        SECTION("unknown") {
            summary.result = makeResult(SolveResult::res_unknown, false, 0);
            SECTION("step") {
                out.setCallQuiet(Output::print_all);
                out.event(ClaspFacade::StepReady{summary});
                REQUIRE(matchOutput("UNKNOWN\n\n"
                                    "Models       : 0+\n"
                                    "Time         : 12.340s  (Solving: 10.080s 1st Model: 0.000s Unsat: 0.000s)\n"
                                    "CPU Time     : 11.230s\n"));
            }
            SECTION("accu") {
                out.setCallQuiet(Output::print_no);
                out.shutdown(summary);
                REQUIRE(matchOutput("UNKNOWN\n\n"
                                    "Models       : 0+\n"
                                    "Calls        : 4\n"
                                    "Time         : 12.340s  (Solving: 10.080s 1st Model: 0.000s Unsat: 0.000s)\n"
                                    "CPU Time     : 11.230s\n"));
            }
            SECTION("interrupt") {
                out.setCallQuiet(Output::print_all);
                summary.result = makeResult(SolveResult::res_unknown, false, SIGALRM);
                out.event(ClaspFacade::StepReady{summary});
                REQUIRE(matchOutput("UNKNOWN\n\n"
                                    "TIME LIMIT   : 1        (Signal: SIGALRM)\n"
                                    "Models       : 0+\n"
                                    "Time         : 12.340s  (Solving: 10.080s 1st Model: 0.000s Unsat: 0.000s)\n"
                                    "CPU Time     : 11.230s\n"));
            }
        }
        summary.unsatTime  = 1.15;
        summary.satTime    = 2.34;
        summary.numEnum    = 23;
        summary.numOptimal = 5;

        SECTION("sat") {
            summary.result = makeResult(SolveResult::res_sat, false);
            SECTION("step") {
                out.setCallQuiet(Output::print_all);
                out.event(ClaspFacade::StepReady{summary});
                REQUIRE(matchOutput("SATISFIABLE\n\n"
                                    "Models       : 23+\n"
                                    "  Optimum    : unknown\n"
                                    "Time         : 12.340s  (Solving: 10.080s 1st Model: 2.340s Unsat: 1.150s)\n"
                                    "CPU Time     : 11.230s\n"));
            }
            SECTION("accu") {
                out.shutdown(summary);
                REQUIRE(matchOutput("Calls        : 4"));
            }
            SECTION("exhausted") {
                summary.result = makeResult(SolveResult::res_sat, true);
                m->opt         = 1;
                out.setCallQuiet(Output::print_all);
                out.event(ClaspFacade::StepReady{summary});
                REQUIRE(matchOutput(
                    "------------------------------------------------------------------------------------------|\n"
                    "OPTIMUM FOUND\n\n"
                    "Models       : 23\n"
                    "  Optimum    : yes\n"
                    "Optimization : 10 20 30\n"
                    "Time         : 12.340s  (Solving: 10.080s 1st Model: 2.340s Unsat: 1.150s)\n"
                    "CPU Time     : 11.230s\n"));
            }
        }
        SECTION("unsat") {
            summary.result = makeResult(SolveResult::res_unsat, true);
            SECTION("step") {
                out.setCallQuiet(Output::print_all);
                out.event(ClaspFacade::StepReady{summary});
                REQUIRE(matchOutput("UNSATISFIABLE\n\n"));
            }
            SECTION("accu") {
                out.shutdown(summary);
                REQUIRE(matchOutput("UNSATISFIABLE\n\nCalls        : 4"));
            }
        }
    }
    SECTION("Event") {
        TextOutput out(rep(), opts);
        libclasp.prepare();
        struct Ev : EventHandler {
            void    onEvent(const Event& ev) override { out->event(ev); }
            Output* out{nullptr};
        } handler;
        handler.setVerbosity(Event::subsystem_facade, static_cast<Event::Verbosity>(3));
        handler.setVerbosity(Event::subsystem_load, static_cast<Event::Verbosity>(3));
        handler.setVerbosity(Event::subsystem_prepare, static_cast<Event::Verbosity>(3));
        handler.setVerbosity(Event::subsystem_solve, static_cast<Event::Verbosity>(3));
        handler.out = &out;
        libclasp.ctx.setEventHandler(&handler);
        out.setCallQuiet(Output::print_best);
        out.start("test_solver", "1.0", Potassco::toSpan(input));
        discardOutput();
        libclasp.ctx.report(ClaspFacade::StepStart{libclasp});
        REQUIRE(matchOutput(
            "------------------------------------------------------------------------------------------|\n"));
        out.setVerbosity(3);
        libclasp.ctx.report(Event::subsystem_load);
        REQUIRE(matchOutput("Reading      : "));
        libclasp.ctx.report(Event::subsystem_prepare);
        REQUIRE(matchOutput("T.TTTs\nPreprocessing: "));
        std::string next("T.TTTs\n");
        SECTION("sat-pre") {
            using SatPre = Clasp::SatPreprocessor;
            libclasp.ctx.report(SatPre::Progress{libclasp.ctx.satPrepro.get(), SatPre::Progress::event_enter, 0, 100});
            REQUIRE(matchOutput("T.TTTs\nSat-Prepro   : \r", complete));
            libclasp.ctx.report(
                SatPre::Progress{libclasp.ctx.satPrepro.get(), static_cast<SatPre::Progress::EventOp>('E'), 44, 100});
            REQUIRE(matchOutput("Sat-Prepro   : E:       44/100"));
            SECTION("with exit") {
                libclasp.ctx.report(
                    SatPre::Progress{libclasp.ctx.satPrepro.get(), SatPre::Progress::event_exit, 100, 100});
                REQUIRE(matchOutput("Sat-Prepro   : T.TTTs   (ClRemoved: 0 ClAdded: 0 LitsStr: 0)\n", complete));
                next = "";
            }
            SECTION("without exit") { next = "Sat-Prepro   : T.TTTs   (unexpected state change - result unknown)\n"; }
        }
        next += "Solving...\n";
        libclasp.ctx.report(Event::subsystem_solve);
        REQUIRE(matchOutput(next, complete));

        BasicSolveEvent ev{*libclasp.ctx.master(), BasicSolveEvent::event_restart, 1000, 2000};
        libclasp.ctx.report(ev);
        REQUIRE(
            matchOutput("------------------------------------------------------------------------------------------|\n"
                        "ID:T       Vars           Constraints         State            Limits            Time     |\n"
                        "       #free/#fixed   #problem/#learnt  #conflicts/ratio #conflict/#learnt                |\n"
                        "------------------------------------------------------------------------------------------|\n"
                        " 0:R|      5/0      |       0/0       |         0/0.000 |    1000/2000      |      T.TTTs |\n",
                        complete));
        libclasp.ctx.master()->stats.conflicts = 1000;
        libclasp.ctx.master()->stats.choices   = 500;
        libclasp.ctx.report(ev);
        REQUIRE(matchOutput(
            " 0:R|      5/0      |       0/0       |      1000/2.000 |    1000/2000      |      T.TTTs |\n", complete));
        ev.op     = BasicSolveEvent::event_deletion;
        ev.cLimit = 700;
        libclasp.ctx.report(ev);
        REQUIRE(matchOutput(
            " 0:D|      5/0      |       0/0       |      1000/2.000 |     700/2000      |      T.TTTs |\n", complete));
        ev.op                                = BasicSolveEvent::event_exit;
        libclasp.ctx.master()->stats.choices = 1200;
        libclasp.ctx.report(ev);
        REQUIRE(matchOutput(
            " 0:E|      5/0      |       0/0       |      1000/0.833 |     700/2000      |      T.TTTs |\n", complete));
        SolveTestEvent ste{*ev.solver, 12, true};
        libclasp.ctx.report(ste);
        REQUIRE(matchOutput(""));
        out.setVerbosity(7);
        libclasp.ctx.report(ste);
        REQUIRE(
            matchOutput("------------------------------------------------------------------------------------------|\n"
                        " 0:P|      5/?      |       0/0       |         0/0.000 |     12:    T.TTTs |      T.TTTs |\r",
                        complete));
        ste.result = 1;
        libclasp.ctx.report(ste);
        REQUIRE(matchOutput(
            " 0:P|      5/Y      |       0/0       |         0/0.000 |     12:    T.TTTs |      T.TTTs |\n", complete));
        ste.result  = 0;
        ste.hcc     = 2;
        ste.partial = false;
        libclasp.ctx.report(ste);
        REQUIRE(matchOutput(
            " 0:F|      5/N      |       0/0       |         0/0.000 |      2:    T.TTTs |      T.TTTs |\n", complete));
        libclasp.ctx.report("attach", ev.solver);
        REQUIRE(
            matchOutput("------------------------------------------------------------------------------------------|\n"
                        "0:L| [Solving+T.TTTs]               attach                                 |      T.TTTs |\n",
                        complete));
#if CLASP_HAS_THREADS
        libclasp.ctx.report(mt::MessageEvent(*ev.solver, "SYNC", mt::MessageEvent::sent));
        REQUIRE(matchOutput(
            " 0:X| SYNC                           sent                                   |      T.TTTs |\n", complete));
        libclasp.ctx.setConcurrency(3, SharedContext::resize_resize);
        libclasp.ctx.report(mt::MessageEvent(*libclasp.ctx.solver(1), "SYNC", mt::MessageEvent::received));
        REQUIRE(matchOutput(
            " 1:X| SYNC                           received                               |      T.TTTs |\n", complete));
        libclasp.ctx.report(mt::MessageEvent(*libclasp.ctx.solver(2), "SYNC", mt::MessageEvent::completed, 12.34));
        REQUIRE(matchOutput(" 2:X| SYNC                           completed            in        12.340s |"));
#endif
    }
}

TEST_CASE_METHOD(TmpFile, "Output", "[cli]") {
    using namespace std::literals;
    ClaspFacade libclasp;
    ClaspConfig config;
    config.stats              = 1;
    std::string         input = "some file";
    TextOutput::Options opts;
    opts.verbosity = 1;
    SECTION("UserStats") {
        auto                    test = GENERATE("text"sv, "json"sv);
        std::unique_ptr<Output> out;
        std::string_view        expect;
        auto                    accuOff = 0;
        if (test == "text"sv) {
            out    = std::make_unique<TextOutput>(rep(), opts);
            expect = R"(deathCounter
  total      : 42
  chickens   : 712
  [thread 0]
    total    : 20
    Animals
      chicken: 2
      cows   : 5
    feeding cost: 1
  [thread 1]
    total    : 40
    Animals
      chicken: 4
      cows   : 10
    feeding cost: 2
  [thread 2]
    total    : 60
    Animals
      chicken: 6
      cows   : 15
    feeding cost: 3
  [thread 3]
    total    : 80
    Animals
      chicken: 8
      cows   : 20
    feeding cost: 4
)";
        }
        else {
            out     = std::make_unique<JsonOutput>(rep(), 1);
            expect  = R"(      "deathCounter": {
        "total": 42,
        "chickens": 712,
        "thread": [
          {
            "total": 20,
            "Animals": {
              "chicken": 2,
              "cows": 5
            },
            "feeding cost": 1
          },
          {
            "total": 40,
            "Animals": {
              "chicken": 4,
              "cows": 10
            },
            "feeding cost": 2
          },
          {
            "total": 60,
            "Animals": {
              "chicken": 6,
              "cows": 15
            },
            "feeding cost": 3
          },
          {
            "total": 80,
            "Animals": {
              "chicken": 8,
              "cows": 20
            },
            "feeding cost": 4
          }
        ]
      }
    })";
            accuOff = 2;
        }
        CAPTURE(test, accuOff);
        out->start("test_solver", "1.0", Potassco::toSpan(input));
        auto& asp = libclasp.startAsp(config, true);
        static_cast<void>(asp);
        libclasp.prepare();
        libclasp.solve();
        auto* stats = libclasp.getStats();
        out->setCallQuiet(Output::print_all);
        SECTION("step") {
            Clasp::Test::addExternalStats(stats, "user_step");
            out->event(ClaspFacade::StepReady{libclasp.summary()});
            REQUIRE(matchOutput(expect));
        }
        SECTION("accu") {
            Clasp::Test::addExternalStats(stats, "user_accu");
            out->shutdown(libclasp.summary(true));
            REQUIRE(matchOutput(expect, lineOff(accuOff)));
        }
        SECTION("unknown root") {
            Clasp::Test::addExternalStats(stats, "myRoot");
            out->event(ClaspFacade::StepReady{libclasp.summary()});
            REQUIRE_FALSE(matchOutput(expect));
        }
    }
}

} // namespace Cli::Test

} // namespace Clasp
