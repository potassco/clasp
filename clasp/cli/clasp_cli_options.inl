//
// Copyright (c) 2013-present Benjamin Kaufmann
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
// clang-format off
/*!
 * \file
 * \brief Supermacros for describing clasp's options.
 * \code
 * OPTION(<key>, <spec>, <arg>, <desc>, <set>, <get>)
 * \endcode
 * Each option consists of:
 *  - <key> : a key (valid and unique C identifier in 'snake_case', e.g., `restart_on_model`)
 *  - <spec>: a value specification as understood by ProgramOptions::OptionInitHelper::applySpec()
 *  - <arg> : an arg description (ARG macro) or empty
 *     - ARG(X): arg description as understood by ProgramOptions::Value, e.g., `arg("<mode>")`
 *     - ARG_EXT(X, ...): arg description followed by one or more enum mapping
 *  - <desc>: a help description (string)
 *  - <set> : an action to be executed when a value (string) for the option is found in a source
 *  - <get> : an action to be executed when the current value for an option is requested
 *
 * \note In the implementation of ClaspCliConfig, each key is mapped to an enumeration constant and
 * the stringified version of key (i.e. \#key) is used to identify options.
 * Furthermore, the key is also used for generating command-line option names.
 * As a convention, compound keys using 'snake_case' to separate words are mapped to dash-separated
 * command-line option names.
 * E.g. an `option_like_this` is mapped to the command-line option `option-like-this`.
 *
 * \note ClaspCliConfig assumes a certain option order. In particular, context options shall
 * precede all solver/search options, which in turn shall precede global asp/solving options.
 *
 * \note The following set actions may be used:
 *  - STORE(obj): converts the string value to the type of obj and stores the result in obj.
 *  - STORE_U(E, n): converts the string value to type E and stores it as unsigned int in n.
 *  - STORE_LEQ(n, max): converts the string value to an unsigned int and stores the result in n if it is <= max.
 *  - STORE_FLAG(n): converts the string value to a bool and stores the result in n as either 0 or 1.
 *  - STORE_OR_FILL(n): converts the string value to an unsigned int t and sets n to std::min(t, maxValue(n)).
 *  - FUN(arg): anonymous function of type bool (Arg& arg), where arg provides the following interface:
 *    - arg.off()          : returns whether arg contains a single token representing a valid off value
 *    - arg.get(x [, ...]) : tries to convert the input into the given arguments, where all but the first are optional;
 *                           returns true if the full input was converted and at least `x` got a value
 *
 * \note The following get actions may be used:
 *  - FUN(str)      : anonymous function of type void (OutputStream& str)
 *  - GET(obj...)   : shorthand for FUN(str) { (str << obj)...; }
 *  - GET_IF(C, obj): shorthand for FUN(str) { C ? str << obj : str << off; }
 *  .
 *
 * \note The following primitives may be used in the set/get arguments:
 *  - off                  : singleton object representing a valid off value ("no", "off", "false", "0")
 *  - SET(x, y)            : shorthand for (x=y) == y.
 *  - SET_LEQ(x, v, m)     : shorthand for (x <= m && SET(x, v)).
 *  - SET_GEQ(x, v, m)     : shorthand for (x >= m && SET(x, v)).
 *  - SET_OR_FILL(x, v)    : behaves like SET(x, min(v, maxValue(x)))
 *  - SET_OR_ZERO(x,v)     : behaves like v <= maxValue(x) ? SET(x, v) : SET(x, 0)
 *  .
 */
#if !defined(OPTION) || defined(SELF) || !defined(CLASP_HAS_THREADS)
#error Invalid include context
#endif

#if !defined(GROUP_BEGIN)
#define GROUP_BEGIN(X)
#endif

#if !defined(GROUP_END)
#define GROUP_END(X)
#endif

//! Options for configuring a SharedContext object stored in a Clasp::ContextParams object.
#if defined(CLASP_CONTEXT_OPTIONS) || defined(CLASP_ALL_GROUPS)
#if !defined(CLASP_CONTEXT_OPTIONS)
#define CLASP_CONTEXT_OPTIONS (*base)
#endif
#define SELF CLASP_CONTEXT_OPTIONS
GROUP_BEGIN(SELF)
OPTION(share, "!@1", ARG_EXT(defaultsTo("auto", true), ENUM_MAP(ContextParams::ShareMode,
       MAP("no", share_no), MAP("all", share_all), MAP("auto", share_auto), MAP("problem", share_problem),
       MAP("learnt", share_learnt))),
       "Configure physical sharing of constraints [%D]\n"
       "      %A: {auto|problem|learnt|all}", STORE_U(ContextParams::ShareMode, SELF.shareMode), GET(as<ContextParams::ShareMode>(SELF.shareMode)))
OPTION(learn_explicit, "*@2" ,, "Do not use Short Implication Graph for learning", STORE_FLAG(SELF.shortMode), GET(SELF.shortMode))
OPTION(short_simp_mode, "@2" , ARG_EXT(arg("<mode>")->defaultsTo("no", true), ENUM_MAP(ContextParams::ShortSimpMode,
       MAP("no", simp_no), MAP("learnt", simp_learnt), MAP("all", simp_all))),
       "Remove duplicate short constraints [%D]\n"
       "      %A: {no|learnt|all}", STORE_U(ContextParams::ShortSimpMode, SELF.shortSimp), GET(as<ContextParams::ShortSimpMode>(SELF.shortSimp)))
OPTION(sat_prepro, "!@1", ARG(arg("<arg>")->implicit("2")),
       "Run SatELite-like preprocessing (Implicit: %I)\n"
       "      %A: <level>[,<limit>...]\n"
       "        <level> : Set preprocessing level to <level  {1..3}>\n"
       "          1: Variable elimination with subsumption (VE)\n"
       "          2: VE with limited blocked clause elimination (BCE)\n"
       "          3: Full BCE followed by VE\n"
       "        <limit> : [<key {iter|occ|time|frozen|clause}>=]<n> (0=no limit)\n"
       "          iter  : Set iteration limit to <n>           [0]\n"
       "          occ   : Set variable occurrence limit to <n> [0]\n"
       "          time  : Set time limit to <n> seconds        [0]\n"
       "          frozen: Set frozen variables limit to <n>%%   [0]\n"
       "          size  : Set size limit to <n>*1000 clauses   [4000]", STORE(SELF.satPre), GET(SELF.satPre))
GROUP_END(SELF)
#undef CLASP_CONTEXT_OPTIONS
#undef SELF
#endif

//! Global options only valid in facade.
#if defined(CLASP_GLOBAL_OPTIONS) || defined(CLASP_ALL_GROUPS)
#if !defined(CLASP_GLOBAL_OPTIONS)
#define CLASP_GLOBAL_OPTIONS (*this)
#endif
#define SELF CLASP_GLOBAL_OPTIONS
GROUP_BEGIN(SELF)
OPTION(stats, "-s", ARG(implicit("1")->arg("<n>[,<t>]")), "Enable {1=basic|2=full} statistics (<t> for tester)",
    FUN(arg) { auto s = 0u; auto t = 0u;
      return (arg.off() || (arg.get(s, t) && s > 0))
        && SET_LEQ(SELF.stats, s, 2u) && ((!SELF.testerConfig() && t == 0u) || SET_LEQ(SELF.addTesterConfig()->stats, t, 2u));
    },
    FUN(str) { TRUE(str << SELF.stats) && SELF.testerConfig() && SELF.testerConfig()->stats && TRUE(str << SELF.testerConfig()->stats); })
OPTION(parse_ext, "*!",, "Enable extensions in non-aspif input",
    FUN(arg) { bool b; return arg.get(b) && TRUE(SELF.parse.assign(ParserOptions::parse_full, b)); },
    GET((SELF.parse.anyOf(ParserOptions::parse_full))))
OPTION(parse_maxsat, "*!",, "Treat dimacs input as MaxSAT problem",
    FUN(arg) { bool b; return arg.get(b) && TRUE(SELF.parse.assign(ParserOptions::parse_maxsat, b)); },
    GET(as<bool>(SELF.parse.isEnabled(ParserOptions::parse_maxsat))))
GROUP_END(SELF)
#undef CLASP_GLOBAL_OPTIONS
#undef SELF
#endif

//! Solver options (see SolverParams).
#if defined(CLASP_SOLVER_OPTIONS) || defined(CLASP_ALL_GROUPS)
#if !defined(CLASP_SOLVER_OPTIONS)
#define CLASP_SOLVER_OPTIONS (*solver)
#endif
#define SELF CLASP_SOLVER_OPTIONS
GROUP_BEGIN(SELF)
OPTION(opt_strategy, ""  , ARG_EXT(arg("<arg>"),
       ENUM_MAP(OptParams::Type, MAP("bb", type_bb), MAP("usc", type_usc))
       ENUM_MAP(OptParams::BBAlgo, MAP("lin", bb_lin), MAP("hier", bb_hier), MAP("inc", bb_inc), MAP("dec", bb_dec))
       ENUM_MAP(OptParams::UscAlgo, MAP("oll", usc_oll), MAP("one", usc_one), MAP("k", usc_k), MAP("pmres", usc_pmr))
       ENUM_MAP(OptParams::UscOption, MAP("disjoint", usc_disjoint), MAP("succinct", usc_succinct), MAP("stratify", usc_stratify))),
       "Configure optimization strategy [bb]\n"
       "      %A: {bb|usc}[,<tactics>]\n"
       "        bb : Model-guided optimization with <tactics {lin|hier|inc|dec}> [lin]\n"
       "          lin : Basic lexicographical descent\n"
       "          hier: Hierarchical (highest priority criteria first) descent \n"
       "          inc : Hierarchical descent with exponentially increasing steps\n"
       "          dec : Hierarchical descent with exponentially decreasing steps\n"
       "        usc: Core-guided optimization with <tactics>: <relax>[,<opts>]\n"
       "          <relax>: Relaxation algorithm {oll|one|k|pmres}                [oll]\n"
       "            oll    : Use strategy from unclasp\n"
       "            one    : Add one cardinality constraint per core\n"
       "            k[,<n>]: Add cardinality constraints of bounded size ([0]=dynamic)\n"
       "            pmres  : Add clauses of size 3\n"
       "          <opts> : Tactics <list {disjoint|succinct|stratify}>|<mask {0..7}>\n"
       "            disjoint: Disjoint-core preprocessing                    (1)\n"
       "            succinct: No redundant (symmetry) constraints            (2)\n"
       "            stratify: Stratification heuristic for handling weights  (4)",
       STORE(SELF.opt), GET(SELF.opt))
OPTION(opt_usc_shrink, "", ARG_EXT(arg("<arg>"), ENUM_MAP(OptParams::UscTrim,
       MAP("lin", usc_trim_lin), MAP("rgs", usc_trim_rgs), MAP("min", usc_trim_min),
       MAP("exp", usc_trim_exp), MAP("inv", usc_trim_inv), MAP("bin", usc_trim_bin))),
       "Enable core-shrinking in core-guided optimization\n"
       "      %A: <algo>[,<limit> (0=no limit)]|no\n"
       "        <algo> : Use algorithm {lin|inv|bin|rgs|exp|min}\n"
       "          lin  : Forward linear search unsat\n"
       "          inv  : Inverse linear search not unsat\n"
       "          bin  : Binary search\n"
       "          rgs  : Repeated geometric sequence until unsat\n"
       "          exp  : Exponential search until unsat\n"
       "          min  : Linear search for subset minimal core\n"
       "        <limit>: Limit solve calls to 2^<n> conflicts [10]",
      FUN(arg) {
        auto t = as<OptParams::UscTrim>(0); uint32_t n = 0;
        return (arg.off() || arg.get(t, n = 10)) && SET(SELF.opt.trim, as<uint32_t>(t)) && SET(SELF.opt.tLim, n); },
      GET_IF(SELF.opt.trim, as<OptParams::UscTrim>(SELF.opt.trim), SELF.opt.tLim))
OPTION(opt_heuristic, "", ARG_EXT(arg("<list>"), ENUM_MAP(OptParams::Heuristic, MAP("sign", heu_sign), MAP("model", heu_model))),
       "Enable optimization heuristic\n"
       "      %A: {sign|model}|no\n"
       "        sign : Prefer signs minimizing objective\n"
       "        model: Assume literals minimizing objective after each model",
       FUN(arg) { Set<OptParams::Heuristic> h; return (arg.off() || arg.get(h)) && SET(SELF.opt.heus, h.value());},
       GET(Set<OptParams::Heuristic>(SELF.opt.heus)))
OPTION(restart_on_model, "*!",, "Restart after each model\n", STORE_FLAG(SELF.restartOnModel), GET(SELF.restartOnModel))
OPTION(lookahead, "!", ARG_EXT(implicit("atom"), ENUM_MAP(VarType,
       MAP("atom", atom), MAP("body", body), MAP("hybrid", hybrid))),
       "Configure failed-literal detection (fld)\n"
       "      %A: <type>[,<limit>] / Implicit: %I\n"
       "        <type> : Run fld via {atom|body|hybrid} lookahead\n"
       "        <limit>: Disable fld after <limit> applications ([0]=no limit)\n"
       "      --lookahead=atom is default if --no-lookback is used\n", FUN(arg) {
       auto type = as<VarType>(0); auto limit = 0u;
       return (arg.off() || arg.get(type, limit)) && SET(SELF.lookType, as<uint32_t>(type)) && SET_OR_ZERO(SELF.lookOps, limit);},
       GET_IF(SELF.lookType, as<VarType>(SELF.lookType), SELF.lookOps))
OPTION(heuristic, "", ARG_EXT(arg("<heu>"), ENUM_MAP(HeuristicType,
       MAP("berkmin", berkmin), MAP("vmtf", vmtf), MAP("vsids"  , vsids),
       MAP("domain", domain), MAP("unit", unit), MAP("auto", def), MAP("none", none))),
       "Configure decision heuristic\n"
       "      %A: {Berkmin|Vmtf|Vsids|Domain|Unit|None}[,<n>]\n"
       "        Berkmin: Use BerkMin-like heuristic (Check last <n> nogoods [0]=all)\n"
       "        Vmtf   : Use Siege-like heuristic (Move <n> literals to the front [8])\n"
       "        Vsids  : Use Chaff-like heuristic (Use 1.0/0.<n> as decay factor  [95])\n"
       "        Domain : Use domain knowledge in Vsids-like heuristic\n"
       "        Unit   : Use Smodels-like heuristic (Default if --no-lookback)\n"
       "        None   : Select the first free variable", FUN(arg) { auto h = HeuristicType::berkmin; auto n = 0u;
       return arg.get(h, n) && SET(SELF.heuId, as<uint32_t>(h)) && (isLookbackHeuristic(h) || !n) && SET_OR_FILL(SELF.heuristic.param, n);},
       GET(as<HeuristicType>(SELF.heuId), SELF.heuristic.param))
OPTION(init_moms, "*!@2",, "Initialize heuristic with MOMS-score", STORE_FLAG(SELF.heuristic.moms), GET(SELF.heuristic.moms))
OPTION(score_res, "@2" , ARG_EXT(arg("<score>"), ENUM_MAP(HeuParams::Score,
       MAP("auto", score_auto), MAP("min", score_min), MAP("set", score_set), MAP("multiset", score_multi_set))),
       "Resolution score {auto|min|set|multiset}", STORE_U(HeuParams::Score, SELF.heuristic.score), GET(as<HeuParams::Score>(SELF.heuristic.score)))
OPTION(score_other, "@2" , ARG_EXT(arg("<arg>"), ENUM_MAP(HeuParams::ScoreOther,
       MAP("auto", other_auto), MAP("no", other_no), MAP("loop", other_loop), MAP("all", other_all))),
       "Score other learnt nogoods: {auto|no|loop|all}", STORE_U(HeuParams::ScoreOther, SELF.heuristic.other), GET(as<HeuParams::ScoreOther>(SELF.heuristic.other)))
OPTION(sign_def, "@1" , ARG_EXT(arg("<sign>"),
       ENUM_MAP(SolverStrategies::SignHeu, MAP("asp", sign_atom), MAP("pos", sign_pos), MAP("neg", sign_neg), MAP("rnd", sign_rnd))),
       "Default sign: {asp|pos|neg|rnd}", STORE_U(SolverStrategies::SignHeu, SELF.signDef), GET(as<SolverStrategies::SignHeu>(SELF.signDef)))
OPTION(sign_fix, "*!@2",, "Disable sign heuristics and use default signs only", STORE_FLAG(SELF.signFix), GET(SELF.signFix))
OPTION(berk_huang, "*!@2",, "Enable Huang-scoring in Berkmin", STORE_FLAG(SELF.heuristic.huang), GET(SELF.heuristic.huang))
OPTION(vsids_acids, "*!@2",, "Enable acids-scheme in Vsids/Domain", STORE_FLAG(SELF.heuristic.acids), GET(SELF.heuristic.acids))
OPTION(vsids_progress, "@2",, "Enable dynamic decaying scheme in Vsids/Domain\n"
       "      %A: <n>[,<i {1..100}>][,<c>]|(0=disable)\n"
       "        <n> : Set initial decay factor to 1.0/0.<n>\n"
       "        <i> : Set decay update to <i>/100.0      [1]\n"
       "        <c> : Decrease decay every <c> conflicts [5000]",
       FUN(arg) { auto n = 0u; auto i = 0u; auto c = 0u;
       return (arg.off() || arg.get(n = 80u, i = 1u, c = 5000u)) && SET(SELF.heuristic.decay.init, n) &&
         SET_LEQ(SELF.heuristic.decay.bump, i, 100) && SET(SELF.heuristic.decay.freq, c); },
       GET_IF(SELF.heuristic.decay.init, SELF.heuristic.decay.init, SELF.heuristic.decay.bump, SELF.heuristic.decay.freq))
OPTION(nant, "*!@2",, "Prefer negative antecedents of P in heuristic", STORE_FLAG(SELF.heuristic.nant), GET(SELF.heuristic.nant))
OPTION(dom_mod, "@1" , ARG_EXT(arg("<arg>"), ENUM_MAP(HeuParams::DomMod,
       MAP("level", mod_level), MAP("pos", mod_spos), MAP("true", mod_true),
       MAP("neg", mod_sneg), MAP("false", mod_false), MAP("init", mod_init), MAP("factor", mod_factor))
       ENUM_MAP(HeuParams::DomPref, MAP("all", pref_atom), MAP("scc", pref_scc), MAP("hcc", pref_hcc),
       MAP("disj", pref_disj), MAP("opt", pref_min), MAP("show", pref_show))),
       "Default modification for domain heuristic\n"
       "      %A: <mod>[,<pick>]|no\n"
       "        <mod>  : Modifier {level|pos|true|neg|false|init|factor}\n"
       "        <pick> : Apply <mod> to (all | <list {scc|hcc|disj|opt|show}>) atoms",
       FUN(arg) { HeuParams::DomMod modK{}; auto modN = 0u; Set<HeuParams::DomPref> pick;
       return (arg.off() || (arg.get(modK, pick) && SET(modN, as<uint32_t>(modK))) || (arg.get(modN, pick) && modN > 0u && modN < 8u)) &&
         SET(SELF.heuristic.domMod, modN) && SET(SELF.heuristic.domPref, pick.value());},
       FUN(str) { Set<HeuParams::DomMod> mod(SELF.heuristic.domMod); Set<HeuParams::DomPref> pick(SELF.heuristic.domPref);
        TRUE(str << mod) && mod.value() && pick.value() && TRUE(str << pick); })
OPTION(save_progress, "", ARG(implicit("1")->arg("<n>")), "Use RSat-like progress saving on backjumps > %A", STORE_OR_FILL(SELF.saveProgress), GET(SELF.saveProgress))
OPTION(init_watches, "@2", ARG_EXT(arg("<arg>"), ENUM_MAP(SolverStrategies::WatchInit,
       MAP("rnd", watch_rand), MAP("first", watch_first), MAP("least", watch_least))),
       "Watched literal initialization: {rnd|first|least}", STORE_U(SolverStrategies::WatchInit, SELF.initWatches), GET(as<SolverStrategies::WatchInit>(SELF.initWatches)))
OPTION(update_mode, "@2", ARG_EXT(arg("<mode>"), ENUM_MAP(SolverStrategies::UpdateMode,
       MAP("propagate", update_on_propagate), MAP("conflict", update_on_conflict))),
       "Process messages on {propagate|conflict}", STORE_U(SolverStrategies::UpdateMode, SELF.upMode), GET(as<SolverStrategies::UpdateMode>(SELF.upMode)))
OPTION(acyc_prop, "@2", ARG(implicit("1")->arg("{0..1}")), "Use backward inference in acyc propagation",
       FUN(arg) { auto x = 0u; return arg.get(x) && SET_LEQ(SELF.acycFwd, (1u-x), 1u); }, GET(1u-SELF.acycFwd))
OPTION(seed, ""   , ARG(arg("<n>")),"Set random number generator's seed to %A", STORE(SELF.seed), GET(SELF.seed))
OPTION(no_lookback, "*",, "Disable all lookback strategies\n", STORE_FLAG(SELF.search),GET(as<bool>(SELF.search == SolverStrategies::no_learning)))
OPTION(forget_on_step, "", ARG_EXT(arg("<opts>"), ENUM_MAP(SolverParams::Forget,
       MAP("varScores", forget_heuristic), MAP("signs", forget_signs), MAP("lemmaScores", forget_activities), MAP("lemmas", forget_learnts))),
       "Configure forgetting on (incremental) step\n"
       "      %A: <list {varScores|signs|lemmaScores|lemmas}>|<mask {0..15}>|no\n",
       FUN(arg) { Set<SolverParams::Forget> s; return (arg.off() || arg.get(s)) && SET(SELF.forgetSet, s.value()); },
       GET(Set<SolverParams::Forget>(SELF.forgetSet)))
OPTION(strengthen, "!", ARG_EXT(arg("<X>"),
       ENUM_MAP(SolverStrategies::CCMinType, MAP("local", cc_local), MAP("recursive", cc_recursive))
       ENUM_MAP(SolverStrategies::CCMinAntes, MAP("all", all_antes), MAP("short", short_antes), MAP("binary", binary_antes))),
       "Use MiniSAT-like conflict nogood strengthening\n"
       "      %A: <mode>[,<type>][,<bump {yes|no}>]\n"
       "        <mode>: Use {local|recursive} self-subsumption check\n"
       "        <type>: Follow {all|short|binary} antecedents [all]\n"
       "        <bump>: Bump activities of antecedents        [yes]", FUN(arg) {
       auto m = SolverStrategies::cc_local; auto t = SolverStrategies::no_antes; auto b = true;
       return (arg.off() || arg.get(m, t = SolverStrategies::all_antes, b)) && SET(SELF.ccMinAntes, as<uint32_t>(t)) && SET(SELF.ccMinRec, as<uint32_t>(m)) && SET(SELF.ccMinKeepAct, uint32_t(!b)); },
       GET_IF(SELF.ccMinAntes != SolverStrategies::no_antes, as<SolverStrategies::CCMinType>(SELF.ccMinRec), as<SolverStrategies::CCMinAntes>(SELF.ccMinAntes), (!SELF.ccMinKeepAct ? "yes":"no")))
OPTION(otfs, ""   , ARG(implicit("1")->arg("{0..2}")), "Enable {1=partial|2=full} on-the-fly subsumption", STORE_LEQ(SELF.otfs, 2u), GET(SELF.otfs))
OPTION(update_lbd, "!@2" , ARG_EXT(arg("<arg>"), ENUM_MAP(SolverStrategies::LbdMode,
       MAP("less", lbd_updated_less), MAP("glucose", lbd_update_glucose), MAP("pseudo", lbd_update_pseudo))),
       "Configure LBD updates during conflict resolution\n"
       "      %A: <mode {less|glucose|pseudo}>[,<n {0..127}>]\n"
       "        less   : update to X = new LBD   iff X   < previous LBD\n"
       "        glucose: update to X = new LBD   iff X+1 < previous LBD\n"
       "        pseudo : update to X = new LBD+1 iff X   < previous LBD\n"
       "           <n> : Protect updated nogoods on next reduce if X <= <n>",
       FUN(arg) { auto n = SolverStrategies::lbd_fixed; auto m = 0u;
         return (arg.off() || (arg.get(n, m) && n > 0)) && SET(SELF.updateLbd, as<uint32_t>(n)) && SET_LEQ(search->reduce.strategy.protect, m, Clasp::lbd_max);},
       GET_IF(SELF.updateLbd, as<SolverStrategies::LbdMode>(SELF.updateLbd), search->reduce.strategy.protect))
OPTION(update_act, "*@2",, "Enable LBD-based activity bumping", STORE_FLAG(SELF.bumpVarAct), GET(SELF.bumpVarAct))
OPTION(reverse_arcs, "", ARG(implicit("1")->arg("{0..3}")), "Enable ManySAT-like inverse-arc learning", STORE_LEQ(SELF.reverseArcs, 3u), GET(SELF.reverseArcs))
OPTION(contraction, "!@2", ARG_EXT(arg("<arg>"),
       ENUM_MAP(SolverStrategies::CCRepMode, MAP("no", cc_no_replace), MAP("decisionSeq", cc_rep_decision), MAP("allUIP", cc_rep_uip), MAP("dynamic", cc_rep_dynamic))),
       "Configure handling of long learnt nogoods\n"
       "      %A: <n>[,<rep>]\n"
       "        <n>  : Contract nogoods if size > <n> (0=disable)\n"
       "        <rep>: Nogood replacement {no|decisionSeq|allUIP|dynamic} [no]\n", FUN(arg) { auto n = 0u; auto r = SolverStrategies::cc_no_replace;
       return (arg.off() || (arg.get(n, r) && n != 0u)) && SET_OR_FILL(SELF.compress, n) && SET(SELF.ccRepMode, as<uint32_t>(r));},
       GET_IF(SELF.compress, SELF.compress, as<SolverStrategies::CCRepMode>(SELF.ccRepMode)))
OPTION(loops, "", ARG_EXT(arg("<type>"), ENUM_MAP(DefaultUnfoundedCheck::ReasonStrategy,
       MAP("common", common_reason)  , MAP("shared", shared_reason),
       MAP("distinct", distinct_reason), MAP("no", only_reason))),
       "Configure learning of loop nogoods\n"
       "      %A: {common|distinct|shared|no}\n"
       "        common  : Create loop nogoods for atoms in an unfounded set\n"
       "        distinct: Create distinct loop nogood for each atom in an unfounded set\n"
       "        shared  : Create loop formula for a whole unfounded set\n"
       "        no      : Do not learn loop formulas\n", STORE_U(DefaultUnfoundedCheck::ReasonStrategy, SELF.loopRep),
       GET(as<DefaultUnfoundedCheck::ReasonStrategy>(SELF.loopRep)))
GROUP_END(SELF)
#undef CLASP_SOLVER_OPTIONS
#undef SELF
#endif

//! Search-related options (see SolveParams).
#if defined(CLASP_SEARCH_OPTIONS) || defined(CLASP_ALL_GROUPS)
#if !defined(CLASP_SEARCH_OPTIONS)
#define CLASP_SEARCH_OPTIONS (*search)
#endif
#define SELF CLASP_SEARCH_OPTIONS
GROUP_BEGIN(SELF)
OPTION(partial_check, "", ARG(implicit("50")), "Configure partial stability tests\n"
       "      %A: <p>[,<h>]|no / Implicit: %I\n"
       "        <p>: Partial check skip percentage\n"
       "        <h>: Init/update value for high bound ([0]=umax)", FUN(arg) {
       auto p = 0u; auto h = 0u;
       return (arg.off() || (arg.get(p, h) && p)) && SET_LEQ(SELF.fwdCheck.highPct, p, 100u) && SET_OR_ZERO(SELF.fwdCheck.highStep, h);},
       GET_IF(SELF.fwdCheck.highPct, SELF.fwdCheck.highPct, SELF.fwdCheck.highStep))
OPTION(sign_def_disj, "@2", ARG(arg("<sign>")), "Default sign for atoms in disjunctions", STORE_U(SolverStrategies::SignHeu, SELF.fwdCheck.signDef), GET(as<SolverStrategies::SignHeu>(SELF.fwdCheck.signDef)))
OPTION(rand_freq, "!", ARG(arg("<p>")), "Make random decisions with probability %A", FUN(arg) {
       auto f = 0.0;
       return (arg.off() || arg.get(f)) && SET_R(SELF.randProb, as<float>(f), 0.0f, 1.0f);}, GET(SELF.randProb))
OPTION(rand_prob, "", ARG(arg("<n>[,<m>]")), "Do <n> random searches with [<m>=100] conflicts",
       FUN(arg) { auto n1 = 0u; auto n2 = 100u;
       return (arg.off() || (arg.get(n1, n2) && n1)) && SET_OR_FILL(SELF.randRuns, n1) && SET_OR_FILL(SELF.randConf, n2);},
       GET_IF(SELF.randRuns, SELF.randRuns,SELF.randConf))
#undef SELF
//! Options for configuring the restart strategy of a solver.
#if !defined(CLASP_SEARCH_RESTART_OPTIONS)
#define CLASP_SEARCH_RESTART_OPTIONS (search->restart)
#endif
#define SELF CLASP_SEARCH_RESTART_OPTIONS
#if defined(NOTIFY_SUBGROUPS)
GROUP_BEGIN(SELF)
#endif
OPTION(restarts, "!-r", ARG_EXT(arg("<sched>"), ENUM_MAP(RestartSchedule::Keep,
       MAP("n", keep_never), MAP("r", keep_restart),
       MAP("b", keep_block), MAP("br",  keep_always),
       MAP("rb", keep_always))), "Configure restart policy\n"
       "      %A: <type {F|L|x|+}>,<n {1..umax}>[,<args>][,<lim>]\n"
       "        F,<n>    : Run fixed sequence of <n> conflicts\n"
       "        L,<n>    : Run Luby et al.'s sequence with unit length <n>\n"
       "        x,<n>,<f>: Run geometric seq. of <n>*(<f>^i) conflicts  (<f> >= 1.0)\n"
       "        +,<n>,<m>: Run arithmetic seq. of <n>+(<m>*i) conflicts (<m {0..umax}>)\n"
       "        ...,<lim>: Repeat sequence every <lim>+j restarts       (<type> != F)\n"
       "      %A: D,<n>,<K>[,<args>]: Dynamic restarts based on moving LBD average\n"
       "        <n>      : Fast moving average window size\n"
       "        <K>      : Fast margin (restart if fastAvg * <K> > slowAvg)\n"
       "        <L>      : LBD average limit                                [0 = none]\n"
       "        <f>      : Fast moving average type                         [d = SMA]\n"
       "          d      : Default\n"
       "          e|l    : EMA with alpha = 2/(<n>+1) or 1/log2(<n>)\n"
       "          es|ls  : e or l with exponentially decreasing alpha for first samples\n"
       "        <k>      : keep fast moving average on (r)estarts/(b)locks  [n = never]\n"
       "        <s>      : slow moving average type                         [d = CMA]\n"
       "        <w>      : slow moving average window size (<s> != d)       [200*<n>]\n"
       "      no|0       : Disable restarts", FUN(arg) { return (arg.off() && TRUE(SELF.disable())) || arg.get(SELF.rsSched);}, GET(SELF.rsSched))
OPTION(reset_restarts, "@2", ARG_EXT(arg("<arg>"), ENUM_MAP(RestartParams::SeqUpdate,
       MAP("no", seq_continue), MAP("repeat", seq_repeat), MAP("disable", seq_disable))),
       "Update restart seq. on model {no|repeat|disable}",
       STORE_U(RestartParams::SeqUpdate, SELF.upRestart), GET(as<RestartParams::SeqUpdate>(SELF.upRestart)))
OPTION(local_restarts, "*!",, "Use Ryvchin et al.'s local restarts", STORE_FLAG(SELF.cntLocal), GET(SELF.cntLocal))
OPTION(counter_restarts, ""   , ARG(arg("<arg>")), "Use counter implication restarts\n"
       "      %A: (<rate>[,<bump>] | {0|no})\n"
       "      <rate>: Interval in number of restarts\n"
       "      <bump>: Bump factor applied to indegrees",
       FUN(arg) { auto n = 0u; auto m = SELF.counterBump;
       return (arg.off() || (arg.get(n, m) && n > 0)) && SET_OR_FILL(SELF.counterRestart, n) && SET_OR_FILL(SELF.counterBump, m); },
       GET_IF(SELF.counterRestart, SELF.counterRestart, SELF.counterBump))
OPTION(block_restarts, ""   , ARG_EXT(arg("<arg>"), ENUM_MAP(MovingAvg::Type,
       MAP("d", avg_sma), MAP("e", avg_ema), MAP("l", avg_ema_log),
       MAP("es",  avg_ema_smooth), MAP("ls", avg_ema_log_smooth))),
	   "Use glucose-style blocking restarts\n"
       "      %A: <n>[,<R {1.0..5.0}>][,<c>][,<a>]\n"
       "        <n>: Window size for moving average (0=disable blocking)\n"
       "        <R>: Block restart if assignment > average * <R>  [1.4]\n"
       "        <c>: Disable blocking for the first <c> conflicts [10000]\n"
       "        <a>: Type of moving average (see restarts)        [e]\n",
       FUN(arg) { auto n = 0u; auto R = 1.4; auto c = 10000u; auto a = MovingAvg::avg_ema;
       return (arg.off() && TRUE(SELF.block=RestartParams::Block())) || (arg.get(n, R, c, a) && SET_GEQ(SELF.block.window, n, 1) &&
         R >= 1.0 && R <= 5.0 && SET(SELF.block.fscale, as<uint32_t>(R*100.0)) && SET(SELF.block.first, c) && SET(SELF.block.avg, a)); },
       GET_IF(SELF.block.window, SELF.block.window, SELF.block.scale(), SELF.block.first, as<MovingAvg::Type>(SELF.block.avg)))
OPTION(shuffle, "!"  , ARG(arg("<n1>,<n2>")), "Shuffle problem after <n1>+(<n2>*i) restarts\n", FUN(arg) { auto n1 = 0u; auto n2 = 0u;
       return (arg.off() || (arg.get(n1, n2) && n1)) && SET_OR_FILL(SELF.shuffle, n1) && SET_OR_FILL(SELF.shuffleNext, n2);},
       GET_IF(SELF.shuffle, SELF.shuffle, SELF.shuffleNext))
#if defined(NOTIFY_SUBGROUPS)
GROUP_END(SELF)
#endif
#undef SELF
#undef CLASP_SEARCH_RESTART_OPTIONS
//! Options for configuring the deletion strategy of a solver.
#if !defined(CLASP_SEARCH_REDUCE_OPTIONS)
#define CLASP_SEARCH_REDUCE_OPTIONS (search->reduce)
#endif
#define SELF CLASP_SEARCH_REDUCE_OPTIONS
#if defined(NOTIFY_SUBGROUPS)
GROUP_BEGIN(SELF)
#endif
OPTION(deletion, "!-d", ARG_EXT(defaultsTo("basic,75,activity", true), ENUM_MAP(ReduceStrategy::Algorithm,
       MAP("basic", reduce_linear), MAP("sort", reduce_stable),
       MAP("ipSort", reduce_sort) , MAP("ipHeap", reduce_heap))
       ENUM_MAP(ReduceStrategy::Score, MAP("activity", score_act), MAP("lbd", score_lbd), MAP("mixed", score_both))),
       "Configure deletion algorithm [%D]\n"
       "      %A: <algo>[,<n {1..100}>][,<sc>]\n"
       "        <algo>: Use {basic|sort|ipSort|ipHeap} algorithm\n"
       "        <n>   : Delete at most <n>%% of nogoods on reduction    [75]\n"
       "        <sc>  : Use {activity|lbd|mixed} nogood scores    [activity]\n"
       "      no      : Disable nogood deletion", FUN(arg){
       auto algo = ReduceStrategy::reduce_linear; auto n = 75u; auto sc = ReduceStrategy::score_act;
       return (arg.off() && TRUE(SELF.disable())) || (arg.get(algo, n, sc) && SET(SELF.strategy.algo, as<uint32_t>(algo)) &&
         SET_R(SELF.strategy.fReduce, n, 1, 100) && SET(SELF.strategy.score, as<uint32_t>(sc)));},
       GET_IF(SELF.strategy.fReduce, as<ReduceStrategy::Algorithm>(SELF.strategy.algo), SELF.strategy.fReduce,as<ReduceStrategy::Score>(SELF.strategy.score)))
OPTION(del_grow, "!",, "Configure size-based deletion policy\n"
       "      %A: <f>[,<g>][,<sched>] (<f> >= 1.0)\n"
       "        <f>     : Keep at most T = X*(<f>^i) learnt nogoods with X being the\n"
       "                  initial limit and i the number of times <sched> fired\n"
       "        <g>     : Stop growth once T > P*<g> (0=no limit)      [3.0]\n"
       "        <sched> : Set grow schedule (<type {F|L|x|+}>) [grow on restart]", FUN(arg){ auto f = 0.0; double g = 3.0; auto sc = ScheduleStrategy::def();
       return (arg.off() && TRUE(SELF.growSched = ScheduleStrategy::none(), SELF.fGrow = 0.0f)) || (
         arg.get(f, g, sc) && SET_R(SELF.fGrow, as<float>(f), 1.0f, FLT_MAX) && SET_R(SELF.fMax, as<float>(g), 0.0f, FLT_MAX) && TRUE(SELF.growSched=sc));},
       FUN(str) { if (SELF.fGrow == 0.0f) str<<off; else { str<<SELF.fGrow<<SELF.fMax; if (!SELF.growSched.disabled()) str<<SELF.growSched;}})
OPTION(del_cfl, "!", ARG(arg("<sched>")), "Configure conflict-based deletion policy\n"
       "      %A:   <type {F|L|x|+}>,<args>... (see restarts)", FUN(arg){
       return (arg.off() && TRUE(SELF.cflSched=ScheduleStrategy::none())) || arg.get(SELF.cflSched); }, GET(SELF.cflSched))
OPTION(del_init, ""  , ARG(defaultsTo("3.0", true)), "Configure initial deletion limit\n"
       "      %A: <f>[,<n>,<o>] (<f> > 0)\n"
       "        <f>    : Set initial limit to P=estimated problem size/<f> [%D]\n"
       "        <n>,<o>: Clamp initial limit to the range [<n>,<n>+<o>]" , FUN(arg) { double f; auto lo = 10u; auto hi = UINT32_MAX;
       return arg.get(f, lo, hi) && f > 0.0 && (SELF.fInit = as<float>(1.0 / f)) > 0 && SET_OR_FILL(SELF.initRange.lo, lo) && SET_OR_FILL(SELF.initRange.hi, (uint64_t(hi)+SELF.initRange.lo));},
       GET_IF(SELF.fInit, 1.0/SELF.fInit, SELF.initRange.lo, SELF.initRange.hi - SELF.initRange.lo))
OPTION(del_estimate, "", ARG(arg("0..3")->implicit("1")), "Use estimated problem complexity in limits", STORE_LEQ(SELF.strategy.estimate, 3u), GET(SELF.strategy.estimate))
OPTION(del_max, "!", ARG(arg("<n>,<X>")), "Keep at most <n> learnt nogoods taking up to <X> MB", FUN(arg) { auto n = UINT32_MAX; auto mb = 0u;
       return (arg.off() || arg.get(n, mb)) && SET_GEQ(SELF.maxRange, n, 1u) && SET(SELF.memMax, mb);}, GET(SELF.maxRange, SELF.memMax))
OPTION(del_glue, "",, "Configure glue clause handling\n"
       "      %A: <n {0..15}>[,<m {0|1}>]\n"
       "        <n>: Do not delete nogoods with LBD <= <n>\n"
       "        <m>: Count (0) or ignore (1) glue clauses in size limit [0]", FUN(arg) { auto lbd = 0u; auto m = 0u;
       return arg.get(lbd, m) && SET(SELF.strategy.glue, lbd) && SET(SELF.strategy.noGlue, m);}, GET(SELF.strategy.glue, SELF.strategy.noGlue))
OPTION(del_on_restart, "", ARG(arg("<n>")), "Delete %A%% of learnt nogoods on each restart", STORE_LEQ(SELF.strategy.fRestart, 100u), GET(SELF.strategy.fRestart))
#if defined(NOTIFY_SUBGROUPS)
GROUP_END(SELF)
#endif
#undef SELF
#undef CLASP_SEARCH_REDUCE_OPTIONS
GROUP_END(CLASP_SEARCH_OPTIONS)
#undef CLASP_SEARCH_OPTIONS
#endif

//! ASP-front-end options stored in an Clasp::Asp::LogicProgram::AspOptions object.
#if defined(CLASP_ASP_OPTIONS) || defined(CLASP_ALL_GROUPS)
#if !defined(CLASP_ASP_OPTIONS)
#define CLASP_ASP_OPTIONS (this->asp)
#endif
#define SELF CLASP_ASP_OPTIONS
GROUP_BEGIN(SELF)
OPTION(trans_ext, "!", ARG_EXT(arg("<mode>"), ENUM_MAP(Asp::LogicProgram::ExtendedRuleMode,
       MAP("no"    , mode_native)          , MAP("all" , mode_transform),
       MAP("choice", mode_transform_choice), MAP("card", mode_transform_card),
       MAP("weight", mode_transform_weight), MAP("scc" , mode_transform_scc),
       MAP("integ" , mode_transform_integ) , MAP("dynamic", mode_transform_dynamic))),
       "Configure handling of extended rules [no]\n"
       "      %A: {all|choice|card|weight|integ|dynamic}\n"
       "        all    : Transform all extended rules to basic rules\n"
       "        choice : Transform choice rules, but keep cardinality and weight rules\n"
       "        card   : Transform cardinality rules, but keep choice and weight rules\n"
       "        weight : Transform cardinality and weight rules, but keep choice rules\n"
       "        scc    : Transform \"recursive\" cardinality and weight rules\n"
       "        integ  : Transform cardinality integrity constraints\n"
       "        dynamic: Transform \"simple\" extended rules, but keep more complex ones", STORE(SELF.erMode), GET(as<Asp::LogicProgram::ExtendedRuleMode>(SELF.erMode)))
OPTION(eq, "", ARG(arg("<n>")), "Configure equivalence preprocessing\n"
       "      Run for at most %A iterations (-1=run to fixpoint)", STORE_OR_FILL(SELF.iters), GET(SELF.iters))
OPTION(backprop,"*!@1",, "Use backpropagation in ASP-preprocessing", STORE_FLAG(SELF.backprop), GET(SELF.backprop))
OPTION(supp_models, "*@1",, "Compute supported models", STORE_FLAG(SELF.suppMod), GET(SELF.suppMod))
OPTION(no_ufs_check, "*@1",, "Disable unfounded set check", STORE_FLAG(SELF.noSCC), GET(SELF.noSCC))
OPTION(no_gamma, "*@1",, "Do not add gamma rules for non-hcf disjunctions", STORE_FLAG(SELF.noGamma), GET(SELF.noGamma))
OPTION(eq_dfs, "*@2",, "Enable df-order in eq-preprocessing", STORE_FLAG(SELF.dfOrder), GET(SELF.dfOrder))
OPTION(dlp_old_map, "*@3",, "Enable old mapping for disjunctive LPs", STORE_FLAG(SELF.oldMap), GET(SELF.oldMap))
GROUP_END(SELF)
#undef CLASP_ASP_OPTIONS
#undef SELF
#endif

//! Options for the solving algorithm (see Clasp::SolveOptions)
#if defined(CLASP_SOLVE_OPTIONS) || defined(CLASP_ALL_GROUPS)
#if !defined(CLASP_SOLVE_OPTIONS)
#define CLASP_SOLVE_OPTIONS (this->solve)
#endif
#define SELF CLASP_SOLVE_OPTIONS
GROUP_BEGIN(SELF)
OPTION(solve_limit, "@1", ARG(arg("<n>[,<m>]")), "Stop search after <n> conflicts or <m> restarts\n", FUN(arg) {
       auto n = UINT32_MAX; auto m = UINT32_MAX;
       return (arg.get(n, m) || arg.off()) && TRUE(SELF.limit=SolveLimits(n == UINT32_MAX ? UINT64_MAX : n, m == UINT32_MAX ? UINT64_MAX : m));},
       GET(as<uint32_t>(Clasp::clamp(SELF.limit.conflicts, 0u, UINT32_MAX)),as<uint32_t>(Clasp::clamp(SELF.limit.restarts, 0u,UINT32_MAX))))
#if CLASP_HAS_THREADS
OPTION(parallel_mode, "-t", ARG_EXT(arg("<arg>"), ENUM_MAP(SolveOptions::Algorithm::SearchMode,
       MAP("compete", mode_compete), MAP("split", mode_split))),
       "Run parallel search with given number of threads\n"
       "      %A: <n {1..64}>[,<mode {compete|split}>]\n"
       "        <n>   : Number of threads to use in search\n"
       "        <mode>: Run competition or splitting based search [compete]\n", FUN(arg){
       auto n = 0u; auto mode = SolveOptions::Algorithm::mode_compete;
       return arg.get(n, mode) && SET_R(SELF.algorithm.threads, n, 1u, 64u) && SET(SELF.algorithm.mode, mode);},
       GET(SELF.algorithm.threads, as<SolveOptions::Algorithm::SearchMode>(SELF.algorithm.mode)))
OPTION(global_restarts, "@1", ARG(arg("<X>")), "Configure global restart policy\n"
       "      %A: <n>[,<sched>]\n"
       "        <n> : Maximal number of global restarts (0=disable)\n"
       "     <sched>: Restart schedule [x,100,1.5] (<type {F|L|x|+}>)\n", FUN(arg) {
       return (arg.off() && TRUE(SELF.restarts = SolveOptions::GRestarts())) || (arg.get(SELF.restarts.maxR, SELF.restarts.sched = ScheduleStrategy())
         && SELF.restarts.maxR);},
       GET_IF(SELF.restarts.maxR, SELF.restarts.maxR, SELF.restarts.sched))
OPTION(distribute, "!@1", ARG_EXT(defaultsTo("conflict,global,4"),
       ENUM_MAP(Distributor::Policy::Types, MAP("all", all), MAP("short", implicit), MAP("conflict", conflict), MAP("loop" , loop))
       ENUM_MAP(SolveOptions::Distribution::Mode, MAP("global", mode_global), MAP("local", mode_local))),
       "Configure nogood distribution [%D]\n"
       "      %A: <type>[,<mode>][,<lbd {0..127}>][,<size>]\n"
       "        <type> : Distribute {all|short|conflict|loop} nogoods\n"
       "        <mode> : Use {global|local} distribution   [global]\n"
       "        <lbd>  : Distribute only if LBD  <= <lbd>  [4]\n"
       "        <size> : Distribute only if size <= <size> [-1]",
       FUN(arg) { auto type = Distributor::Policy::no; auto mode = SolveOptions::Distribution::mode_global; auto lbd = 4u; auto size = UINT32_MAX;
       return (arg.off() && TRUE(SELF.distribute.policy() = Distributor::Policy(0, 0, 0))) || ((arg.get(type, mode, lbd, size) || arg.get(type, lbd, size)) &&
         SET(SELF.distribute.types, as<uint32_t>(type)) && SET(SELF.distribute.mode, as<uint32_t>(mode)) && SET(SELF.distribute.lbd, lbd) && SET_OR_FILL(SELF.distribute.size, size));},
       GET_IF(SELF.distribute.types, as<Distributor::Policy::Types>(SELF.distribute.types), as<SolveOptions::Distribution::Mode>(SELF.distribute.mode), SELF.distribute.lbd, SELF.distribute.size))
OPTION(integrate, "@1", ARG_EXT(defaultsTo("gp", true),
       ENUM_MAP(SolveOptions::Integration::Filter,
       MAP("all", filter_no), MAP("gp", filter_gp),
       MAP("unsat", filter_sat), MAP("active", filter_heuristic))
       ENUM_MAP(SolveOptions::Integration::Topology,
       MAP("all" , topo_all) , MAP("ring" , topo_ring),
       MAP("cube", topo_cube), MAP("cubex", topo_cubex))),
       "Configure nogood integration [%D]\n"
       "      %A: <pick>[,<n>][,<topo>]\n"
       "        <pick>: Add {all|unsat|gp(unsat wrt guiding path)|active} nogoods\n"
       "        <n>   : Always keep at least last <n> integrated nogoods   [1024]\n"
       "        <topo>: Accept nogoods from {all|ring|cube|cubex} peers    [all]\n", FUN(arg) {
       auto pick = SolveOptions::Integration::filter_no; auto n = 1024u; auto topo = SolveOptions::Integration::topo_all;
       return arg.get(pick, n, topo) && SET(SELF.integrate.filter, as<uint32_t>(pick)) && SET_OR_FILL(SELF.integrate.grace, n) && SET(SELF.integrate.topo, as<uint32_t>(topo));},
       GET(as<SolveOptions::Integration::Filter>(SELF.integrate.filter), SELF.integrate.grace, as<SolveOptions::Integration::Topology>(SELF.integrate.topo)))
#endif
OPTION(enum_mode, "-e", ARG_EXT(defaultsTo("auto", true), ENUM_MAP(SolveOptions::EnumType,
       MAP("bt", enum_bt), MAP("record", enum_record), MAP("domRec", enum_dom_record),
       MAP("brave", enum_brave), MAP("cautious", enum_cautious), MAP("query", enum_query),
       MAP("auto", enum_auto), MAP("user", enum_user))),
       "Configure enumeration algorithm [%D]\n"
       "      %A: {bt|record|brave|cautious|auto}\n"
       "        bt      : Backtrack decision literals from solutions\n"
       "        record  : Add nogoods for computed solutions\n"
       "        domRec  : Add nogoods over true domain atoms\n"
       "        brave   : Compute brave consequences (union of models)\n"
       "        cautious: Compute cautious consequences (intersection of models)\n"
       "        auto    : Use bt for enumeration and record for optimization", STORE(SELF.enumMode), GET(SELF.enumMode))
OPTION(project, "!", ARG_EXT(arg("<arg>")->implicit("auto,3"), ENUM_MAP(ProjectMode,
       MAP("auto", implicit), MAP("show", output), MAP("project", project))),
       "Enable projective solution enumeration\n"
       "      %A: {show|project|auto}[,<bt {0..3}>] (Implicit: %I)\n"
       "        Project to atoms in show or project directives, or\n"
       "        select depending on the existence of a project directive\n"
       "      <bt> : Additional options for enumeration algorithm 'bt'\n"
       "        Use activity heuristic (1) when selecting backtracking literal\n"
       "        and/or progress saving (2) when retracting solution literals",
       FUN(arg) { auto m = ProjectMode::implicit; auto p = 0u;
         return ( arg.off() || (arg.get(p) && TRUE(p = p | (p != 0))) || (arg.get(m, p) && TRUE(p = (p<<1)|1)) ) &&
           SET(SELF.proMode, m) && SET_LEQ(SELF.project, p, 7u);},
       GET_IF(SELF.project, SELF.proMode, SELF.project >> 1))
OPTION(models, "-n", ARG(arg("<n>")), "Compute at most %A models (0 for all)\n", STORE(SELF.numModels), GET(SELF.numModels))
OPTION(opt_mode, "", ARG_EXT(arg("<arg>"), ENUM_MAP(MinimizeMode,
       MAP("opt" , optimize), MAP("enum"  , enumerate),
       MAP("optN", enum_opt) , MAP("ignore", ignore))),
       "Configure optimization algorithm\n"
       "      %A: <mode {opt|enum|optN|ignore}>[,<bound>...]\n"
       "        opt   : Find optimal model\n"
       "        enum  : Find models with costs <= <bound>\n"
       "        optN  : Find optimum, then enumerate optimal models\n"
       "        ignore: Ignore optimize statements\n"
       "      <bound> : Set initial bound for objective function(s)",
       FUN(arg) { auto m = MinimizeMode::optimize; SumVec B; return arg.get(m, B) && SET(SELF.optMode, m) && TRUE(SELF.optBound.swap(B)); },
       FUN(str) { str << SELF.optMode; if (!SELF.optBound.empty()) str << SELF.optBound; })
OPTION(opt_stop, "", ARG(arg("<bound>...")), "Stop optimization on model with cost <= <bound> \n",
       FUN(arg) { SumVec B; return (arg.get(B) || arg.off()) && TRUE(SELF.optStop = B); },
       GET_IF(not SELF.optStop.empty(), SELF.optStop))
GROUP_END(SELF)
#undef CLASP_SOLVE_OPTIONS
#undef SELF
#endif

#undef GROUP_BEGIN
#undef GROUP_END
#undef OPTION
#undef NOTIFY_SUBGROUPS
#undef ARG
#undef ARG_EXT
#undef CLASP_ALL_GROUPS
