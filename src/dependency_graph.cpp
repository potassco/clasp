//
// Copyright (c) 2010-present Benjamin Kaufmann
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
#include <clasp/dependency_graph.h>

#include <clasp/clause.h>
#include <clasp/solve_algorithms.h>
#include <clasp/solver.h>
#include <clasp/util/timer.h>

#include <potassco/bits.h>
#include <potassco/error.h>

#include <span>

namespace Clasp {
SolveTestEvent::SolveTestEvent(const Solver& s, uint32_t a_hcc, bool part)
    : SolveEvent(this, s, verbosity_max)
    , result(-1)
    , hcc(a_hcc)
    , partial(part) {
    confDelta   = s.stats.conflicts;
    choiceDelta = s.stats.choices;
    time        = 0.0;
}
uint64_t SolveTestEvent::choices() const { return solver->stats.choices - choiceDelta; }
uint64_t SolveTestEvent::conflicts() const { return solver->stats.conflicts - confDelta; }
namespace Asp {
/////////////////////////////////////////////////////////////////////////////////////////
// class PrgDepGraph
/////////////////////////////////////////////////////////////////////////////////////////
PrgDepGraph::PrgDepGraph(NonHcfMapType m) {
    // add sentinel atom needed for disjunctions
    createAtom(lit_false, PrgNode::no_scc);
    uint32_t empty[1] = {id_max};
    initAtom(sentinel_atom, 0, empty, 0);
    seenComponents_ = 0;
    mapType_        = static_cast<uint32_t>(m);
    stats_          = nullptr;
}

PrgDepGraph::~PrgDepGraph() {
    for (auto& atom : atoms_) { delete[] atom.adj; }
    for (auto& body : bodies_) { delete[] body.adj; }
    while (not components_.empty()) {
        delete components_.back();
        components_.pop_back();
    }
}
static bool relevantPrgAtom(const Solver& s, const PrgAtom* a) {
    return not a->ignoreScc() && a->inUpper() && a->scc() != PrgNode::no_scc && not s.isFalse(a->literal());
}
static bool relevantPrgBody(const Solver& s, const PrgBody* b) { return not s.isFalse(b->literal()); }

// Creates a positive-body-atom-dependency graph (PBADG)
// The PBADG contains a node for each atom A of a non-trivial SCC and
// a node for each body B, s.th. there is a non-trivially connected atom A with
// B in body(A).
// Pre : b->seen() = 1 for all new and relevant bodies b
// Post: b->seen() = 0 for all bodies that were added to the PBADG
void PrgDepGraph::addSccs(const LogicProgram& prg, const AtomList& sccAtoms, const NonHcfSet& nonHcfs) {
    // Pass 1: Create graph atom nodes and estimate number of bodies
    atoms_.reserve(atoms_.size() + sccAtoms.size());
    auto           numBodies = 0u;
    SharedContext& ctx       = *prg.ctx();
    for (auto* atom : sccAtoms) {
        if (relevantPrgAtom(*ctx.master(), atom)) {
            // add graph atom node and store link between program node and graph node for later lookup
            atom->resetId(createAtom(atom->literal(), atom->scc()), true);
            // atom is defined by more than just a bunch of clauses
            ctx.setFrozen(atom->var(), true);
            numBodies += atom->numSupports();
        }
    }
    // Pass 2: Init atom nodes and create body nodes
    VarVec adj, ext;
    bodies_.reserve(bodies_.size() + numBodies / 2);
    PrgBody* prgBody;
    for (auto* atom : sccAtoms) {
        if (relevantPrgAtom(*ctx.master(), atom)) {
            uint32_t prop = 0;
            for (auto s : atom->supports()) {
                assert(s.isBody() || s.isDisj());
                NodeId bId = PrgNode::no_node;
                if (s.isBody() && not s.isGamma()) {
                    prgBody = prg.getBody(s.node());
                    bId     = relevantPrgBody(*ctx.master(), prgBody) ? addBody(prg, prgBody) : PrgNode::no_node;
                }
                else if (s.isDisj()) {
                    PrgDisj* prgDis  = prg.getDisj(s.node());
                    bId              = addDisj(prg, prgDis);
                    prop            |= AtomNode::property_in_disj;
                }
                if (bId != PrgNode::no_node) {
                    if (not bodies_[bId].seen()) {
                        bodies_[bId].seen(true);
                        adj.push_back(bId);
                    }
                    if (s.isChoice()) {
                        // mark atom as in choice
                        prop |= AtomNode::property_in_choice;
                    }
                }
            }
            auto nPred = size32(adj);
            for (auto dep : atom->deps()) {
                if (not dep.sign()) {
                    prgBody = prg.getBody(dep.var());
                    if (relevantPrgBody(*ctx.master(), prgBody) && prgBody->scc(prg) == atom->scc()) {
                        if (NodeId bodyId = addBody(prg, prgBody); not bodies_[bodyId].extended()) {
                            adj.push_back(bodyId);
                        }
                        else {
                            ext.push_back(bodyId);
                            ext.push_back(bodies_[bodyId].findPred(atom->id()));
                            prop |= AtomNode::property_in_ext;
                        }
                    }
                }
            }
            if (not ext.empty()) {
                adj.push_back(id_max);
                adj.insert(adj.end(), ext.begin(), ext.end());
            }
            adj.push_back(id_max);
            initAtom(atom->id(), prop, adj, nPred);
            adj.clear();
            ext.clear();
        }
    }
    if (not nonHcfs.empty() && stats_ == nullptr && nonHcfs.config && nonHcfs.config->context().stats) {
        enableNonHcfStats(nonHcfs.config->context().stats, prg.isIncremental());
    }
    // "update" existing non-hcf components
    for (auto* hcc : components_) { hcc->update(ctx); }
    // add new non-hcf components
    for (uint32_t hcc = seenComponents_; auto x : nonHcfs.view(seenComponents_)) {
        addNonHcf(hcc++, ctx, nonHcfs.config, x);
    }
    seenComponents_ = size32(nonHcfs);
}

uint32_t PrgDepGraph::createAtom(Literal lit, uint32_t aScc) {
    auto id = size32(atoms_);
    atoms_.push_back(AtomNode());
    AtomNode& ua = atoms_.back();
    ua.lit       = lit;
    ua.scc       = aScc;
    return id;
}

void PrgDepGraph::initAtom(uint32_t id, uint32_t prop, VarView adj, uint32_t numPreds) {
    AtomNode& ua = atoms_[id];
    ua.setProperties(prop);
    ua.adj         = new NodeId[adj.size()];
    ua.sep         = ua.adj + numPreds;
    NodeId*  sExt  = ua.adj;
    NodeId*  sSame = sExt + numPreds;
    uint32_t aScc  = ua.scc;
    for (auto bId : adj.subspan(0, numPreds)) {
        BodyNode& bn = bodies_[bId];
        if (bn.scc != aScc) {
            *sExt++ = bId;
        }
        else {
            *--sSame = bId;
        }
        bn.seen(false);
    }
    std::reverse(sSame, ua.adj + numPreds);
    std::ranges::copy(adj.subspan(numPreds), ua.sep);
}

uint32_t PrgDepGraph::createBody(const PrgBody* b, uint32_t bScc) {
    auto id = size32(bodies_);
    bodies_.push_back(BodyNode(b, bScc));
    return id;
}

// Creates and initializes a body node for the given body b.
uint32_t PrgDepGraph::addBody(const LogicProgram& prg, PrgBody* b) {
    if (b->seen()) { // first time we see this body -
        VarVec   preds, atHeads;
        uint32_t bScc = b->scc(prg);
        NodeId   bId  = createBody(b, bScc);
        addPreds(prg, b, bScc, preds);
        addHeads(prg, b, atHeads);
        initBody(bId, preds, atHeads);
        b->resetId(bId, false);
        prg.ctx()->setFrozen(b->var(), true);
    }
    return b->id();
}

// Adds all relevant predecessors of 'b' to preds.
// The returned list looks like this:
// [[B], a1, [w1], ..., aj, [wj], id_max, l1, [w1], ..., lk, [wk], id_max], where
// 'B' is the bound of b (only for card/weight rules),
// 'ai' is a positive predecessor from bScc,
// 'wi' is the weight of 'ai' (only for weight rules), and
// 'li' is a literal of a subgoal from some other scc (only for cardinality/weight rules)
void PrgDepGraph::addPreds(const LogicProgram& prg, const PrgBody* b, uint32_t bScc, VarVec& preds) {
    if (bScc == PrgNode::no_scc) {
        preds.clear();
        return;
    }
    const bool weights = b->type() == BodyType::sum;
    for (uint32_t n = 0; auto g : b->goals()) {
        if (g.sign()) {
            break;
        }
        auto* pred = prg.getAtom(g.var());
        if (relevantPrgAtom(*prg.ctx()->master(), pred) && pred->scc() == bScc) {
            preds.push_back(pred->id());
            if (weights) {
                preds.push_back(static_cast<Var_t>(b->weight(n)));
            }
        }
        ++n;
    }
    if (b->type() != BodyType::normal) {
        preds.insert(preds.begin(), static_cast<Var_t>(b->bound()));
        preds.push_back(id_max);
        for (uint32_t n = 0; auto g : b->goals()) {
            PrgAtom* pred = prg.getAtom(g.var());
            bool     ext  = g.sign() || pred->scc() != bScc;
            Literal  lit  = g.sign() ? ~pred->literal() : pred->literal();
            if (ext && not prg.ctx()->master()->isFalse(lit)) {
                preds.push_back(lit.rep());
                if (weights) {
                    preds.push_back(static_cast<Var_t>(b->weight(n)));
                }
            }
            ++n;
        }
    }
    preds.push_back(id_max);
}

// Splits the heads of b into atoms and disjunctions.
// Disjunctions are flattened to sentinel-enclosed atom-lists.
uint32_t PrgDepGraph::addHeads(const LogicProgram& prg, const PrgBody* b, VarVec& heads) {
    for (auto e : b->heads()) {
        if (e.isAtom() && not e.isGamma()) {
            PrgAtom* a = prg.getAtom(e.node());
            if (relevantPrgAtom(*prg.ctx()->master(), a)) {
                heads.push_back(a->id());
            }
        }
        else if (e.isDisj()) {
            assert(prg.getDisj(e.node())->inUpper() && prg.getDisj(e.node())->numSupports() == 1);
            PrgDisj* d = prg.getDisj(e.node());
            // flatten disjunction and enclose in sentinels
            heads.push_back(sentinel_atom);
            getAtoms(prg, d, heads);
            heads.push_back(sentinel_atom);
        }
    }
    return size32(heads);
}

// Adds the atoms from the given disjunction to atoms and returns the disjunction's scc.
uint32_t PrgDepGraph::getAtoms(const LogicProgram& prg, const PrgDisj* d, VarVec& atoms) {
    uint32_t scc = PrgNode::no_scc;
    for (auto id : d->atoms()) {
        auto* a = prg.getAtom(id);
        if (relevantPrgAtom(*prg.ctx()->master(), a)) {
            assert(scc == PrgNode::no_scc || scc == a->scc());
            atoms.push_back(a->id());
            scc = a->scc();
        }
    }
    return scc;
}

// Initializes preds and succs lists of the body node with the given id.
void PrgDepGraph::initBody(uint32_t id, VarView preds, VarView atHeads) {
    BodyNode* bn     = &bodies_[id];
    uint32_t  nSuccs = size32(atHeads);
    bn->adj          = new NodeId[nSuccs + preds.size()];
    bn->sep          = bn->adj + nSuccs;
    NodeId*  sSame   = bn->adj;
    NodeId*  sExt    = sSame + nSuccs;
    uint32_t bScc    = bn->scc;
    uint32_t disj    = 0;
    for (auto it = atHeads.begin(), end = atHeads.end(); it != end;) {
        if (*it) {
            auto hScc = getAtom(*it).scc;
            if (hScc == bScc) {
                *sSame++ = *it++;
            }
            else {
                *--sExt = *it++;
            }
        }
        else {
            auto hScc = getAtom(it[1]).scc;
            ++disj;
            if (hScc == bScc) {
                *sSame++ = *it++;
                while ((*sSame++ = *it++)) { ; }
            }
            else {
                *--sExt = *it++;
                while ((*--sExt = *it++)) { ; }
            }
        }
    }
    std::ranges::copy(preds, bn->sep);
    bn->sep += bn->extended();
    if (disj) {
        bodies_[id].data |= BodyNode::flag_has_delta;
    }
}

uint32_t PrgDepGraph::addDisj(const LogicProgram& prg, PrgDisj* d) {
    assert(d->inUpper() && d->numSupports() == 1);
    if (d->seen()) { // first time we see this disjunction
        PrgBody* prgBody = prg.getBody(d->support().node());
        uint32_t bId     = PrgNode::no_node;
        if (relevantPrgBody(*prg.ctx()->master(), prgBody)) {
            bId = addBody(prg, prgBody);
        }
        d->resetId(bId, false);
    }
    return d->id();
}

void PrgDepGraph::addNonHcf(uint32_t id, SharedContext& ctx, Configuration* config, uint32_t scc) {
    VarVec sccAtoms, sccBodies;
    // get all atoms from scc
    for (auto i : irange(numAtoms())) {
        if (getAtom(i).scc == scc) {
            sccAtoms.push_back(i);
            atoms_[i].set(AtomNode::property_in_non_hcf);
        }
    }
    // get all bodies defining an atom in scc
    const Solver& generator = *ctx.master();
    for (auto atomId : sccAtoms) {
        const AtomNode& a = getAtom(atomId);
        for (auto bId : a.bodies()) {
            BodyNode& body = bodies_[bId];
            if (not body.seen()) {
                POTASSCO_ASSERT(generator.value(body.lit.var()) != value_free || not generator.seen(body.lit));
                sccBodies.push_back(bId);
                body.seen(true);
            }
        }
    }
    for (auto bodyId : sccBodies) { bodies_[bodyId].seen(false); }
    components_.push_back(new NonHcfComponent(id, *this, ctx, config, scc, sccAtoms, sccBodies));
    if (stats_) {
        stats_->addHcc(*components_.back());
    }
}
void PrgDepGraph::simplify(const Solver& s) {
    const bool shared = s.sharedContext()->isShared();
    auto       j      = components_.begin();
    for (auto& component : components_) {
        bool ok = component->simplify(s);
        if (not shared) {
            if (ok) {
                *j++ = component;
            }
            else {
                if (stats_) {
                    stats_->removeHcc(*component);
                }
                delete component;
            }
        }
    }
    if (not shared) {
        components_.erase(j, components_.end());
    }
}
PrgDepGraph::NonHcfStats* PrgDepGraph::enableNonHcfStats(uint32_t level, bool inc) {
    if (not stats_) {
        stats_ = std::make_unique<NonHcfStats>(*this, level, inc);
    }
    return stats_.get();
}
/////////////////////////////////////////////////////////////////////////////////////////
// class PrgDepGraph::NonHcfComponent::ComponentMap
/////////////////////////////////////////////////////////////////////////////////////////
class PrgDepGraph::NonHcfComponent::ComponentMap {
public:
    ComponentMap() = default;
    struct Mapping {
        explicit Mapping(NodeId id) : node(id) {
            static_assert(sizeof(Mapping) == sizeof(uint64_t), "Invalid padding!");
        }
        uint32_t node;         // node id in dep-graph of generator program P
        uint32_t var : 30 {0}; // var in tester solver
        uint32_t ext : 2 {0};  // additional data
        // Atom
        [[nodiscard]] bool    disj() const { return ext != 0u; }
        [[nodiscard]] bool    hasTp() const { return ext == 2u; }
        [[nodiscard]] Literal up() const { return posLit(var); }
        [[nodiscard]] Literal hp() const {
            assert(disj());
            return posLit(var + 1);
        }
        [[nodiscard]] Literal tp() const {
            assert(disj());
            return posLit((var + 2) * static_cast<uint32_t>(hasTp()));
        }
        // Body
        [[nodiscard]] Literal fb() const { return {var, (ext & 1u) != 0u}; }
        [[nodiscard]] bool    eq() const { return ext != 0u; }

        bool operator==(const Mapping& other) const { return node == other.node; }
        auto operator<=>(const Mapping& other) const { return node <=> other.node; }
    };
    using SccGraph = PrgDepGraph;
    using NodeMap  = PodVector_t<Mapping>;
    using MapIt    = NodeMap::iterator;
    using MapIt_c  = NodeMap::const_iterator;
    using MapSpan  = SpanView<Mapping>;

    void addVars(Solver& generator, const SccGraph& dep, VarView atoms, VarView bodies, SharedContext& comp);
    void addAtomConstraints(SharedContext& comp);
    void addBodyConstraints(const Solver& generator, const SccGraph& dep, uint32_t scc, SharedContext& comp);
    void mapGeneratorAssignment(const Solver& s, const SccGraph& dep, LitVec& assume) const;
    void mapTesterModel(const Solver& s, VarVec& out) const;
    bool simplify(const Solver& generator, const SccGraph& dep, Solver& tester);
    [[nodiscard]] MapSpan atoms() const { return {mapping.begin(), mapping.begin() + numAtoms}; }
    [[nodiscard]] MapSpan bodies() const { return {mapping.begin() + numAtoms, mapping.end()}; }
    [[nodiscard]] MapIt_c findAtom(NodeId nodeId) const {
        return std::lower_bound(mapping.begin(), mapping.begin() + numAtoms, Mapping(nodeId));
    }
    NodeMap  mapping;     // maps nodes of P to literals in C;
    uint32_t numAtoms{0}; // number of atoms
};
// Adds necessary variables for all atoms and bodies to the component program.
// Input-Vars: (set via assumptions)
//  tp: for each atom p in a proper disjunctive head, tp is true iff p is true in P
//  fb: for each body b, fb is true iff b is false in P
// Aux-Var: (derived)
//  hp: for each atom p in a proper disjunctive head, hp is true iff tp and ~up
// Output: (unfounded sets)
//  up: for each atom p, up is true iff a is unfounded w.r.t the assignment of P.
void PrgDepGraph::NonHcfComponent::ComponentMap::addVars(Solver& generator, const SccGraph& dep, VarView atoms,
                                                         VarView bodies, SharedContext& comp) {
    assert(generator.decisionLevel() == 0);
    mapping.reserve(atoms.size() + bodies.size());
    const auto mt = dep.nonHcfMapType();
    for (auto atomId : atoms) {
        const AtomNode& at  = dep.getAtom(atomId);
        Literal         gen = at.lit;
        if (generator.isFalse(gen)) {
            continue;
        }
        Mapping map(atomId);
        // up [ hp [tp] ]
        map.var = comp.addVar(VarType::atom); // up
        map.ext = (mt == PrgDepGraph::map_old || at.inDisjunctive());
        comp.setFrozen(map.var, true);
        if (map.ext) {
            comp.addVar(VarType::atom);      // hp
            if (not generator.isTrue(gen)) { // tp
                comp.setFrozen(comp.addVar(VarType::atom), true);
                ++map.ext;
            }
        }
        mapping.push_back(map);
    }
    numAtoms = size32(mapping);
    std::ranges::sort(mapping);
    // add necessary vars for bodies
    for (auto bodyId : bodies) {
        Literal gen = dep.getBody(bodyId).lit;
        if (generator.isFalse(gen)) {
            continue;
        }
        Mapping map(bodyId);
        if (not generator.seen(gen) && not generator.isTrue(gen)) {
            map.var = comp.addVar(VarType::atom);
            comp.setFrozen(map.var, true);
            generator.markSeen(gen);
        }
        else if (generator.isTrue(gen)) {
            map.ext = 1u;
        }
        else {
            map.ext = 2u;
            auto bs = this->bodies();
            if (auto it = std::find_if(bs.rbegin(), bs.rend(),
                                       [&](const Mapping& m) { return dep.getBody(m.node).lit == gen; });
                it != bs.rend()) {
                map.var = it->var;
            }
        }
        assert(map.var <= comp.numVars() && (map.var || map.ext == 1u));
        mapping.push_back(map);
    }
    for (const auto& m : this->bodies()) {
        if (not m.eq()) {
            auto v = dep.getBody(m.node).lit.var();
            generator.clearSeen(v);
        }
    }
}

// Adds constraints stemming from the given atoms to the component program.
// 1. [up(a0) v ... v up(an-1)], where
//   - ai is an atom in P from the given atom set, and
//   - up(ai) is the corresponding output-atom in the component program C.
// 2. For each atom 'ai' in atom set occurring in a proper disjunction, [hp(ai) <=> tp(ai), ~up(ai)], where
//   tp(ai), hp(ai), up(ai) are the input, aux, and output atoms in C.
void PrgDepGraph::NonHcfComponent::ComponentMap::addAtomConstraints(SharedContext& comp) {
    ClauseCreator cc1(comp.master()), cc2(comp.master());
    cc1.addDefaultFlags(ClauseCreator::clause_force_simplify);
    cc1.start();
    for (const auto& m : atoms()) {
        cc1.add(m.up());
        if (m.disj()) {
            cc2.start().add(~m.tp()).add(m.up()).add(m.hp()).end(); // [~tp v up v hp]
            cc2.start().add(~m.hp()).add(m.tp()).end();             // [~hp v tp]
            cc2.start().add(~m.hp()).add(~m.up()).end();            // [~hp v ~up]
        }
    }
    cc1.end();
}

// Adds constraints stemming from the given bodies to the component program.
// For each atom 'ai' and rule a0 | ai | ...| an :- B, s.th. B in bodies
//  [~up(ai) v fb(B) V hp(aj), j != i V up(p), p in B+ ^ C], where
// hp(ai), up(ai) are the aux and output atoms of 'ai' in C.
void PrgDepGraph::NonHcfComponent::ComponentMap::addBodyConstraints(const Solver& generator, const SccGraph& dep,
                                                                    uint32_t scc, SharedContext& comp) {
    ClauseCreator cc(comp.master());
    cc.addDefaultFlags(ClauseCreator::clause_force_simplify);
    ClauseCreator dc(comp.master());
    MapIt         j = mapping.begin() + numAtoms;
    for (const auto& m : bodies()) {
        const BodyNode& body = dep.getBody(m.node);
        if (generator.isFalse(body.lit)) {
            continue;
        }
        POTASSCO_CHECK_PRE(not body.extended(), "Extended bodies not supported - use '--trans-ext=weight'");
        auto headSpan = body.heads();
        for (auto hIt = headSpan.begin(), hEnd = headSpan.end(); hIt != hEnd; ++hIt) {
            uint32_t hScc = *hIt ? dep.getAtom(*hIt).scc : dep.getAtom(hIt[1]).scc;
            if (hScc != scc) {
                // the head is not relevant to this non-hcf - skip it
                if (!*hIt) {
                    do { ++hIt; } while (*hIt);
                }
                continue;
            }
            // [fb(B) v ~up(a) V hp(o) for all o != a in B.disHead V up(b) for each b in B+ ^ C]
            cc.start().add(m.fb());
            if (body.scc == scc) { // add subgoals from same scc
                for (const auto& x : body.predecessors(true)) {
                    MapIt_c atMapped = findAtom(x.id());
                    cc.add(atMapped->up());
                }
            }
            if (*hIt) { // normal head
                MapIt_c atMapped = findAtom(*hIt);
                assert(atMapped != mapping.begin() + numAtoms);
                cc.add(~atMapped->up());
                cc.end();
            }
            else { // disjunctive head
                for (auto dHead = ++hIt; *hIt; ++hIt) {
                    dc.start();
                    dc               = cc;
                    MapIt_c atMapped = findAtom(*hIt);
                    dc.add(~atMapped->up());
                    for (auto other = dHead; *other; ++other) {
                        if (*other != *hIt) {
                            assert(dep.getAtom(*other).scc == scc);
                            atMapped = findAtom(*other);
                            dc.add(atMapped->hp());
                        }
                    }
                    dc.end();
                }
            }
        }
        if (not m.eq()) {
            *j++ = m;
        }
    }
    mapping.erase(j, mapping.end());
}

// Maps the generator assignment given in s to a list of tester assumptions.
void PrgDepGraph::NonHcfComponent::ComponentMap::mapGeneratorAssignment(const Solver& s, const SccGraph& dep,
                                                                        LitVec& assume) const {
    Literal gen;
    assume.clear();
    assume.reserve(mapping.size());
    for (const auto& at : atoms()) {
        gen = dep.getAtom(at.node).lit;
        if (at.hasTp()) {
            assume.push_back(at.tp() ^ (not s.isTrue(gen)));
        }
        if (s.isFalse(gen)) {
            assume.push_back(~at.up());
        }
    }
    for (const auto& m : bodies()) {
        gen = dep.getBody(m.node).lit;
        assume.push_back(m.fb() ^ (not s.isFalse(gen)));
    }
}
// Maps the tester model given in s back to a list of unfounded atoms in the generator.
void PrgDepGraph::NonHcfComponent::ComponentMap::mapTesterModel(const Solver& s, VarVec& out) const {
    assert(s.numFreeVars() == 0);
    out.clear();
    for (const auto& m : atoms()) {
        if (s.isTrue(m.up())) {
            out.push_back(m.node);
        }
    }
}
bool PrgDepGraph::NonHcfComponent::ComponentMap::simplify(const Solver& generator, const SccGraph& dep,
                                                          Solver& tester) {
    if (not tester.popRootLevel(UINT32_MAX)) {
        return false;
    }
    if (tester.sharedContext()->isShared() && (tester.sharedContext()->allowImplicit(ConstraintType::conflict) ||
                                               tester.sharedContext()->distributor.get())) {
        // Simplification not safe: top-level assignments of threads are
        // not necessarily synchronised at this point and clauses simplified
        // with top-level assignment of this thread might not (yet) be valid
        // wrt possible assumptions in other threads.
        return true;
    }
    const bool rem = not tester.sharedContext()->isShared();
    MapIt      j   = rem ? mapping.begin() : mapping.end();
    for (MapIt_c it = mapping.begin(), aEnd = it + numAtoms, end = mapping.end(); it != end; ++it) {
        const Mapping& m    = *it;
        const bool     atom = it < aEnd;
        Literal        g    = atom ? dep.getAtom(m.node).lit : dep.getBody(m.node).lit;
        if (generator.topValue(g.var()) == value_free) {
            if (rem) {
                *j++ = m;
            }
            continue;
        }
        bool isFalse = generator.isFalse(g);
        bool ok      = atom || tester.force(isFalse ? m.fb() : ~m.fb());
        if (atom) {
            if (not isFalse) {
                ok = not m.hasTp() || tester.force(m.tp());
                if (rem) {
                    *j++ = m;
                }
            }
            else {
                ok        = tester.force(~m.up()) && (not m.hasTp() || tester.force(~m.tp()));
                numAtoms -= (ok && rem);
            }
        }
        if (not ok) {
            if (rem) {
                j = std::copy(it, end, j);
            }
            break;
        }
    }
    mapping.erase(j, mapping.end());
    return tester.simplify();
}
/////////////////////////////////////////////////////////////////////////////////////////
// class PrgDepGraph::NonHcfComponent
/////////////////////////////////////////////////////////////////////////////////////////
PrgDepGraph::NonHcfComponent::NonHcfComponent(uint32_t id, const PrgDepGraph& dep, SharedContext& genCtx,
                                              Configuration* c, uint32_t scc, VarView atoms, VarView bodies)
    : dep_(&dep)
    , prg_(std::make_unique<SharedContext>())
    , comp_(std::make_unique<ComponentMap>())
    , id_(id)
    , scc_(scc) {
    Solver& generator = *genCtx.master();
    prg_->setConcurrency(genCtx.concurrency(), SharedContext::resize_reserve);
    prg_->setConfiguration(c);
    comp_->addVars(generator, dep, atoms, bodies, *prg_);
    prg_->startAddConstraints();
    comp_->addAtomConstraints(*prg_);
    comp_->addBodyConstraints(generator, dep, scc, *prg_);
    prg_->endInit(true);
}

PrgDepGraph::NonHcfComponent::~NonHcfComponent() = default;

void PrgDepGraph::NonHcfComponent::update(const SharedContext& generator) {
    for (uint32_t i = 0; generator.hasSolver(i); ++i) {
        if (not prg_->hasSolver(i)) {
            prg_->attach(prg_->pushSolver());
        }
        else {
            prg_->initStats(*prg_->solver(i));
        }
    }
}

void PrgDepGraph::NonHcfComponent::assumptionsFromAssignment(const Solver& s, LitVec& assume) const {
    comp_->mapGeneratorAssignment(s, *dep_, assume);
}

bool PrgDepGraph::NonHcfComponent::test(const Solver& generator, LitView assume, VarVec& unfoundedOut) const {
    assert(generator.id() < prg_->concurrency() && "Invalid id!");
    // Forwards to message handler of generator so that messages are
    // handled during long-running tests.
    struct Tester : MessageHandler {
        Tester(Solver& s, MessageHandler* gen) : solver(&s), generator(gen) {
            if (gen) {
                s.addPost(this);
            }
        }
        ~Tester() override {
            if (generator) {
                solver->removePost(this);
            }
        }
        bool handleMessages() override { return generator->handleMessages(); }
        bool propagateFixpoint(Solver&, PostPropagator*) override {
            if (not Tester::handleMessages()) {
                solver->setStopConflict(); // terminate
                return false;
            }
            return true;
        }
        [[nodiscard]] int test(LitView assume) const {
            bool init = solver->stats.choices == 0;
            return static_cast<int>(not BasicSolve(*solver).satisfiable(assume, init));
        }
        Solver*         solver;
        MessageHandler* generator;
    } tester(*prg_->solver(generator.id()),
             static_cast<MessageHandler*>(generator.getPost(PostPropagator::priority_reserved_msg)));
    SolveTestEvent ev(*tester.solver, id_, generator.numFreeVars() != 0);
    tester.solver->stats.addTest(ev.partial);
    generator.sharedContext()->report(ev);
    ev.time = ThreadTime::getTime();
    if (ev.result = tester.test(assume); ev.result == 0) {
        tester.solver->stats.addModel(tester.solver->decisionLevel());
        comp_->mapTesterModel(*tester.solver, unfoundedOut);
    }
    ev.time = ThreadTime::getTime() - ev.time;
    tester.solver->stats.addCpuTime(ev.time);
    generator.sharedContext()->report(ev);
    return ev.result != 0;
}
bool PrgDepGraph::NonHcfComponent::simplify(const Solver& s) const {
    return comp_->simplify(s, *dep_, *prg_->solver(s.id()));
}
/////////////////////////////////////////////////////////////////////////////////////////
// class PrgDepGraph::NonHcfStats
/////////////////////////////////////////////////////////////////////////////////////////
struct PrgDepGraph::NonHcfStats::Data {
    using ProblemVec = StatsVec<ProblemStats>;
    using SolverVec  = StatsVec<SolverStats>;
    struct ComponentStats {
        ProblemVec problem;
        SolverVec  solvers;
        SolverVec  accu;
    };
    Data(uint32_t level, bool inc) : components(level > 1 ? std::make_unique<ComponentStats>() : nullptr) {
        if (inc) {
            accus         = std::make_unique<SolverStats>();
            solvers.multi = accus.get();
        }
    }
    void addHcc(const NonHcfComponent& c) {
        assert(components);
        ProblemVec& hcc    = components->problem;
        SolverVec&  solver = components->solvers;
        SolverVec*  accu   = solvers.multi ? &components->accu : nullptr;
        uint32_t    id     = c.id();
        if (id >= hcc.size()) {
            hcc.growTo(id + 1);
            solver.growTo(id + 1);
            if (accu) {
                accu->growTo(id + 1);
            }
        }
        if (not hcc[id]) {
            hcc[id]    = new ProblemStats(c.ctx().stats());
            solver[id] = new SolverStats();
            if (accu) {
                (*accu)[id]       = new SolverStats();
                solver[id]->multi = (*accu)[id];
            }
        }
    }
    void updateHcc(const NonHcfComponent& c) {
        c.ctx().accuStats(solvers);
        if (components && c.id() < components->solvers.size()) {
            POTASSCO_CHECK_PRE(components->solvers[c.id()], "component not added to stats!");
            c.ctx().accuStats(*components->solvers[c.id()]);
            components->solvers[c.id()]->flush();
        }
    }
    ProblemStats                    hccs;
    SolverStats                     solvers;
    std::unique_ptr<ComponentStats> components;
    std::unique_ptr<SolverStats>    accus;
};
PrgDepGraph::NonHcfStats::NonHcfStats(PrgDepGraph& g, uint32_t l, bool inc)
    : graph_(&g)
    , data_(std::make_unique<Data>(l, inc)) {
    for (auto* hcc : g.nonHcfs()) { addHcc(*hcc); }
}
PrgDepGraph::NonHcfStats::~NonHcfStats() = default;
void PrgDepGraph::NonHcfStats::accept(StatsVisitor& out, bool final) const {
    if (not data_->solvers.multi) {
        final = false;
    }
    out.visitProblemStats(data_->hccs);
    out.visitSolverStats(final ? *data_->solvers.multi : data_->solvers);
    if (data_->components && out.visitHccs(StatsVisitor::enter)) {
        const Data::SolverVec&  solver = final ? data_->components->accu : data_->components->solvers;
        const Data::ProblemVec& hcc    = data_->components->problem;
        for (auto i : irange(hcc)) { out.visitHcc(i, *hcc[i], *solver[i]); }
        out.visitHccs(StatsVisitor::leave);
    }
}
void PrgDepGraph::NonHcfStats::startStep(uint32_t statsLevel) {
    data_->solvers.reset();
    if (data_->components) {
        data_->components->solvers.reset();
    }
    if (statsLevel > 1 && not data_->components) {
        data_->components = std::make_unique<Data::ComponentStats>();
        for (auto* hcc : graph_->nonHcfs()) { data_->addHcc(*hcc); }
    }
}
void PrgDepGraph::NonHcfStats::endStep() {
    for (auto* hcc : graph_->nonHcfs()) { data_->updateHcc(*hcc); }
    data_->solvers.flush();
}
void PrgDepGraph::NonHcfStats::addHcc(const NonHcfComponent& c) {
    data_->hccs.accu(c.ctx().stats());
    if (data_->components) {
        data_->addHcc(c);
    }
}
void PrgDepGraph::NonHcfStats::removeHcc(const NonHcfComponent& c) { data_->updateHcc(c); }
void PrgDepGraph::NonHcfStats::addTo(StatsMap& problem, StatsMap& solving, StatsMap* accu) const {
    data_->solvers.addTo("hccs", solving, accu);
    problem.add("hccs", StatisticObject::map(&data_->hccs));
    if (data_->components) {
        problem.add("hcc", data_->components->problem.toStats());
        solving.add("hcc", data_->components->solvers.toStats());
        if (accu) {
            accu->add("hcc", data_->components->accu.toStats());
        }
    }
}
} // namespace Asp
/////////////////////////////////////////////////////////////////////////////////////////
// class ExtDepGraph
/////////////////////////////////////////////////////////////////////////////////////////
ExtDepGraph::ExtDepGraph(uint32_t) : maxNode_(0), comEdge_(0), genCnt_(0) {}
ExtDepGraph::~ExtDepGraph() = default;
void ExtDepGraph::addEdge(Literal lit, uint32_t startNode, uint32_t endNode) {
    POTASSCO_CHECK_PRE(not frozen(), "ExtDepGraph::update() not called!");
    fwdArcs_.push_back(Arc::create(lit, startNode, endNode));
    maxNode_ = std::max(std::max(startNode, endNode) + 1u, maxNode_);
    if (comEdge_ && std::min(startNode, endNode) < nodes_.size()) {
        invArcs_.clear();
        comEdge_ = 0;
        ++genCnt_;
    }
}
bool ExtDepGraph::frozen() const { return not fwdArcs_.empty() && fwdArcs_.back().tail() == UINT32_MAX; }
void ExtDepGraph::update() {
    if (frozen()) {
        fwdArcs_.pop_back();
    }
}
uint32_t ExtDepGraph::finalize(SharedContext& ctx) {
    if (frozen()) {
        return comEdge_;
    }
    // sort by end node
    std::sort(fwdArcs_.begin() + comEdge_, fwdArcs_.end(), CmpArc<1>());
    invArcs_.reserve(fwdArcs_.size());
    Node sent = {UINT32_MAX, UINT32_MAX};
    nodes_.resize(maxNode_, sent);
    for (auto it = fwdArcs_.begin() + comEdge_, end = fwdArcs_.end(); it != end;) {
        uint32_t node = it->head();
        POTASSCO_CHECK_PRE(not comEdge_ || nodes_[node].invOff == UINT32_MAX,
                           "ExtDepGraph: invalid incremental update!");
        Inv inv;
        nodes_[node].invOff = size32(invArcs_);
        do {
            inv.lit = it->lit;
            inv.rep = static_cast<uint32_t>(it->tail() << 1) | 1u;
            invArcs_.push_back(inv);
            ctx.setFrozen(it->lit.var(), true);
        } while (++it != end && it->head() == node);
        invArcs_.back().rep ^= 1u;
    }
    // sort by start node
    std::sort(fwdArcs_.begin() + comEdge_, fwdArcs_.end(), CmpArc<0>());
    for (auto it = fwdArcs_.begin() + comEdge_, end = fwdArcs_.end(); it != end;) {
        uint32_t node = it->tail();
        POTASSCO_CHECK_PRE(not comEdge_ || nodes_[node].fwdOff == UINT32_MAX,
                           "ExtDepGraph: invalid incremental update!");
        nodes_[node].fwdOff = static_cast<uint32_t>(it - fwdArcs_.begin());
        it                  = std::lower_bound(it, end, node + 1, CmpArc<0>());
    }
    comEdge_ = size32(fwdArcs_);
    fwdArcs_.push_back(Arc::create(lit_false, UINT32_MAX, UINT32_MAX));
    return comEdge_;
}
uint64_t ExtDepGraph::attach(Solver& s, Constraint& p, uint64_t genId) {
    auto count = static_cast<uint32_t>(genId >> 32);
    auto edges = static_cast<uint32_t>(genId);
    POTASSCO_ASSERT(edges <= comEdge_);
    uint32_t update = count == genCnt_ ? 0u : edges;
    for (auto i : irange(count == genCnt_ ? edges : 0u, comEdge_)) {
        const Arc& a = fwdArcs_[i];
        if (a.head() != a.tail()) {
            if (s.topValue(a.lit.var()) == value_free) {
                if (GenericWatch* w = update ? s.getWatch(a.lit, &p) : nullptr; not w) {
                    s.addWatch(a.lit, &p, i);
                }
                else {
                    w->data = i;
                    --update;
                }
            }
            else if (s.isTrue(a.lit)) {
                p.propagate(s, a.lit, i);
            }
        }
        else if (not s.force(~a.lit)) {
            break;
        }
    }
    return (static_cast<uint64_t>(genCnt_) << 32) | comEdge_;
}
void ExtDepGraph::detach(Solver* s, Constraint& p) {
    if (s) {
        for (auto i = fwdArcs_.size(); i--;) { s->removeWatch(fwdArcs_[i].lit, &p); }
    }
}
/////////////////////////////////////////////////////////////////////////////////////////
// class AcyclicityCheck
/////////////////////////////////////////////////////////////////////////////////////////
struct AcyclicityCheck::ReasonStore {
    using NogoodMap = PodVector_t<LitVec*>;
    NogoodMap db;
    void      getReason(Literal p, LitVec& out) {
        if (const LitVec* r = db[p.var()]) {
            out.insert(out.end(), r->begin(), r->end());
        }
    }
    void setReason(Literal p, LitView reason) {
        auto v = p.var();
        if (v >= db.size()) {
            db.resize(v + 1, nullptr);
        }
        if (db[v] == nullptr) {
            db[v] = new LitVec;
        }
        db[v]->assign(reason.begin(), reason.end());
    }
    ~ReasonStore() { std::ranges::for_each(db, DeleteObject()); }
};
AcyclicityCheck::AcyclicityCheck(DependencyGraph* graph)
    : graph_(graph)
    , solver_(nullptr)
    , nogoods_(nullptr)
    , strat_(Potassco::nth_bit<uint32_t>(config_bit))
    , tagCnt_(0)
    , genId_(0) {}
AcyclicityCheck::~AcyclicityCheck() = default;

void AcyclicityCheck::setStrategy(Strategy p) { strat_ = p; }
void AcyclicityCheck::setStrategy(const SolverParams& p) {
    if (p.acycFwd) {
        setStrategy(prop_fwd);
    }
    else {
        setStrategy(p.loopRep ? prop_full_imp : prop_full);
    }
    Potassco::store_set_bit(strat_, config_bit);
}

bool AcyclicityCheck::init(Solver& s) {
    if (not graph_) {
        graph_ = s.sharedContext()->extGraph.get();
    }
    if (not graph_) {
        return true;
    }
    if (Potassco::test_bit(strat_, config_bit)) {
        setStrategy(s.sharedContext()->configuration()->solver(s.id()));
    }
    tags_.assign(graph_->nodes(), tagCnt_ = 0);
    parent_.resize(graph_->nodes());
    todo_.clear();
    solver_ = &s;
    genId_  = graph_->attach(s, *this, genId_);
    return true;
}

uint32_t AcyclicityCheck::startSearch() {
    if (++tagCnt_ != 0) {
        return tagCnt_;
    }
    const uint32_t last = tagCnt_ - 1;
    for (auto& tag : tags_) { tag = (tag == last); }
    return tagCnt_ = 2;
}
void AcyclicityCheck::setReason(Literal p, LitView reason) {
    if (not nogoods_) {
        nogoods_ = std::make_unique<ReasonStore>();
    }
    nogoods_->setReason(p, reason);
}
void AcyclicityCheck::addClauseLit(Solver& s, Literal p) {
    assert(s.isFalse(p));
    uint32_t dl = s.level(p.var());
    if (dl && not s.seen(p)) {
        s.markSeen(p);
        s.markLevel(dl);
        reason_.push_back(p);
    }
}

void AcyclicityCheck::reset() {
    todo_.clear();
    reason_.clear();
}

bool AcyclicityCheck::valid(Solver& s) {
    if (todo_.empty()) {
        return true;
    }
    return AcyclicityCheck::propagateFixpoint(s, nullptr);
}
bool AcyclicityCheck::isModel(Solver& s) { return AcyclicityCheck::valid(s); }

void AcyclicityCheck::destroy(Solver* s, bool detach) {
    if (s && detach) {
        s->removePost(this);
    }
    if (graph_) {
        graph_->detach(detach ? s : nullptr, *this);
    }
    PostPropagator::destroy(s, detach);
}
void AcyclicityCheck::reason(Solver&, Literal p, LitVec& out) {
    if (not reason_.empty() && reason_[0] == p) {
        out.insert(out.end(), reason_.begin() + 1, reason_.end());
    }
    else if (nogoods_) {
        nogoods_->getReason(p, out);
    }
}

bool AcyclicityCheck::propagateFixpoint(Solver& s, PostPropagator*) {
    for (Arc x; not todo_.empty();) {
        x = todo_.pop_ret();
        if (not dfsForward(s, x) || (strategy() != prop_fwd && not dfsBackward(s, x))) {
            return false;
        }
    }
    todo_.clear();
    return true;
}
bool AcyclicityCheck::dfsForward(Solver& s, const Arc& root) {
    const uint32_t tag = startSearch();
    nStack_.clear();
    pushVisit(root.head(), tag);
    while (not nStack_.empty()) {
        auto node = nStack_.back();
        nStack_.pop_back();
        for (const Arc* a = graph_->fwdBegin(node); a; a = a->next()) {
            if (s.isTrue(a->lit)) {
                auto nodeNext = a->head();
                if (nodeNext == root.tail()) {
                    setParent(nodeNext, {.lit = a->lit, .node = node});
                    reason_.assign(1, ~root.lit);
                    for (auto n0 = nodeNext; n0 != root.head();) {
                        const auto& [plit, pnode] = parent_[n0];
                        assert(s.isTrue(plit));
                        reason_.push_back(plit);
                        n0 = pnode;
                    }
                    return s.force(~root.lit, this);
                }
                if (not visited(nodeNext, tag)) {
                    setParent(nodeNext, {.lit = a->lit, .node = node});
                    pushVisit(nodeNext, tag);
                }
            }
        }
    }
    return true;
}
bool AcyclicityCheck::dfsBackward(Solver& s, const Arc& root) {
    const uint32_t tag = startSearch();
    const uint32_t fwd = tag - 1;
    nStack_.clear();
    pushVisit(root.tail(), tag);
    while (not nStack_.empty()) {
        auto node = nStack_.back();
        nStack_.pop_back();
        for (const Inv* a = graph_->invBegin(node); a; a = a->next()) {
            auto val      = s.value(a->lit.var());
            auto nodeNext = a->tail();
            if (val == falseValue(a->lit) || visited(nodeNext, tag)) {
                continue;
            }
            if (visited(nodeNext, fwd)) { // a->lit would complete a cycle - force to false
                assert(val == value_free || s.level(a->lit.var()) == s.decisionLevel());
                reason_.assign(1, ~a->lit);
                addClauseLit(s, ~root.lit);
                for (auto n = nodeNext; n != root.head();) {
                    const auto& [plit, pnode] = parent_[n];
                    assert(s.isTrue(plit) && visited(pnode, fwd));
                    addClauseLit(s, ~plit);
                    n = pnode;
                }
                for (auto n = node; n != root.tail();) {
                    const auto& [plit, pnode] = parent_[n];
                    assert(s.isTrue(plit) && visited(pnode, tag));
                    addClauseLit(s, ~plit);
                    n = pnode;
                }
                if (val == value_free && strategy() == prop_full) {
                    ConstraintInfo info(ConstraintType::loop);
                    s.finalizeConflictClause(reason_, info, 0);
                    ClauseCreator::create(s, reason_, ClauseCreator::clause_no_prepare, info);
                }
                else {
                    for (auto& p : drop(reason_, 1u)) {
                        s.clearSeen(p.var());
                        p = ~p;
                    }
                    if (not s.force(~a->lit, this)) {
                        return false;
                    }
                    setReason(~a->lit, drop(reason_, 1u));
                }
                assert(s.isFalse(a->lit));
                if (not s.propagateUntil(this)) {
                    return false;
                }
            }
            else if (val != value_free) { // follow true edge backward
                setParent(nodeNext, {.lit = a->lit, .node = node});
                pushVisit(nodeNext, tag);
            }
        }
    }
    return true;
}
} // namespace Clasp
