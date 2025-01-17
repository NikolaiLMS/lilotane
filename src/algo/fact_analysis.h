
#ifndef DOMPASCH_LILOTANE_ANALYSIS_H
#define DOMPASCH_LILOTANE_ANALYSIS_H

#include "data/htn_instance.h"
#include "algo/network_traversal.h"
#include "algo/arg_iterator.h"
#include "algo/compute_fact_frame.h"

typedef std::function<bool(const USignature&, bool)> StateEvaluator;

class FactAnalysis {

private:
    NetworkTraversal _traversal;

    USigSet _initialized_facts;
    USigSet _relevant_facts;

    // Maps an (action|reduction) name 
    // to the set of (partially lifted) fact signatures
    // that might be added to the state due to this operator. 
    NodeHashMap<int, SigSet> _fact_changes; 
    NodeHashMap<int, SigSet> _lifted_fact_changes;
    NodeHashMap<USignature, SigSet, USignatureHasher> _fact_changes_cache;

protected:
    NodeHashMap<int, SigSet> _postconditions;
    NodeHashMap<int, SigSet> _new_postconditions;
    bool _new_position = true;
    NodeHashMap<int, FactFrame> _fact_frames;
    FactAnalysisUtil _util;
    USigSet _init_state;
    int _rigid_predicates_matched = 0;
    int _invalid_rigid_preconditions_found = 0;
    int _invalid_rigid_preconditions_found_varrestrictions = 0;
    int _invalid_fluent_preconditions_found = 0;
    int _invalid_fluent_preconditions_found_varrestrictions = 0;
    int _invalid_fluent_preconditions_found_via_postconditions = 0;
    int _invalid_operations_found_via_invalid_subtasks = 0;
    int _invalid_operations_found_via_postconditions = 0;
    int _variables_restricted = 0;
    int _nodes_variables_restricted = 0;

    HtnInstance& _htn;
    USigSet _pos_layer_facts;
    USigSet _neg_layer_facts;
    
    int _new_variable_domain_size_limit = 1;

    NodeHashMap<int, USigSet> _final_effects_positive;
    NodeHashMap<int, USigSet> _final_effects_negative;
    int _name_id_;
public:
    FactAnalysis(HtnInstance& htn, Parameters& params) : _htn(htn), _traversal(htn), _init_state(htn.getInitState()), _util(htn, _fact_frames, _traversal), 
        _new_variable_domain_size_limit(params.getIntParam("pfcRestrictLimit")), _name_id_(_htn.nameId("??_")) {
        resetReachability();
    }

    void resetPostconditions() {
        _new_position = true;
        _postconditions.clear();
        for (const auto& [id, sigset]: _new_postconditions) {
            for (const auto& postcondition: sigset) {
                if (_htn.isFullyGround(postcondition._usig)) {
                    _postconditions[id].insert(postcondition);
                    if (!_htn.hasQConstants(postcondition._usig)) {
                        if (postcondition._negated) {
                            if (_pos_layer_facts.count(postcondition._usig)) _pos_layer_facts.erase(postcondition._usig);
                        } else {
                            if (_neg_layer_facts.count(postcondition._usig)) _neg_layer_facts.erase(postcondition._usig);
                        }
                    }
                }
            }
        }
        _new_postconditions.clear();
    }

    void resetPFCCache() {
        _fact_changes_cache.clear();
    }

    int getRigidPredicatesMatched() {
        return _rigid_predicates_matched;
    }

    int getInvalidRigidPreconditionsFound() {
        return _invalid_rigid_preconditions_found;
    }

    int getInvalidRigidPreconditionsFoundByVarRestriction() {
        return _invalid_rigid_preconditions_found_varrestrictions;
    }

    int getInvalidFluentPreconditionsFound() {
        return _invalid_fluent_preconditions_found;
    }

    int getInvalidFluentPreconditionsFoundByVarRestriction() {
        return _invalid_fluent_preconditions_found_varrestrictions;
    }

    int getInvalidFluentPreconditionsFoundViaPostconditions() {
        return _invalid_fluent_preconditions_found_via_postconditions;
    }

    int getInvalidSubtasksFound() {
        return _invalid_operations_found_via_invalid_subtasks;
    }

    int getInvalidOperationsFoundViaPC() {
        return _invalid_operations_found_via_postconditions;
    }

   int getNumEffects() {
        return _util.getNumEffects();
    }

   int getNumVariablesRestricted() {
        return _variables_restricted;
    }

   int getNumNodesVariablesRestricted() {
        return _nodes_variables_restricted;
    }

    void resetReachability() {
        _pos_layer_facts = _init_state;
        _neg_layer_facts.clear();
        _initialized_facts.clear();
        _fact_changes_cache = NodeHashMap<USignature, SigSet, USignatureHasher>();
        _postconditions.clear();
        _new_postconditions.clear();
        _new_position = true;
    }

    void addReachableFact(const Signature& fact) {
        addReachableFact(fact._usig, fact._negated);
    }

    void addReachableFact(const USignature& fact, bool negated) {
        (negated ? _neg_layer_facts : _pos_layer_facts).insert(fact);
    }

    bool isReachable(const Signature& fact) {
        return isReachable(fact._usig, fact._negated);
    }
    
    bool isReachable(const USignature& fact, bool negated) {
        if (negated) {
            return _neg_layer_facts.count(fact) || !_init_state.count(fact);
        }
        return _pos_layer_facts.count(fact);
    }

    bool countPositive(NodeHashMap<int, USigSet>& effects, USignature& usig, NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions) {
        if (_htn.isFullyGround(usig) && !_htn.hasQConstants(usig)) return countPositiveGround(effects[usig._name_id], usig, freeArgRestrictions);
        if (effects[usig._name_id].count(usig)) return true;
        if (_pos_layer_facts.count(usig)) return true;
        for (const USignature& groundFact : ArgIterator::getFullInstantiation(usig, _htn, freeArgRestrictions, true)) {
            //Log::e("groundFact: %s\n", TOSTR(groundFact));
            if (countPositiveGround(effects[usig._name_id], groundFact, freeArgRestrictions)) return true;
        }
        return false;
    }

    bool countPositiveGround(USigSet& effects, const USignature& usig, NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions) {
        if (_pos_layer_facts.count(usig)) return true;
        if (effects.count(usig)) return true;
        for (const auto& eff: effects) {
            for (const USignature& groundFact : ArgIterator::getFullInstantiation(eff, _htn, freeArgRestrictions, true)) {
                //Log::e("groundFact internal: %s\n", TOSTR(groundFact));
                if (groundFact == usig) return true;
            }
        }
        return false;
    }

    bool countNegativeGround(USigSet& effects, const USignature& usig, NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions) {
        if (_neg_layer_facts.count(usig)) return true;
        if (effects.count(usig)) return true;
        for (const auto& eff: effects) {
            for (const USignature& groundFact : ArgIterator::getFullInstantiation(eff, _htn, freeArgRestrictions, true)) {
                if (groundFact == usig) return true;
            }
        }
        return false;
    }

    bool isInvariant(const Signature& fact) {
        return isInvariant(fact._usig, fact._negated);
    }

    bool isInvariant(const USignature& fact, bool negated) {
        return !isReachable(fact, !negated);
    }

    void addRelevantFact(const USignature& fact) {
        _relevant_facts.insert(fact);
    }

    bool isRelevant(const USignature& fact) {
        return _relevant_facts.count(fact);
    }

    const USigSet& getRelevantFacts() {
        return _relevant_facts;
    }

    void addInitializedFact(const USignature& fact) {
        _initialized_facts.insert(fact);
        if (isReachable(fact, /*negated=*/true)) {
            _neg_layer_facts.insert(fact);
        }
    }

    bool isInitialized(const USignature& fact) {
        return _initialized_facts.count(fact);
    }

    SigSet inferPreconditions(const USignature& op) {
        return _util.getFactFrame(op).preconditions;
    }

    std::vector<FlatHashSet<int>> getReducedArgumentDomains(const HtnOp& op);

    inline bool isPseudoOrGroundFactReachable(const USignature& sig, bool negated) {
        if (!_htn.isFullyGround(sig)) return true;
        
        // Q-Fact:
        if (_htn.hasQConstants(sig)) {
            for (const auto& decSig : _htn.decodeObjects(sig, _htn.getEligibleArgs(sig))) {
                if (isReachable(decSig, negated)) return true;
            }
            return false;
        }

        return isReachable(sig, negated);
    }

    inline bool isPseudoOrGroundFactReachable(const Signature& sig) {
        return isPseudoOrGroundFactReachable(sig._usig, sig._negated);
    }

    inline bool hasValidPreconditions(const SigSet& preconds) {
        for (const Signature& pre : preconds) if (!isPseudoOrGroundFactReachable(pre)) {
            return false;
        } 
        return true;
    }

    virtual void computeFactFrames();

    virtual SigSet getPossibleFactChanges(const USignature& sig);

    void deletePossibleFactChangesFromCache(const USignature& sig) {
        if (_fact_changes_cache.count(sig)) _fact_changes_cache.erase(sig);
    }

    const SigSet& getPossibleFactChangesCache(const USignature& sig) {
        if (!_fact_changes_cache.count(sig)) {
            _fact_changes_cache[sig] = getPossibleFactChanges(sig);
        }
        return _fact_changes_cache[sig];
    }

    void substituteEffectsAndAdd(const SigSet& effects, Substitution& s, NodeHashMap<int, USigSet>& positiveEffects,
        NodeHashMap<int, USigSet>& negativeEffects, NodeHashMap<int, SigSet>& postconditions, NodeHashMap<int, FlatHashSet<int>>& globalFreeArgRestrictions);
    bool checkPreconditionValidityRigid(const SigSet& preconditions, NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions);
    bool checkPreconditionValidityFluent(SigSet& preconditions, NodeHashMap<int, USigSet>& foundEffectsPositive, 
        NodeHashMap<int, USigSet>& foundEffectsNegative, NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions,
        NodeHashMap<int, SigSet>& postconditions);
    
    bool restrictNewVariables(SigSet& preconditions, SigSet& fluentPreconditions, Substitution& s, 
        NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions, 
        FlatHashMap<int, FlatHashMap<USignature, FlatHashSet<int>, USignatureHasher>>& rigid_predicate_cache, FlatHashSet<int> nodeArgs,
        NodeHashMap<int, USigSet>& foundEffectsPositive, NodeHashMap<int, USigSet>& foundEffectsNegative, 
        NodeHashMap<int, SigSet>& postconditions, Substitution& globalSub);
    USigSet removeDominated(const NodeHashMap<int, USigSet>& originalSignatures);

    SigSet groundEffects(const NodeHashMap<int, USigSet>& positiveEffects, const NodeHashMap<int, USigSet>& negativeEffects, NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions);
    SigSet groundEffects(const NodeHashMap<int, USigSet>& effects, bool negated, NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions);
};

#endif
