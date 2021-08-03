
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

    USigSet _pos_layer_facts;
    USigSet _neg_layer_facts;

    USigSet _initialized_facts;
    USigSet _relevant_facts;

    // Maps an (action|reduction) name 
    // to the set of (partially lifted) fact signatures
    // that might be added to the state due to this operator. 
    NodeHashMap<int, SigSet> _fact_changes; 
    NodeHashMap<int, SigSet> _lifted_fact_changes;
    NodeHashMap<USignature, SigSet, USignatureHasher> _fact_changes_cache;
 
protected:
    NodeHashMap<int, FactFrame> _fact_frames;
    FactAnalysisUtil _util;
    USigSet _init_state;
    int _rigid_predicates_matched = 0;
    int _invalid_preconditions_found = 0;
    int _invalid_subtasks_found = 0;
    HtnInstance& _htn;

public:
    FactAnalysis(HtnInstance& htn) : _htn(htn), _traversal(htn), _init_state(htn.getInitState()), _util(htn, _fact_frames, _traversal) {
        resetReachability();
    }


    int getRigidPredicatesMatched() {
        return _rigid_predicates_matched;
    }

    int getInvalidPreconditionsFound() {
        return _invalid_preconditions_found;
    }

    int getInvalidSubtasksFound() {
        return _invalid_subtasks_found;
    }

    void resetReachability() {
        _pos_layer_facts = _init_state;
        _neg_layer_facts.clear();
        _initialized_facts.clear();
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
            return _neg_layer_facts.count(fact) || !_pos_layer_facts.count(fact);
        }
        return _pos_layer_facts.count(fact);
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

    // SigSet getPossibleFactChanges(const USignature& sig) {
    //     if (_fact_changes_cache.count(sig)) {
    //         SigSet res = _fact_changes_cache[sig];
    //         _fact_changes_cache.erase(sig);
    //         return res;
    //     } else {
    //         _fact_changes_cache[sig] = computePossibleFactChanges(sig);
    //         return _fact_changes_cache[sig];
    //     }
    // }

    void substituteEffectsAndAdd(const SigSet& effects, Substitution& s, FlatHashMap<int, USigSet>& positiveEffects, FlatHashMap<int, USigSet>& negativeEffects);
    bool checkPreconditionValidityRigid(SigSet& substitutedPreconditions);
    bool checkPreconditionValidityFluent(SigSet& substitutedPreconditions, USigSet& foundEffectsPositive, USigSet& foundEffectsNegative);
    USigSet removeDominated(const FlatHashMap<int, USigSet>& originalSignatures);
    SigSet groundEffects(const FlatHashMap<int, USigSet>& negativeEffects, const FlatHashMap<int, USigSet>& positiveEffects);
};

#endif
