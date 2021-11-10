#include "data/htn_instance.h"
#include "algo/network_traversal.h"
#include "algo/fact_analysis_util.h"
#include "util/params.h"

class FactAnalysisPreprocessing {

private:
    HtnInstance& _htn;
    NodeHashMap<int, FactFrame>& _fact_frames;
    FactAnalysisUtil& _util;
    std::function<Signature(const Signature& sig, FlatHashSet<int> argSet)> normalizeSignature = [&](const Signature& sig, FlatHashSet<int> argSet) {
        Signature newSig = sig;
        for (size_t j = 0; j < newSig._usig._args.size(); j++) {
            int& arg = newSig._usig._args[j];
            if (!argSet.count(arg)) arg = _htn.nameId("??_");
        }
        return newSig;
    };
    std::function<bool(const Signature& sig, FlatHashSet<int> argSet)> hasUnboundArgs = [&](const Signature& sig, FlatHashSet<int> argSet) {
        for (size_t j = 0; j < sig._usig._args.size(); j++) {
            const int& arg = sig._usig._args[j];
            if (!argSet.count(arg)) return true;
        }
        return false;
    };
    FlatHashSet<int> _fluent_predicates;
    bool _postcondition_pruning;
    int _num_custom_vars = 0;
    int MAX_NODES = 100;
    USigSet& _init_state;
    FlatHashMap<int, FlatHashMap<USignature, FlatHashSet<int>, USignatureHasher>> _rigid_predicate_cache;
    FlatHashSet<int> operationsWithCycleInDescent;
public:
    FactAnalysisPreprocessing (HtnInstance& htn, NodeHashMap<int, FactFrame>& fact_frames, FactAnalysisUtil& util, Parameters& params, USigSet& init_state) : 
        _htn(htn), _fact_frames(fact_frames), _util(util), MAX_NODES(params.getIntParam("pfcNumNodes", 128)), 
        _postcondition_pruning(bool(params.getIntParam("pfcPostconditions"))), _init_state(init_state) {}

    void computeFactFramesBase();

    void computeFactFramesTree();

    FlatHashMap<int, FlatHashMap<USignature, FlatHashSet<int>, USignatureHasher>>& getRigidPredicateCache() {
        return _rigid_predicate_cache;
    }

private:
    SigSet filterFluentPredicates(const SigSet& unfiltered, FlatHashSet<int>& _fluent_predicates) {
        SigSet filteredSigSet;
        for (auto& prereq :  unfiltered) {
            if (!_fluent_predicates.count(prereq._usig._name_id)) {
                filteredSigSet.insert(prereq);
            }
        }
        return filteredSigSet;
    }

    SigSet filterRigidPredicates(const SigSet& unfiltered, FlatHashSet<int>& _fluent_predicates) {
        SigSet filteredSigSet;
        for (auto& prereq :  unfiltered) {
            if (_fluent_predicates.count(prereq._usig._name_id)) {
                filteredSigSet.insert(prereq);
            }
        }
        return filteredSigSet;
    }
    
    std::vector<int> calcOrderedOpList();

    void fillFactFramesAction(int& opId, int& aId, bool& change);

    void fillFactFramesBase(std::vector<int>& orderingOplist);
    void fillRigidPredicateCache();

    void extendPreconditions(std::vector<int>& orderingOplist);

    void fillPFCNodesTopDownBFS(std::vector<int>& orderedOpIds);

    void printFactFrameBFS(int opId);

    void findOperationsWithCycles(std::map<int, std::vector<int>>& orderingOplist);
    bool findCycle(std::map<int, std::vector<int>>& orderingOplist, int operation, FlatHashSet<int>& foundNodes);

    FlatHashSet<int> findFluentPredicates(const std::vector<int>& orderedOpIds);
};
