#include "data/htn_instance.h"
#include "algo/network_traversal.h"
#include "algo/fact_analysis_util.h"

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
    FlatHashSet<int> _fluent_predicates;
public:
    FactAnalysisPreprocessing (HtnInstance& htn, NodeHashMap<int, FactFrame>& fact_frames, FactAnalysisUtil& util) : _htn(htn), _fact_frames(fact_frames), _util(util) {}

    void computeFactFramesBase();

    void computeFactFramesCondEffs();

    void computeFactFramesTree();

private:
    std::vector<int> calcOrderedOpList();

    void normalizeSubstituteNodeDiff(const PFCNode& newNode, PFCNode& nodeToExtend, const FlatHashSet<int>& argSet, const Substitution& s, 
        std::function<Signature(const Signature& sig, FlatHashSet<int> argSet)> normalizeFunction, int depthLimit);

    void fillFactFramesAction(int& opId, int& aId, bool& change);

    void computeCondEffs(std::vector<int>& orderingOplist);

    void fillFactFramesBase(std::vector<int>& orderingOplist);

    void extendPreconditions(std::vector<int>& orderingOplist);

    void fillPFCNodes(std::vector<int>& orderingOplist);
    
    FlatHashSet<int> findFluentPredicates(const std::vector<int>& orderedOpIds);
};
