
#include "util/log.h"

class FactAnalysisUtil {

private:
    HtnInstance& _htn;
    NodeHashMap<int, FactFrame>& _fact_frames;
    NetworkTraversal& _traversal;

public:

    NetworkTraversal& getTraversal() {
        return _traversal;
    }

    FactAnalysisUtil(HtnInstance& htn, NodeHashMap<int, FactFrame>& fact_frames, NetworkTraversal& traversal) : _htn(htn), _fact_frames(fact_frames), _traversal(traversal) {
    }

    FactFrame getFactFrame(const USignature& sig) {
        const FactFrame& f = _fact_frames.at(sig._name_id);
        return f.substitute(Substitution(f.sig._args, sig._args));
    }

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

    std::vector<int> findCycle(int nodeToFind, std::vector<int>& adjacentNodes, std::map<int, std::vector<int>>& orderingOplist, std::vector<int>& traversedNodes) {
        for (const auto& adjacentNode : adjacentNodes) {
            Log::d("NodeToFind: %i, adjacentNode: %i\n", nodeToFind, adjacentNode);
            bool cycle = false;
            for (const auto& traversedNode: traversedNodes) {
                Log::d("TraversedNode: %i\n", traversedNode);
                if (traversedNode == adjacentNode) cycle = true;
            }
            if (cycle) {
                if (adjacentNode == nodeToFind) {
                    Log::d("Found cycle!\n");
                    traversedNodes.push_back(adjacentNode);
                    return traversedNodes;
                } else {
                    continue;
                }
            } else {
                std::vector<int> newTraversedNodes = traversedNodes;
                newTraversedNodes.push_back(adjacentNode);
                return findCycle(nodeToFind, orderingOplist[adjacentNode], orderingOplist, newTraversedNodes);
            }
        }
        return std::vector<int>();
    }
};