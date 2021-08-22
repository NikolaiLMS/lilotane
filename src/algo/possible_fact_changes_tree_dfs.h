#include "util/params.h"
#include "algo/fact_analysis.h"
#include "util/log.h"

class PFCTreeDFS: public FactAnalysis {
private:
    FactAnalysisPreprocessing _preprocessing;
    bool _check_fluent_preconditions;
    int _max_depth;
public:
    PFCTreeDFS(HtnInstance& htn, Parameters& params): 
        FactAnalysis(htn), _preprocessing(htn, _fact_frames, _util, params), _check_fluent_preconditions(bool(params.getIntParam("pfcFluentPreconditions", 0))), _max_depth(params.getIntParam("pfcTreeDepth", 1)) {

    }

    void computeFactFrames() {
        _preprocessing.computeFactFramesTree();
    }

    SigSet getPossibleFactChanges(const USignature& sig) {
        _final_effects_positive.clear();
        _final_effects_negative.clear();
        //Log::e("getPossibleFactChanges for: %s\n", TOSTR(sig));
        FactFrame& factFrame = _fact_frames.at(sig._name_id);
        Substitution s = Substitution(factFrame.sig._args, sig._args);

        if (factFrame.numNodes == 1) {
            substituteEffectsAndAdd(factFrame.effects, s, _final_effects_positive, _final_effects_negative);
            return groundEffects(_final_effects_positive, _final_effects_negative);
        } else {
            int subtaskIdx = 0;
            for (const auto& subtask: factFrame.subtasks) {
                if (!checkSubtaskDFS(subtask, _final_effects_positive, _final_effects_negative, _max_depth - 1, s)) {
                    _invalid_subtasks_found++;
                    //Log::e("subtask %i is not valid\n", subtaskIdx);
                    throw std::invalid_argument("getPFC: Operator has subtask with no valid children\n");
                }
                subtaskIdx++;
            }
            //Log::e("PFC: reduction is valid\n");
            return groundEffects(_final_effects_positive, _final_effects_negative);
        }
    }

    bool checkSubtaskDFS(NodeHashMap<int, PFCNode>* children, FlatHashMap<int, USigSet>& foundEffectsPos, FlatHashMap<int, USigSet>& foundEffectsNeg, int depth, Substitution& s) {
        bool valid = false;
        FlatHashMap<int, USigSet> foundEffectsPositiveCopy = foundEffectsPos;
        FlatHashMap<int, USigSet> foundEffectsNegativeCopy = foundEffectsNeg;

        for (const auto& [id, child]: *children) {
            //Log::e("Checking child %s\n", TOSTR(child.sig.substitute(s)));
            bool childValid = false;
            FlatHashMap<int, USigSet> childEffectsPositive = foundEffectsPositiveCopy;
            FlatHashMap<int, USigSet> childEffectsNegative = foundEffectsNegativeCopy;

            bool preconditionsValid = checkPreconditionValidityRigid(child.rigidPreconditions, s);
            if (preconditionsValid && _check_fluent_preconditions) {
                preconditionsValid = checkPreconditionValidityFluent(child.fluentPreconditions, childEffectsPositive, childEffectsNegative, s);
            }
            if (preconditionsValid) {
                childValid = true;
                if (depth == 0 || child.numNodes == 1) {
                    substituteEffectsAndAdd(child.effects, s, foundEffectsPos, foundEffectsNeg);
                } else {
                    for (const auto& subtask: child.subtasks) {
                        if (!checkSubtaskDFS(subtask, childEffectsPositive, childEffectsNegative, depth - 1, s)) {
                            childValid = false;
                            break;
                        }
                    }
                }
            }
            if (childValid) {
                valid = true;
                for (const auto& [id, sigset]: childEffectsPositive) {
                    Sig::unite(sigset, foundEffectsPos[id]);
                }
                for (const auto& [id, sigset]: childEffectsNegative) {
                    Sig::unite(sigset, foundEffectsNeg[id]);
                }
            }
        }
        return valid;
    }
};