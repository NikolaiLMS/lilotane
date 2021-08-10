#include "util/params.h"
#include "algo/fact_analysis.h"
#include "util/log.h"

class PFCTree: public FactAnalysis {
private:
    FactAnalysisPreprocessing _preprocessing;
    bool _check_fluent_preconditions;
    int _max_depth;
public:
    PFCTree(HtnInstance& htn, Parameters& params): 
        FactAnalysis(htn), _preprocessing(htn, _fact_frames, _util, params), _check_fluent_preconditions(bool(params.getIntParam("pfcFluentPreconditions", 0))), _max_depth(params.getIntParam("pfcTreeDepth", 1)) {

    }

    void computeFactFrames() {
        _preprocessing.computeFactFramesTree();
    }

    SigSet getPossibleFactChanges(const USignature& sig) {
        //Log::e("getPossibleFactChanges for: %s\n", TOSTR(sig));
        FlatHashMap<int, USigSet> effectsPositive;
        FlatHashMap<int, USigSet> effectsNegative;
        FactFrame& factFrame = _fact_frames.at(sig._name_id);
        Substitution s = Substitution(factFrame.sig._args, sig._args);

        if (factFrame.numNodes == 1) {
            substituteEffectsAndAdd(factFrame.effects, s, effectsPositive, effectsNegative);
        } else {
            std::vector<NodeHashMap<int, PFCNode>*> subtasks = factFrame.subtasks;
            for (int i = 0; i < _max_depth; i++) {
                USigSet foundEffectsNegative;
                USigSet foundEffectsPositive;
                std::vector<NodeHashMap<int, PFCNode>*> newSubtasks;
                for (const auto& subtask: subtasks) {
                    FlatHashMap<int, USigSet> effectsPositiveSubtask;
                    FlatHashMap<int, USigSet> effectsNegativeSubtask;
                    bool subtaskValid = false;
                    //Log::e("subtasksize: %i\n", (*subtask).size());
                    for (const auto& child: *subtask) {
                        //Log::e("Checking child: %s\n", TOSTR(child.second.sig._name_id));
                        bool preconditionsValid = checkPreconditionValidityRigid(child.second.rigidPreconditions, s);
                        if (preconditionsValid && _check_fluent_preconditions) {
                            preconditionsValid = checkPreconditionValidityFluent(child.second.fluentPreconditions, foundEffectsPositive, foundEffectsNegative, s);
                        }
                        if (preconditionsValid) {
                            substituteEffectsAndAdd(child.second.effects, s, effectsPositiveSubtask, effectsNegativeSubtask);
                            subtaskValid = true;
                            if (child.second.numNodes == 1 || i+1 == _max_depth) {
                                substituteEffectsAndAdd(child.second.effects, s, effectsPositive, effectsNegative);
                            } else {
                                for (const auto& subtask: child.second.subtasks) {
                                    newSubtasks.push_back(subtask);
                                }
                            }
                        }
                    }
                    if (!subtaskValid) {
                        //Log::e("Found invalid subtask at depth %i\n", i);
                        //Log::e("in getPFC for %s\n", TOSTR(sig));
                        _invalid_subtasks_found++;
                        if (i == 0) {
                            throw std::invalid_argument("getPFC: Operator has subtask with no valid children\n");
                        }
                    } else {
                        Sig::unite(groundEffectsQConst(effectsPositiveSubtask), foundEffectsPositive);
                        Sig::unite(groundEffectsQConst(effectsNegativeSubtask), foundEffectsNegative);
                    }
                }
                subtasks = newSubtasks;
            }
        }
        return groundEffects(effectsPositive, effectsNegative);
    }
};