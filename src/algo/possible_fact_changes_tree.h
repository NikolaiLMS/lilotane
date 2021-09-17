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
        FactAnalysis(htn, params), _preprocessing(htn, _fact_frames, _util, params, _init_state), _check_fluent_preconditions(bool(params.getIntParam("pfcFluentPreconditions", 0))), _max_depth(params.getIntParam("pfcTreeDepth", 1)) {

    }

    void computeFactFrames() {
        _preprocessing.computeFactFramesTree();
    }

    SigSet getPossibleFactChanges(const USignature& sig) {
        FlatHashMap<int, SigSet> postconditions;
        //Log::e("getPossibleFactChanges for: %s\n", TOSTR(sig));
        _final_effects_positive.clear();
        _final_effects_negative.clear();
        FactFrame& factFrame = _fact_frames.at(sig._name_id);
        Substitution s = Substitution(factFrame.sig._args, sig._args);
        FlatHashMap<int, FlatHashSet<int>> freeArgRestrictions;
        if (factFrame.numNodes == 1) {
            substituteEffectsAndAdd(factFrame.effects, s, _final_effects_positive, _final_effects_negative, postconditions);
        } else {
            std::vector<NodeHashMap<int, PFCNode>*> subtasks = factFrame.subtasks;
            for (int i = 0; i < _max_depth; i++) {
                FlatHashMap<int, USigSet> foundEffectsNegative;
                FlatHashMap<int, USigSet> foundEffectsPositive;
                std::vector<NodeHashMap<int, PFCNode>*> newSubtasks;
                for (const auto& subtask: subtasks) {
                    FlatHashMap<int, USigSet> effectsPositiveSubtask;
                    FlatHashMap<int, USigSet> effectsNegativeSubtask;
                    bool subtaskValid = false;
                    //Log::e("subtasksize: %i\n", (*subtask).size());
                    for (const auto& child: *subtask) {
                        // Log::e("Layer %i\n", i);
                        // Log::e("Checking child: %s\n", TOSTR(child.second.sig));
                        // Log::e("Checking child: %s\n", TOSTR(child.second.sig.substitute(s)));
                        bool preconditionsValid = checkPreconditionValidityRigid(child.second.rigidPreconditions, s, freeArgRestrictions, _preprocessing.getRigidPredicateCache());
                        if (preconditionsValid && _check_fluent_preconditions) {
                            preconditionsValid = checkPreconditionValidityFluent(child.second.fluentPreconditions, foundEffectsPositive, foundEffectsNegative, s, freeArgRestrictions, postconditions);
                        }
                        if (preconditionsValid) {
                            substituteEffectsAndAdd(child.second.effects, s, effectsPositiveSubtask, effectsNegativeSubtask, postconditions);
                            subtaskValid = true;
                            if (child.second.numNodes == 1 || i+1 == _max_depth) {
                                substituteEffectsAndAdd(child.second.effects, s, _final_effects_positive, _final_effects_negative, postconditions);
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
                        if (i == 0) {
                            _invalid_subtasks_found++;
                            throw std::invalid_argument("getPFC: Operator has subtask with no valid children\n");
                        }
                    } else {
                        for (const auto& [id, sigset]: effectsPositiveSubtask) {
                            Sig::unite(sigset, foundEffectsPositive[id]);
                        }
                        for (const auto& [id, sigset]: effectsNegativeSubtask) {
                            Sig::unite(sigset, foundEffectsNegative[id]);
                        }
                    }
                }
                subtasks = newSubtasks;
            }
        }
        return groundEffects(_final_effects_positive, _final_effects_negative, freeArgRestrictions);
    }
};