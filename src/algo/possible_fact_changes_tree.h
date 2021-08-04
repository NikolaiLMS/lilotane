
#include "algo/fact_analysis.h"
#include "util/log.h"

class PFCTree: public FactAnalysis {
private:
    FactAnalysisPreprocessing _preprocessing;
public:
    PFCTree(HtnInstance& htn): FactAnalysis(htn), _preprocessing(htn, _fact_frames, _util) {

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

        int MAX_DEPTH = 1;
        if (factFrame.numNodes == 1) {
            substituteEffectsAndAdd(factFrame.effects, s, effectsPositive, effectsNegative);
        } else {
            std::vector<NodeHashMap<int, PFCNode>*> subtasks = factFrame.subtasks;
            for (int i = 0; i < MAX_DEPTH; i++) {
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
                        // if (preconditionsValid) {
                            // substitutedPreconditions = SigSet();
                            // for (const auto& prereq: child.second.fluentPreconditions) {
                            //     //Log::e("Unsubstituted prereq: %s\n", TOSTR(prereq));
                            //     substitutedPreconditions.insert(prereq.substitute(s));
                            // }
                            // preconditionsValid = checkPreconditionValidityFluent(substitutedPreconditions, foundEffectsPositive, foundEffectsNegative);
                        // }
                        if (preconditionsValid) {
                            //substituteEffectsAndAdd(child.second.effects, s, effectsPositiveSubtask, effectsNegativeSubtask);
                            subtaskValid = true;
                            if (child.second.numNodes == 1 || i+1 == MAX_DEPTH) {
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
                    } //else {
                    //     USigSet effectsToGround = removeDominated(effectsPositiveSubtask);
                    //     USigSet groundEffects;
                    //     for (const auto& positiveEffect: effectsToGround) {
                    //         for (const USignature& groundFact : ArgIterator::getFullInstantiation(positiveEffect, _htn)) {
                    //             groundEffects.emplace(groundFact);
                    //         }
                    //     }
                    //     Sig::unite(foundEffectsPositive, groundEffects);

                    //     effectsToGround = removeDominated(effectsNegativeSubtask);
                    //     groundEffects = USigSet();
                    //     for (const auto& negativeEffect: effectsToGround) {
                    //         for (const USignature& groundFact : ArgIterator::getFullInstantiation(negativeEffect, _htn)) {
                    //             groundEffects.emplace(groundFact);
                    //         }
                    //     }
                    //     Sig::unite(foundEffectsNegative, groundEffects);
                    // }
                }
                subtasks = newSubtasks;
            }
        }
        return groundEffects(effectsPositive, effectsNegative);
    }
};