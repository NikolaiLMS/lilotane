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
        _final_effects_positive.clear();
        _final_effects_negative.clear();
        //Log::e("getPossibleFactChanges for: %s\n", TOSTR(sig));
        FactFrame& factFrame = _fact_frames.at(sig._name_id);
        Substitution s = Substitution(factFrame.sig._args, sig._args);

        if (factFrame.numNodes == 1) {
            substituteEffectsAndAdd(factFrame.effects, s, _final_effects_positive, _final_effects_negative);
            return groundEffects(_final_effects_positive, _final_effects_negative);
        } else {
            std::vector<USigSet*> foundEffectsPositive;
            std::vector<USigSet*> foundEffectsNegative;
            int subtaskIdx = 0;
            for (const auto& subtask: factFrame.subtasks) {
                if (!checkSubtaskDFS(subtask, foundEffectsPositive, foundEffectsNegative, _max_depth - 1, s)) {
                    _invalid_subtasks_found++;
                    for (const auto pointer: foundEffectsPositive) {
                        free(pointer);
                    }
                    for (const auto pointer: foundEffectsNegative) {
                        free(pointer);
                    }
                    //Log::e("subtask %i is not valid\n", subtaskIdx);
                    throw std::invalid_argument("getPFC: Operator has subtask with no valid children\n");
                }
                subtaskIdx++;
            }
            for (const auto pointer: foundEffectsPositive) {
                free(pointer);
            }
            for (const auto pointer: foundEffectsNegative) {
                free(pointer);
            }
            //Log::e("PFC: reduction is valid\n");
            return groundEffects(_final_effects_positive, _final_effects_negative);
        }
    }

    bool checkSubtaskDFS(NodeHashMap<int, PFCNode>* children, std::vector<USigSet*>& foundEffectsPos, std::vector<USigSet*>& foundEffectsNeg, 
            int depth, Substitution& s) {
        bool valid = false;
        std::vector<USigSet*> foundEffectsPositiveCopy = foundEffectsPos;
        std::vector<USigSet*> foundEffectsNegativeCopy = foundEffectsNeg;

        for (const auto& [id, child]: *children) {
            //Log::e("Checking child %s\n", TOSTR(child.sig.substitute(s)));
            bool childValid = false;
            std::vector<USigSet*> childEffectsPositive = foundEffectsPositiveCopy;
            std::vector<USigSet*> childEffectsNegative = foundEffectsNegativeCopy;

            bool preconditionsValid = checkPreconditionValidityRigid(child.rigidPreconditions, s);
            if (preconditionsValid && _check_fluent_preconditions) {
                preconditionsValid = checkPreconditionValidityFluent(child.fluentPreconditions, childEffectsPositive, childEffectsNegative, s);
            }
            if (preconditionsValid) {
                childValid = true;
                if (depth == 0 || child.numNodes == 1) {
                    substituteEffectsAndAdd(child.effects, s, _final_effects_positive, _final_effects_negative);
                    
                    FlatHashMap<int, USigSet> liftedSubstitutedTempPositive;
                    FlatHashMap<int, USigSet> liftedSubstitutedTempNegative;
                    substituteEffectsAndAdd(child.effects, s, liftedSubstitutedTempPositive, liftedSubstitutedTempNegative);

                    USigSet* newSigSetPositive = new USigSet;
                    USigSet* newSigSetNegative = new USigSet;
                    groundEffectsQConstIntoTarget(liftedSubstitutedTempPositive, newSigSetPositive);
                    groundEffectsQConstIntoTarget(liftedSubstitutedTempNegative, newSigSetNegative);
                    foundEffectsPos.push_back(newSigSetPositive);
                    foundEffectsNeg.push_back(newSigSetNegative);
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
                if (childEffectsPositive.size() > foundEffectsPositiveCopy.size()) {
                    if (foundEffectsPos.size() == foundEffectsPositiveCopy.size()) {
                        foundEffectsPos.push_back(childEffectsPositive[foundEffectsPositiveCopy.size()]);
                    }
                    for (int i = foundEffectsPositiveCopy.size() + 1; i < childEffectsPositive.size(); i++) {
                        Sig::unite(*(childEffectsPositive[i]), *(foundEffectsPos[foundEffectsPos.size()-1]));
                        free(childEffectsPositive[i]);
                    }
                }
                if (childEffectsNegative.size() > foundEffectsNegativeCopy.size()) {
                    if (foundEffectsNeg.size() == foundEffectsNegativeCopy.size()) {
                        foundEffectsNeg.push_back(childEffectsNegative[foundEffectsNegativeCopy.size()]);
                    }
                    for (int i = foundEffectsNegativeCopy.size() + 1; i < childEffectsNegative.size(); i++) {
                        Sig::unite(*(childEffectsNegative[i]), *(foundEffectsNeg[foundEffectsNeg.size()-1]));
                        free(childEffectsNegative[i]);
                    }
                }
            } else {
                for (int i = foundEffectsPositiveCopy.size(); i < childEffectsPositive.size(); i++) {
                    free(childEffectsPositive[i]);
                }
                for (int i = foundEffectsNegativeCopy.size(); i < childEffectsNegative.size(); i++) {
                    free(childEffectsNegative[i]);
                }
            }
        }
        for (int i = foundEffectsPos.size()-1; i > 0 ; i--) {
            Sig::unite(*foundEffectsPos[i], *foundEffectsPos[0]);
            free(foundEffectsPos[i]);
            foundEffectsPos.pop_back();
        }
        for (int i = foundEffectsNeg.size()-1; i > 0 ; i--) {
            Sig::unite(*foundEffectsNeg[i], *foundEffectsNeg[0]);
            free(foundEffectsNeg[i]);
            foundEffectsNeg.pop_back();
        }
        return valid;
    }
};