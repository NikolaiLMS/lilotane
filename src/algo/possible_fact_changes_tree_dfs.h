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
        FactAnalysis(htn, params), _preprocessing(htn, _fact_frames, _util, params, _init_state), _check_fluent_preconditions(bool(params.getIntParam("pfcFluentPreconditions", 0))), _max_depth(params.getIntParam("pfcTreeDepth", 1)) {

    }

    void computeFactFrames() {
        _preprocessing.computeFactFramesTree();
    }

    SigSet getPossibleFactChanges(const USignature& sig) {
        _final_effects_positive.clear();
        _final_effects_negative.clear();
        FactFrame& factFrame = _fact_frames.at(sig._name_id);
        Substitution s = Substitution(factFrame.sig._args, sig._args);
        //Log::e("getPossibleFactChanges for: %s\n", TOSTR(sig));
        // for (const auto& eff: factFrame.effects) {
        //     Log::e("effects: %s\n", TOSTR(eff.substitute(s)));
        // }
        FlatHashMap<int, SigSet> postconditions;
        FlatHashMap<int, FlatHashSet<int>> freeArgRestrictions;
        if (factFrame.subtasks.size() == 0) {
            substituteEffectsAndAdd(factFrame.effects, s, _final_effects_positive, _final_effects_negative, postconditions);
            return groundEffects(_final_effects_positive, _final_effects_negative, freeArgRestrictions);
        } else {
            int subtaskIdx = 0;
            for (const auto& subtask: factFrame.subtasks) {
                //Log::e("Checking subtask %i\n", subtaskIdx);
                if (!checkSubtaskDFS(subtask, _final_effects_positive, _final_effects_negative, _max_depth - 1, s, freeArgRestrictions, postconditions)) {
                    _invalid_subtasks_found++;
                    Log::e("subtask %i is not valid\n", subtaskIdx);
                    throw std::invalid_argument("getPFC: Operator has subtask with no valid children\n");
                }
                subtaskIdx++;
            }
            //Log::e("PFC: reduction is valid\n");

            SigSet pfc =  groundEffects(_final_effects_positive, _final_effects_negative, freeArgRestrictions);
            //Log::e("PFC: %s\n", TOSTR(pfc));
            return pfc;
        }
    }

    bool checkSubtaskDFS(NodeHashMap<int, PFCNode>* children, FlatHashMap<int, USigSet>& foundEffectsPos, FlatHashMap<int, USigSet>& foundEffectsNeg, 
        int depth, Substitution& s, FlatHashMap<int, FlatHashSet<int>>& globalFreeArgRestrictions, FlatHashMap<int, SigSet>& postconditions) {
        bool valid = false;
        FlatHashMap<int, USigSet> foundEffectsPositiveCopy = foundEffectsPos;
        FlatHashMap<int, USigSet> foundEffectsNegativeCopy = foundEffectsNeg;
        FlatHashMap<int, SigSet> newPostconditions;
        bool firstChild = true;
        for (const auto& [id, child]: *children) {
            //Log::e("Checking child %s at depth %i\n", TOSTR(child.sig.substitute(s)), _max_depth - depth);
            bool childValid = false;
            FlatHashMap<int, USigSet> childEffectsPositive = foundEffectsPositiveCopy;
            FlatHashMap<int, USigSet> childEffectsNegative = foundEffectsNegativeCopy;
            FlatHashMap<int, SigSet> childPostconditions = postconditions;
            bool preconditionsValid = restrictNewVariables(child.rigidPreconditions, s, globalFreeArgRestrictions, _preprocessing.getRigidPredicateCache(), child.newArgs);
            if (preconditionsValid) preconditionsValid = checkPreconditionValidityRigid(child.rigidPreconditions, s, globalFreeArgRestrictions, _preprocessing.getRigidPredicateCache());
            if (preconditionsValid && _check_fluent_preconditions) {
                preconditionsValid = checkPreconditionValidityFluent(child.fluentPreconditions, childEffectsPositive, childEffectsNegative, s, globalFreeArgRestrictions, postconditions);
            }
            if (preconditionsValid) {
                childValid = true;
                if (depth == 0 || child.subtasks.size() == 0) {
                    substituteEffectsAndAdd(child.effects, s, foundEffectsPos, foundEffectsNeg, childPostconditions);
                    for (const auto& postcondition: child.postconditions) {
                        childPostconditions[postcondition._usig._name_id].insert(postcondition.substitute(s));
                    }
                } else {
                    for (const auto& subtask: child.subtasks) {
                        if (!checkSubtaskDFS(subtask, childEffectsPositive, childEffectsNegative, depth - 1, s, globalFreeArgRestrictions, childPostconditions)) {
                            childValid = false;
                            break;
                        }
                    }
                }
            }
            if (childValid) {
                if (firstChild) {
                    newPostconditions = childPostconditions;
                    firstChild = false;
                } else {
                    std::vector<int> toDelete;
                    for (auto& [id, signatures]: newPostconditions) {
                        if (childPostconditions.count(id) && childPostconditions[id].size() > 0) {
                            Sig::intersect(childPostconditions[id], signatures);
                        } else {
                            toDelete.push_back(id);
                        }
                    }
                    for (const auto& id: toDelete) {
                        newPostconditions.erase(id);
                    }
                }
                valid = true;
                for (const auto& [id, sigset]: childEffectsPositive) {
                    Sig::unite(sigset, foundEffectsPos[id]);
                }
                for (const auto& [id, sigset]: childEffectsNegative) {
                    Sig::unite(sigset, foundEffectsNeg[id]);
                }
            }
        }
        if (valid) {
            postconditions = newPostconditions;
        }
        return valid;
    }
};