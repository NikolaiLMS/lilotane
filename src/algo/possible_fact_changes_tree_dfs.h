#include "util/params.h"
#include "algo/fact_analysis.h"
#include "util/log.h"

class PFCTreeDFS: public FactAnalysis {
private:
    FactAnalysisPreprocessing _preprocessing;
    bool _check_fluent_preconditions;
    int _max_depth;
    int _init_node_limit;
    int _invalid_node_increase;
    int _restrict_vars_increase;
    int _nodes_left;
public:
    PFCTreeDFS(HtnInstance& htn, Parameters& params): 
        FactAnalysis(htn, params), _preprocessing(htn, _fact_frames, _util, params, _init_state), 
        _check_fluent_preconditions(bool(params.getIntParam("pfcFluentPreconditions", 0))), _max_depth(params.getIntParam("pfcTreeDepth", 1)),
        _init_node_limit(params.getIntParam("pfcInitNodeLimit")), _invalid_node_increase(params.getIntParam("pfcInvalidNodeIncrease")),
        _restrict_vars_increase(params.getIntParam("pfcRestrictVarsIncrease")) {
    }

    void computeFactFrames() {
        _preprocessing.computeFactFramesTree();
    }

    SigSet getPossibleFactChanges(const USignature& sig) {
        _nodes_left = _init_node_limit;
        _final_effects_positive.clear();
        _final_effects_negative.clear();
        // Log::e("old postconditions: \n");
        // for (const auto& [id, sigset]: _postconditions) {
        //     Log::e("%s: %s\n", TOSTR(id), TOSTR(sigset));
        // }
        FactFrame& factFrame = _fact_frames.at(sig._name_id);
        Substitution s = Substitution(factFrame.sig._args, sig._args);
        //Log::e("getPossibleFactChanges for: %s\n", TOSTR(sig));
        for (const auto& precondition: factFrame.preconditions) {
            Signature substitutedPrecondition = precondition.substitute(s);
            substitutedPrecondition.negate();
            if (_postconditions.count(substitutedPrecondition._usig._name_id) && _postconditions[substitutedPrecondition._usig._name_id].count(substitutedPrecondition)) {
                //Log::e("negated substitutedPrecondition: %s found in postconditions\n", TOSTR(substitutedPrecondition));
                throw std::invalid_argument("getPFC: Operations preconditions invalid because of postconditions\n");
            }
        }
        // for (const auto& eff: factFrame.effects) {
        //     Log::e("effects: %s\n", TOSTR(eff.substitute(s)));
        // }
        FlatHashMap<int, SigSet> postconditionCopy = _postconditions;
        FlatHashMap<int, FlatHashSet<int>> freeArgRestrictions;
        if (factFrame.subtasks.size() == 0 || _nodes_left < factFrame.numDirectChildren) {
            substituteEffectsAndAdd(factFrame.effects, s, _final_effects_positive, _final_effects_negative, postconditionCopy, freeArgRestrictions);
            for (const auto& postcondition: factFrame.postconditions) {
                postconditionCopy[postcondition._usig._name_id].insert(postcondition.substitute(s));
                //Log::e("Adding postcondition %s\n", TOSTR(postcondition));
            }
            for (const auto& postcondition: factFrame.negatedPostconditions) {
                Signature positiveCopy = postcondition;
                positiveCopy.negate();
                if (!postconditionCopy[postcondition._usig._name_id].count(positiveCopy.substitute(s))) {
                    postconditionCopy[postcondition._usig._name_id].insert(postcondition.substitute(s));
                    //Log::e("Adding postcondition %s\n", TOSTR(postcondition));
                }
            }
            if (_new_position) {
                _new_postconditions = postconditionCopy;
                _new_position = false;
            } else {
                std::vector<int> toDelete;
                for (auto& [id, signatures]: _new_postconditions) {
                    if (postconditionCopy.count(id) && postconditionCopy[id].size() > 0) {
                        Sig::intersect(postconditionCopy[id], signatures);
                    } else {
                        toDelete.push_back(id);
                    }
                }
                for (const auto& id: toDelete) {
                    _new_postconditions.erase(id);
                }
            }
            // Log::e("NewPostconditions: \n");
            // for (const auto& [id, sigset]: _new_postconditions) {
            //     Log::e("%s: %s\n", TOSTR(id), TOSTR(sigset));
            // }
            return groundEffects(_final_effects_positive, _final_effects_negative, freeArgRestrictions);
        } else {
            _nodes_left -= factFrame.numDirectChildren;
            int subtaskIdx = 0;
            for (const auto& subtask: factFrame.subtasks) {
                //Log::e("Checking subtask %i\n", subtaskIdx);
                if (!checkSubtaskDFS(subtask, _final_effects_positive, _final_effects_negative, _max_depth - 1, s, freeArgRestrictions, postconditionCopy)) {
                    _invalid_subtasks_found++;
                    //Log::e("subtask %i is not valid\n", subtaskIdx);
                    throw std::invalid_argument("getPFC: Operator has subtask with no valid children\n");
                }
                subtaskIdx++;
            }
            //Log::e("PFC: reduction is valid\n");
            if (_new_position) {
                _new_postconditions = postconditionCopy;
                _new_position = false;
            } else {
                std::vector<int> toDelete;
                for (auto& [id, signatures]: _new_postconditions) {
                    if (postconditionCopy.count(id) && postconditionCopy[id].size() > 0) {
                        Sig::intersect(postconditionCopy[id], signatures);
                    } else {
                        toDelete.push_back(id);
                    }
                }
                for (const auto& id: toDelete) {
                    _new_postconditions.erase(id);
                }
            }
            // Log::e("NewPostconditions: \n");
            // for (const auto& [id, sigset]: _new_postconditions) {
            //     Log::e("%s: %s\n", TOSTR(id), TOSTR(sigset));
            // }
            return groundEffects(_final_effects_positive, _final_effects_negative, freeArgRestrictions);
            //Log::e("PFC: %s\n", TOSTR(pfc));
        }
    }

    bool checkSubtaskDFS(NodeHashMap<int, PFCNode>* children, FlatHashMap<int, USigSet>& foundEffectsPos, FlatHashMap<int, USigSet>& foundEffectsNeg,
        int depth, Substitution& s, FlatHashMap<int, FlatHashSet<int>>& globalFreeArgRestrictions, FlatHashMap<int, SigSet>& postconditions) {
        bool valid = false;
        FlatHashMap<int, USigSet> foundEffectsPositiveCopy = foundEffectsPos;
        FlatHashMap<int, USigSet> foundEffectsNegativeCopy = foundEffectsNeg;
        FlatHashMap<int, SigSet> oldPostconditions = postconditions;
        bool firstChild = true;

        for (const auto& [id, child]: *children) {
            // Log::e("Checking child %s at depth %i\n", TOSTR(child.sig.substitute(s)), _max_depth - depth);
            // Log::e("%i\n", child.sig._name_id);
            bool childValid = false;
            FlatHashMap<int, USigSet> childEffectsPositive = foundEffectsPositiveCopy;
            FlatHashMap<int, USigSet> childEffectsNegative = foundEffectsNegativeCopy;
            FlatHashMap<int, SigSet> childPostconditions = oldPostconditions;
            bool restrictedVars = false;
            bool preconditionsValid = restrictNewVariables(child.rigidPreconditions, child.fluentPreconditions, s, globalFreeArgRestrictions, _preprocessing.getRigidPredicateCache(), 
                child.newArgs, foundEffectsPositiveCopy, foundEffectsNegativeCopy, restrictedVars, oldPostconditions);
            if (preconditionsValid) preconditionsValid = checkPreconditionValidityRigid(child.rigidPreconditions, s, globalFreeArgRestrictions, _preprocessing.getRigidPredicateCache());
            if (preconditionsValid && _check_fluent_preconditions) {
                preconditionsValid = checkPreconditionValidityFluent(child.fluentPreconditions, childEffectsPositive, childEffectsNegative, s, globalFreeArgRestrictions, oldPostconditions);
            }
            if (preconditionsValid) {
                if (restrictedVars) {
                    _nodes_left += _restrict_vars_increase;
                }
                childValid = true;
                if (child.subtasks.size() == 0 || _nodes_left < child.numDirectChildren) {
                    substituteEffectsAndAdd(child.effects, s, foundEffectsPos, foundEffectsNeg, childPostconditions, globalFreeArgRestrictions);
                    for (const auto& postcondition: child.postconditions) {
                        childPostconditions[postcondition._usig._name_id].insert(postcondition.substitute(s));
                        // Log::e("Adding postcondition %s\n", TOSTR(postcondition));
                    }
                    for (const auto& postcondition: child.negatedPostconditions) {
                        Signature positiveCopy = postcondition;
                        positiveCopy.negate();
                        if (!childPostconditions[postcondition._usig._name_id].count(positiveCopy.substitute(s))) {
                            childPostconditions[postcondition._usig._name_id].insert(postcondition.substitute(s));
                            // Log::e("Adding postcondition %s\n", TOSTR(postcondition));
                        }
                    }
                } else {
                    _nodes_left -= child.numDirectChildren;
                    for (const auto& subtask: child.subtasks) {
                        if (!checkSubtaskDFS(subtask, childEffectsPositive, childEffectsNegative, depth - 1, s, globalFreeArgRestrictions, childPostconditions)) {
                            childValid = false;
                            break;
                        }
                    }
                }
            } else {
                _nodes_left += _invalid_node_increase;
            }
            if (childValid) {
                if (firstChild) {
                    postconditions = childPostconditions;
                    firstChild = false;
                } else {
                    std::vector<int> toDelete;
                    for (auto& [id, signatures]: postconditions) {
                        if (childPostconditions.count(id) && childPostconditions[id].size() > 0) {
                            Sig::intersect(childPostconditions[id], signatures);
                        } else {
                            toDelete.push_back(id);
                        }
                    }
                    for (const auto& id: toDelete) {
                        postconditions.erase(id);
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
            // Log::e("NewPostconditions: \n");
            // for (const auto& [id, sigset]: postconditions) {
            //     Log::e("%s: %s\n", TOSTR(id), TOSTR(sigset));
            // }
            for (const auto& [id, signatures]: postconditions) {
                for (const auto& postcondition: signatures) {
                    Signature negatedCopy = postcondition;
                    negatedCopy.negate();
                    if (negatedCopy._negated) {
                        foundEffectsNeg[id].erase(negatedCopy._usig);
                    } else {
                        foundEffectsPos[id].erase(negatedCopy._usig);
                    }
                }
            }
        }
        return valid;
    }
};