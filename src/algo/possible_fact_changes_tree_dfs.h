#include "util/params.h"
#include "algo/fact_analysis.h"
#include "util/log.h"
#include <iostream>
#include <iomanip>

class PFCTreeDFS: public FactAnalysis {
private:
    FactAnalysisPreprocessing _preprocessing;
    bool _check_fluent_preconditions;
    int _max_depth;
    int _init_node_limit;
    int _invalid_node_increase;
    float _nodes_left;
public:
    PFCTreeDFS(HtnInstance& htn, Parameters& params): 
        FactAnalysis(htn, params), _preprocessing(htn, _fact_frames, _util, params, _init_state), 
        _check_fluent_preconditions(bool(params.getIntParam("pfcFluentPreconditions", 0))), _max_depth(params.getIntParam("pfcTreeDepth", 1)),
        _init_node_limit(params.getIntParam("pfcInitNodeLimit")), _invalid_node_increase(params.getIntParam("pfcInvalidNodeIncrease")){
    }

    void computeFactFrames() {
        _preprocessing.computeFactFramesTree();
    }

    SigSet getPossibleFactChanges(const USignature& sig) {
        _nodes_left = float(_init_node_limit);
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
        NodeHashMap<int, SigSet> postconditionCopy = _postconditions;
        NodeHashMap<int, FlatHashSet<int>> freeArgRestrictions;
        if (factFrame.subtasks.size() == 0 || _nodes_left < factFrame.numDirectChildren) {
            substituteEffectsAndAdd(factFrame.effects, s, _final_effects_positive, _final_effects_negative, postconditionCopy, freeArgRestrictions);
            for (const auto& postcondition: factFrame.postconditions) {
                postconditionCopy[postcondition._usig._name_id].insert(postcondition.substitute(s));
                //Log::e("Adding postcondition %s\n", TOSTR(postcondition));
            }
            for (const auto& postcondition: factFrame.negatedPostconditions) {
                postconditionCopy[postcondition._usig._name_id].insert(postcondition.substitute(s));
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
            _variables_restricted += freeArgRestrictions.size();
            return groundEffects(_final_effects_positive, _final_effects_negative, freeArgRestrictions);
        } else {
            _nodes_left -= factFrame.numDirectChildren;
            int subtaskIdx = 0;
            for (const auto& subtask: factFrame.subtasks) {
                //Log::e("Checking subtask %i\n", subtaskIdx);
                if (!checkSubtaskDFS(subtask, _final_effects_positive, _final_effects_negative, _max_depth - 1, s, freeArgRestrictions, postconditionCopy)) {
                    _invalid_subtasks_found++;
                    //Log::e("subtask %i is not valid\n", subtaskIdx);
                    _variables_restricted += freeArgRestrictions.size();
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
            _variables_restricted += freeArgRestrictions.size();
            return groundEffects(_final_effects_positive, _final_effects_negative, freeArgRestrictions);
            //Log::e("PFC: %s\n", TOSTR(pfc));
        }
    }

    bool checkSubtaskDFS(NodeHashMap<int, PFCNode>* children, NodeHashMap<int, USigSet>& foundEffectsPos, NodeHashMap<int, USigSet>& foundEffectsNeg,
        int depth, Substitution& s, NodeHashMap<int, FlatHashSet<int>>& globalFreeArgRestrictions, NodeHashMap<int, SigSet>& postconditions) {
        bool valid = false;
        NodeHashMap<int, USigSet> foundEffectsPositiveCopy = foundEffectsPos;
        NodeHashMap<int, USigSet> foundEffectsNegativeCopy = foundEffectsNeg;
        NodeHashMap<int, SigSet> oldPostconditions = postconditions;
        bool firstChild = true;

        for (const auto& [id, child]: *children) {
            FactFrame& ff = _fact_frames[id];
            Substitution newSub = child.substitution.concatenate(s);

            // Log::e("Checking child %s at depth %i\n", TOSTR(child.sig.substitute(s)), _max_depth - depth);
            // Log::e("%i\n", child.sig._name_id);
            bool childValid = false;
            NodeHashMap<int, USigSet> childEffectsPositive = foundEffectsPositiveCopy;
            NodeHashMap<int, USigSet> childEffectsNegative = foundEffectsNegativeCopy;
            NodeHashMap<int, SigSet> childPostconditions = oldPostconditions;

            SigSet subtitutedRigidPreconditions = ff.rigidPreconditions;
            SigSet subtitutedFluentPreconditions = ff.fluentPreconditions;
            size_t oldArgRestrictionSize = globalFreeArgRestrictions.size();
            bool preconditionsValid = restrictNewVariables(subtitutedRigidPreconditions, subtitutedFluentPreconditions, newSub, globalFreeArgRestrictions, _preprocessing.getRigidPredicateCache(), 
                child.newArgs, foundEffectsPositiveCopy, foundEffectsNegativeCopy, oldPostconditions, s);
            if (preconditionsValid) preconditionsValid = checkPreconditionValidityRigid(subtitutedRigidPreconditions, globalFreeArgRestrictions);
            if (preconditionsValid && _check_fluent_preconditions) {
                preconditionsValid = checkPreconditionValidityFluent(subtitutedFluentPreconditions, childEffectsPositive, childEffectsNegative, globalFreeArgRestrictions, oldPostconditions);
            }
            if (preconditionsValid) {
                if (globalFreeArgRestrictions.size() > oldArgRestrictionSize) {
                    _nodes_left += _invalid_node_increase;
                    _nodes_variables_restricted++;
                }
                childValid = true;
                if (child.subtasks.size() == 0 || _nodes_left < child.numDirectChildren) {
                    substituteEffectsAndAdd(ff.effects, newSub, foundEffectsPos, foundEffectsNeg, childPostconditions, globalFreeArgRestrictions);
                    for (const auto& postcondition: ff.postconditions) {
                        childPostconditions[postcondition._usig._name_id].insert(postcondition.substitute(newSub));
                        // Log::e("Adding postcondition %s\n", TOSTR(postcondition));
                    }
                    for (const auto& postcondition: ff.negatedPostconditions) {
                        childPostconditions[postcondition._usig._name_id].insert(postcondition.substitute(newSub));
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