
#include "util/log.h"
#include "algo/compute_fact_frame.h"
#include "data/fact_frame.h"
#include "algo/topological_ordering.h"

int DEPTH_LIMIT = 1;

void FactAnalysisPreprocessing::computeFactFramesBase() {

    std::vector<int> orderedOpIds = calcOrderedOpList();

    _fluent_predicates = findFluentPredicates(orderedOpIds);

    fillFactFramesBase(orderedOpIds);

    extendPreconditions(orderedOpIds);

    // for (const auto& [id, ff] : _fact_frames) {
    //     Log::d("FF %s effects: %s\n", TOSTR(ff.sig), TOSTR(ff.effects));
    //     Log::d("FF: %s\n", TOSTR(ff));
    // }
}


void FactAnalysisPreprocessing::computeFactFramesTree() {

    std::vector<int> orderedOpIds = calcOrderedOpList();

    _fluent_predicates = findFluentPredicates(orderedOpIds);

    fillRigidPredicateCache();

    fillFactFramesBase(orderedOpIds);

    extendPreconditions(orderedOpIds);

    fillPFCNodesTopDownBFS(orderedOpIds);

    // for (const auto& [id, ff] : _fact_frames) {
    //     printFactFrameBFS(id);
    // }
}

void FactAnalysisPreprocessing::fillRigidPredicateCache() {
    for (const auto& fact: _init_state) {
        if (!_fluent_predicates.count(fact._name_id)) {
            for (size_t argPosition = 0; argPosition < fact._args.size(); argPosition++) {
                USignature copy = fact;
                copy._args[argPosition] = _htn.nameId("??_");
                _rigid_predicate_cache[fact._name_id][copy].insert(fact._args[argPosition]);
            }
        }
    }
}

std::vector<int> FactAnalysisPreprocessing::calcOrderedOpList() {
    // Build an adjacency map for the (lifted) operations in the problem
    std::map<int, std::vector<int>> orderingOplist;
    // Create local copy of action templates because getRepetitionOfAction(·) 
    // may manipulate the action templates internally 
    auto templates = _htn.getActionTemplates();
    for (const auto& [aId, action] : templates) {
        if (_htn.isActionRepetition(aId)) continue;
        int repId = _htn.getRepetitionOfAction(action.getSignature())._name_id;
        // Repeated actions have no outgoing edges to other operations: insert empty vector
        orderingOplist[repId];
        // "Normal" actions have their repetition as their only outgoing edge
        orderingOplist[aId].push_back(repId);
    }
    for (const auto& [rId, reduction] : _htn.getReductionTemplates()) {
        // For each reduction, find all children and add their IDs as outgoing edges
        FlatHashSet<int> childIds;
        for (size_t i = 0; i < reduction.getSubtasks().size(); i++) {
            std::vector<USignature> children;
            _util.getTraversal().getPossibleChildren(reduction.getSubtasks(), i, children);
            for (const auto& child : children) {
                childIds.insert(child._name_id);
            }
        }
        orderingOplist[rId].insert(orderingOplist[rId].end(), childIds.begin(), childIds.end());
    }

    // Perform a topological ordering on the nodes (operations).
    // As the graph may be cyclic, the ordering is not flawless
    // and can contain forward references.
    std::vector<int> orderedOpIds = TopologicalOrdering::compute(orderingOplist);
    //Log::d("FF all: { %s }\n", TOSTR(orderedOpIds));
    return orderedOpIds;
}

void FactAnalysisPreprocessing::fillFactFramesAction(int& opId, int& aId, bool& change) {
    //Log::e("filling action fact frame for id %i\n", opId);
    Action action = _htn.getAnonymousAction(aId);
    if (_fact_frames[opId].sig != action.getSignature()) {
        _fact_frames[opId].sig = action.getSignature();
        _fact_frames[opId].preconditions = action.getPreconditions();
        _fact_frames[opId].postconditions = action.getPreconditions();
        _fact_frames[opId].effects = action.getEffects();
        FlatHashSet<int> posEffPredicates;
        for (const auto& eff: action.getEffects()) {
            for (const auto& postcondition: action.getPreconditions()) {
                if (eff._usig._name_id == postcondition._usig._name_id && eff._negated != postcondition._negated) {
                    _fact_frames[opId].postconditions.erase(postcondition);
                }
            }
            if (!eff._negated) {
                posEffPredicates.insert(eff._usig._name_id);
                Signature negatedEffectCopy = eff;
                negatedEffectCopy.negate();
                if (_fact_frames[opId].effects.count(negatedEffectCopy)) {
                    _fact_frames[opId].effects.erase(negatedEffectCopy);
                }
            }
        }
        if (_postcondition_pruning) {
            for (const auto& eff: _fact_frames[opId].effects) {
                if (!eff._negated) {
                    _fact_frames[opId].postconditions.insert(eff);
                } else {
                    if (!posEffPredicates.count(eff._usig._name_id)) _fact_frames[opId].negatedPostconditions.insert(eff);
                }
            }
        }
        change = true;
    } // else: fact frame already set
}

void FactAnalysisPreprocessing::fillFactFramesBase(std::vector<int>& orderedOpIds) {
    bool change = true;
    int numEffects;
    while (change) {
        numEffects = 0;
        change = false;
        // Iterate over each (lifted) operation in reversed order
        for (int i = orderedOpIds.size()-1; i >= 0; i--) {
            int opId = orderedOpIds[i];
            //Log::d("FF %i : %s\n", i, TOSTR(opId));
            if (_htn.isAction(opId) || _htn.isActionRepetition(opId)) {
                // Action: Setting fact frame is trivial
                int aId = opId;
                if (_htn.isActionRepetition(opId)) aId = _htn.getActionNameFromRepetition(opId);
                fillFactFramesAction(opId, aId, change);
                numEffects += _fact_frames[opId].effects.size();
            } else if (_htn.isReductionPrimitivizable(opId)) {
                // Primitivization of a reduction, i.e., essentially just an action
                int aId = _htn.getReductionPrimitivizationName(opId);
                fillFactFramesAction(opId, aId, change);
                numEffects += _fact_frames[opId].effects.size();
            } else if (_htn.isReduction(opId)) {
                // Reduction
                const auto& reduction = _htn.getAnonymousReduction(opId);
                FlatHashSet<int> argSet(reduction.getArguments().begin(), reduction.getArguments().end());
                //Log::d("reduction %s\n", TOSTR(opId));
                //Log::e("with id %i\n", opId);

                // Set up (new?) fact frame with the reduction's preconditions
                FactFrame& result = _fact_frames[opId];
                result.sig = reduction.getSignature();
                result.preconditions.insert(reduction.getPreconditions().begin(), 
                                            reduction.getPreconditions().end());
                result.offsetEffects.resize(reduction.getSubtasks().size());
                size_t priorEffs = result.effects.size();
                size_t priorPostconditionSize = result.postconditions.size();
                size_t priorNegatedPostconditionSize = result.negatedPostconditions.size();
                SigSet newPostconditions = result.preconditions;
                result.numDirectChildren = 0;

                // For each subtask of the reduction
                for (size_t i = 0; i < reduction.getSubtasks().size(); i++) {
                    //Log::e("checking subtask with index %i\n", i);
                    // Find all possible child operations for this subtask
                    std::vector<USignature> children;
                    _util.getTraversal().getPossibleChildren(reduction.getSubtasks(), i, children);
                    SigSet childrenEffectIntersection;
                    bool firstChild = true;
                    result.numDirectChildren += children.size();

                    // For each such child operation
                    for (const auto& child : children) {
                        // Fact frame for this child already present?
                        if (_fact_frames.count(child._name_id)) {
                            //Log::e("checking child with id %i\n", child._name_id);
                            // Retrieve child's fact frame
                            FactFrame childFrame = _util.getFactFrame(child);
                            SigSet normalizedEffects;
                            for (auto& eff : childFrame.effects) normalizedEffects.insert(normalizeSignature(eff, argSet));

                            Sig::unite(normalizedEffects, result.effects);
                            Sig::unite(normalizedEffects, result.offsetEffects[i]);
                            SigSet childPostconditions;
                            for (auto& eff : childFrame.postconditions) {
                                //Log::e("postcondition: %s\n", TOSTR(eff));
                                if (!hasUnboundArgs(eff, argSet)) childPostconditions.insert(eff);
                            }
                            for (auto& eff : childFrame.negatedPostconditions) {
                                //Log::e("postcondition: %s\n", TOSTR(eff));
                                if (!hasUnboundArgs(eff, argSet)) childPostconditions.insert(eff);
                            }
                            if (firstChild) {
                                firstChild = false;
                                childrenEffectIntersection = childPostconditions;
                            } else {
                                Sig::intersect(childPostconditions, childrenEffectIntersection);
                            }

                            SigSet newPostconditionsFiltered;
                            for (const auto& eff: newPostconditions) {
                                bool valid = true;
                                for (const auto& normEff: normalizedEffects) {
                                    if (eff._usig._name_id == normEff._usig._name_id &&
                                        eff._negated != normEff._negated) {
                                            valid = false;
                                            break;
                                    }
                                }
                                if (valid) {
                                    newPostconditionsFiltered.insert(eff);
                                }
                            }
                            newPostconditions = newPostconditionsFiltered;
                        }
                    }
                    Sig::unite(childrenEffectIntersection, newPostconditions);
                    for (auto negatedCopy: newPostconditions) {
                        negatedCopy.negate();
                        if (result.effects.count(negatedCopy)) {
                            result.effects.erase(negatedCopy);
                        }
                    }
                }
                result.postconditions.clear();
                result.negatedPostconditions.clear();
                for (const auto& eff: newPostconditions) {
                    if (eff._negated) {
                        result.negatedPostconditions.insert(eff);
                    } else {
                        result.postconditions.insert(eff);
                    }
                }

                numEffects += result.effects.size();
                if (result.effects.size() != priorEffs or result.postconditions.size() != priorPostconditionSize or 
                    result.negatedPostconditions.size() != priorNegatedPostconditionSize) {
                    change = true;
                }
            }
        }
    }
    _util.setNumEffects(numEffects);
    
}

void FactAnalysisPreprocessing::extendPreconditions(std::vector<int>& orderedOpIds) {
    // In a next step, use the converged fact changes to infer preconditions
    for (int i = orderedOpIds.size()-1; i >= 0; i--) {
        int opId = orderedOpIds[i];
        Log::d("FF %i : %s\n", i, TOSTR(opId));
        if (_htn.isReduction(opId) && !_htn.isReductionPrimitivizable(opId)) {
            const auto& reduction = _htn.getAnonymousReduction(opId);
            FlatHashSet<int> argSet(reduction.getArguments().begin(), reduction.getArguments().end());
            FactFrame& result = _fact_frames[opId];

            // Effects which may be caused by the operation up to the current subtask
            SigSet effects;
            // For each subtask of the reduction
            for (size_t i = 0; i < reduction.getSubtasks().size(); i++) {    

                // Find all possible child operations for this subtask
                std::vector<USignature> children;
                _util.getTraversal().getPossibleChildren(reduction.getSubtasks(), i, children);
                
                // For each such child operation
                FactFrame offsetFrame;
                bool firstChild = true;
                for (const auto& child : children) {
                    // Retrieve child's fact frame
                    FactFrame childFrame = _fact_frames.at(child._name_id);
                    // Convert fact frame to local args of child
                    childFrame = childFrame.substitute(Substitution(childFrame.sig._args, child._args));
                    for (auto& pre : childFrame.preconditions) pre = normalizeSignature(pre, argSet);
                    for (auto& eff : childFrame.effects) eff = normalizeSignature(eff, argSet);

                    if (firstChild) {
                        // Add all preconditions of child that are not yet part of the parent's effects
                        // at the previous offset
                        for (const auto& pre : childFrame.preconditions) {
                            bool isNew = true;
                            // Normalize precondition
                            for (const auto& eff : effects) {
                                if (_htn.isUnifiable(eff, pre) || _htn.isUnifiable(pre, eff)) {
                                    isNew = false;
                                    break;
                                } 
                            }
                            if (isNew) offsetFrame.preconditions.insert(pre);
                        }
                        firstChild = false;
                    } else {
                        // Intersect preconditions with previous childrens' preconditions
                        Sig::intersect(childFrame.preconditions, offsetFrame.preconditions);
                    }
                }

                // Write into parent's fact frame
                Sig::unite(offsetFrame.preconditions, result.preconditions);

                // Update effects with offset effects found above
                Sig::unite(result.offsetEffects[i], effects);
            }
            result.rigidPreconditions = filterFluentPredicates(result.preconditions, _fluent_predicates);
            result.fluentPreconditions = filterRigidPredicates(result.preconditions, _fluent_predicates);

            // Clear unneeded cached offset effects
            result.offsetEffects.clear();
        } else {
            FactFrame& result = _fact_frames[opId];
            result.rigidPreconditions = filterFluentPredicates(result.preconditions, _fluent_predicates);
            result.fluentPreconditions = filterRigidPredicates(result.preconditions, _fluent_predicates);
        }
    }
}

void FactAnalysisPreprocessing::fillPFCNodesTopDownBFS(std::vector<int>& orderedOpIds) {
    // Iterate over each (lifted) operation in reversed order
    for (int i = orderedOpIds.size()-1; i >= 0; i--) {
        int opId = orderedOpIds[i];
        
        if (_htn.isReduction(opId)) {
            int num_custom_vars = 0;
            int numNodes = 1;
            // Set up (new?) fact frame with the reduction's preconditions
            FactFrame& result = _fact_frames[opId];
            PFCNode tempNode;
            tempNode.sig = result.sig;
            
            std::vector<NodeHashMap<int, PFCNode>*> tempSubtasks;
            tempSubtasks.push_back(new NodeHashMap<int, PFCNode>);
            (*tempSubtasks[0])[opId] = tempNode;

            std::vector<NodeHashMap<int, PFCNode>*> subtasks = tempSubtasks;
            bool done = false;
            while(subtasks.size() > 0 && numNodes < MAX_NODES) {
                std::vector<NodeHashMap<int, PFCNode>*> nextSubtasks;
                for (const auto& subtask: subtasks) {
                    for (auto& [id, child]: *subtask) {
                        if (_htn.isReduction(id)) {
                            // Reduction
                            const auto& subtaskReduction = _htn.getAnonymousReduction(id);
                            FlatHashSet<int> argSet(subtaskReduction.getArguments().begin(), subtaskReduction.getArguments().end());

                            int numChildrenSubtask = 0;
                            for (size_t i = 0; i < subtaskReduction.getSubtasks().size(); i++) {
                                std::vector<USignature> subtaskChildren;
                                _util.getTraversal().getPossibleChildren(subtaskReduction.getSubtasks(), i, subtaskChildren);
                                numChildrenSubtask += subtaskChildren.size();
                            }

                            if (numChildrenSubtask + numNodes > MAX_NODES) {
                                nextSubtasks.resize(0);
                                done = true;
                                break;
                            }
                            child.numDirectChildren = numChildrenSubtask;
                            for (size_t i = 0; i < subtaskReduction.getSubtasks().size(); i++) {
                                NodeHashMap<int, PFCNode>* newSubtask = new NodeHashMap<int, PFCNode>;
                                // Find all possible child operations for this subtask
                                std::vector<USignature> subtaskChildren;
                                _util.getTraversal().getPossibleChildren(subtaskReduction.getSubtasks(), i, subtaskChildren);
                                
                                // For each such child operation
                                for (const auto& newChild : subtaskChildren) {
                                    // Log::e("newChild: %s\n", TOSTR(child));
                                    FactFrame& childFrame = _fact_frames.at(newChild._name_id);
                                    Substitution s = Substitution(childFrame.sig._args, newChild._args);
                                    PFCNode childNode;
                                    childNode.sig = childFrame.sig;
                                    std::vector<int> argsToSubstitute;
                                    std::vector<int> argSubstitutions;
                                    for (const auto& arg: newChild._args) {
                                        if (!argSet.count(arg)) {
                                            int newArgument = _htn.nameId(std::string("?_customPFCVar_") + std::to_string(num_custom_vars));
                                            num_custom_vars++;
                                            argsToSubstitute.push_back(arg);
                                            argSubstitutions.push_back(newArgument);
                                            childNode.newArgs.insert(newArgument);
                                        }
                                    }
                                    s = s.concatenate(Substitution(argsToSubstitute, argSubstitutions));
                                    s = s.concatenate(Substitution(subtaskReduction.getSignature()._args, child.sig._args));
                                    childNode.substitute(s);
                                    childNode.substitution = s;
                                    (*newSubtask)[newChild._name_id] = childNode;
                                    numNodes++;
                                }
                                child.subtasks.push_back(newSubtask);
                                nextSubtasks.push_back(newSubtask);
                            }
                        }
                    }
                    if (done) break;
                }
                subtasks = nextSubtasks;
            }
            result.subtasks = (*tempSubtasks[0])[opId].subtasks;
            free(tempSubtasks[0]);
            tempSubtasks[0] = NULL;
            result.numNodes = numNodes;
        } else {
            Log::d("FF %s : unmatched\n", TOSTR(opId));
        }
    }
}


// Iterate though all operations and find all predicates occuring in any actions effects (fluent predicates)
// to fill _fluent_predicates, and thus also implicitly identify rigid predicates.
FlatHashSet<int> FactAnalysisPreprocessing::findFluentPredicates(const std::vector<int>& orderedOpIds) {
    FlatHashSet<int> fluentPredicates;
    // find predicate signatures that are affected by operations (and thus find rigid predicates)
    for (int i = orderedOpIds.size()-1; i >= 0; i--) {
        int opId = orderedOpIds[i];
        
        if (_htn.isAction(opId) || _htn.isActionRepetition(opId)) {
            int aId = opId;
            if (_htn.isActionRepetition(opId)) aId = _htn.getActionNameFromRepetition(opId);
            Action action = _htn.getAnonymousAction(aId);
            for (auto effect : action.getEffects()) {
                fluentPredicates.insert(effect._usig._name_id);
            }

        } else if (_htn.isReductionPrimitivizable(opId)) {
            // Primitivization of a reduction, i.e., essentially just an action
            int aId = _htn.getReductionPrimitivizationName(opId);
            Action action = _htn.getAnonymousAction(aId);
            for (auto effect : action.getEffects()) {
                fluentPredicates.insert(effect._usig._name_id);
            }
        }
    }
    
    return fluentPredicates;
}