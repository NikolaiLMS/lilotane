
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

    for (const auto& [id, ff] : _fact_frames) {
        Log::d("FF %s effects: %s\n", TOSTR(ff.sig), TOSTR(ff.effects));
        Log::d("FF: %s\n", TOSTR(ff));
    }
}

void FactAnalysisPreprocessing::computeFactFramesCondEffs() {

    std::vector<int> orderedOpIds = calcOrderedOpList();

    _fluent_predicates = findFluentPredicates(orderedOpIds);

    computeCondEffs(orderedOpIds);

    extendPreconditions(orderedOpIds);

    // for (const auto& [id, ff] : _fact_frames) {
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
    Log::d("FF all: { %s }\n", TOSTR(orderedOpIds));
    return orderedOpIds;
}

void FactAnalysisPreprocessing::fillFactFramesAction(int& opId, int& aId, bool& change) {
    Action action = _htn.getAnonymousAction(aId);
    if (_fact_frames[opId].sig != action.getSignature()) {
        _fact_frames[opId].sig = action.getSignature();
        _fact_frames[opId].preconditions = action.getPreconditions();
        _fact_frames[opId].effects = action.getEffects();
        for (const auto& eff: action.getEffects()) {
            if (!eff._negated) {
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
                    _fact_frames[opId].negatedPostconditions.insert(eff);
                }
            }
        }
        change = true;
    } // else: fact frame already set
}

void FactAnalysisPreprocessing::fillFactFramesBase(std::vector<int>& orderedOpIds) {
    bool change = true;
    int numEffectsReductions;
    int run = 1;
    while (change) {
        //Log::e("Run number %i\n", run);
        run++;
        numEffectsReductions = 0;
        _util.setNumEffectsErasedByPostconditions(0);
        change = false;
        // Iterate over each (lifted) operation in reversed order
        for (int i = orderedOpIds.size()-1; i >= 0; i--) {
            int opId = orderedOpIds[i];
            Log::d("FF %i : %s\n", i, TOSTR(opId));
            if (_htn.isAction(opId) || _htn.isActionRepetition(opId)) {
                // Action: Setting fact frame is trivial
                int aId = opId;
                if (_htn.isActionRepetition(opId)) aId = _htn.getActionNameFromRepetition(opId);
                fillFactFramesAction(opId, aId, change);
            } else if (_htn.isReductionPrimitivizable(opId)) {
                // Primitivization of a reduction, i.e., essentially just an action
                int aId = _htn.getReductionPrimitivizationName(opId);
                fillFactFramesAction(opId, aId, change);
            } else if (_htn.isReduction(opId)) {
                // Reduction
                const auto& reduction = _htn.getAnonymousReduction(opId);
                FlatHashSet<int> argSet(reduction.getArguments().begin(), reduction.getArguments().end());
                Log::d("reduction %s\n", TOSTR(opId));

                // Set up (new?) fact frame with the reduction's preconditions
                FactFrame& result = _fact_frames[opId];
                result.sig = reduction.getSignature();
                result.preconditions.insert(reduction.getPreconditions().begin(), 
                                            reduction.getPreconditions().end());
                result.offsetEffects.resize(reduction.getSubtasks().size());
                size_t priorEffs = result.effects.size();
                size_t priorPostconditionSize = result.postconditions.size();
                size_t priorNegatedPostconditionSize = result.negatedPostconditions.size();
                SigSet newPostconditions;

                // For each subtask of the reduction
                for (size_t i = 0; i < reduction.getSubtasks().size(); i++) {

                    // Find all possible child operations for this subtask
                    std::vector<USignature> children;
                    _util.getTraversal().getPossibleChildren(reduction.getSubtasks(), i, children);
                    SigSet childrenEffectIntersection;
                    bool firstChild = true;

                    // For each such child operation
                    for (const auto& child : children) {
                        // Fact frame for this child already present?
                        if (_fact_frames.count(child._name_id)) {
                            // Retrieve child's fact frame
                            FactFrame childFrame = _util.getFactFrame(child);
                            SigSet normalizedEffects;
                            for (auto& eff : childFrame.effects) normalizedEffects.insert(normalizeSignature(eff, argSet));

                            Sig::unite(normalizedEffects, result.effects);
                            Sig::unite(normalizedEffects, result.offsetEffects[i]);
                            SigSet childPostconditions;
                            for (auto& eff : childFrame.postconditions) {
                                if (!hasUnboundArgs(eff, argSet)) childPostconditions.insert(eff);
                            }
                            for (auto& eff : childFrame.negatedPostconditions) {
                                if (!hasUnboundArgs(eff, argSet)) childPostconditions.insert(eff);
                            }
                            if (firstChild) {
                                firstChild = false;
                                childrenEffectIntersection = childPostconditions;
                            } else {
                                for (const auto& eff: childPostconditions) {
                                    if (!childrenEffectIntersection.count(eff)) {
                                        childrenEffectIntersection.erase(eff);
                                    }
                                }
                            }
                            SigSet childrenEffectIntersectionFiltered;
                            for (const auto& eff: childrenEffectIntersection) {
                                bool valid = true;
                                if (eff._negated) {
                                    for (const auto& normEff: normalizedEffects) {
                                        if (eff._usig._name_id == normEff._usig._name_id &&
                                            eff._negated != normEff._negated) {
                                            valid = false; 
                                            break;
                                        }
                                    }
                                }
                                if (valid) {
                                    childrenEffectIntersectionFiltered.insert(eff);
                                }
                            }
                            childrenEffectIntersection = childrenEffectIntersectionFiltered;

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
                    for (const auto& eff: newPostconditions) {
                        Signature negatedCopy = eff;
                        negatedCopy._negated = !eff._negated;
                        if (result.effects.count(negatedCopy)) {
                            result.effects.erase(negatedCopy);
                            _util.incrementNumEffectsErasedByPostconditions();
                            Log::e("Removed effect %s from effects of reduction %s\n", TOSTR(negatedCopy), TOSTR(opId));
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

                numEffectsReductions += result.effects.size();
                if (result.effects.size() != priorEffs or result.postconditions.size() != priorPostconditionSize or 
                    result.negatedPostconditions.size() != priorNegatedPostconditionSize) {
                    change = true;
                }
            }
        }
    }
    _util.setNumEffectsReductions(numEffectsReductions);
    
}

// Repeatedly extend the operations' fact frames until convergence of fact changes
void FactAnalysisPreprocessing::computeCondEffs(std::vector<int>& orderedOpIds) {
    bool change = true;
    while (change) {
        change = false;

        // Iterate over each (lifted) operation in reversed order
        for (int i = orderedOpIds.size()-1; i >= 0; i--) {
            int opId = orderedOpIds[i];
            Log::d("FF %i : %s\n", i, TOSTR(opId));
            
            if (_htn.isAction(opId) || _htn.isActionRepetition(opId)) {
                // Action: Setting fact frame is trivial
                int aId = opId;
                if (_htn.isActionRepetition(opId)) aId = _htn.getActionNameFromRepetition(opId);
                Action action = _htn.getAnonymousAction(aId);
                if (_fact_frames[opId].sig != action.getSignature()) {
                    _fact_frames[opId].sig = action.getSignature();
                    _fact_frames[opId].preconditions = action.getPreconditions();
                    _fact_frames[opId].effects = action.getEffects();
                    NodeHashMap<std::pair<SigSet, SigSet>, SigSet, SigSetPairHasher, SigSetPairEquals> condEffs;
                    condEffs[{SigSet(), SigSet()}] = action.getEffects();
                    _fact_frames[opId].conditionalEffects.push_back(condEffs);
                    change = true;
                } // else: fact frame already set

            } else if (_htn.isReductionPrimitivizable(opId)) {
                // Primitivization of a reduction, i.e., essentially just an action
                int aId = _htn.getReductionPrimitivizationName(opId);
                Action action = _htn.getAnonymousAction(aId);
                if (_fact_frames[opId].sig != action.getSignature()) {
                    _fact_frames[opId].sig = action.getSignature();
                    _fact_frames[opId].preconditions = action.getPreconditions();
                    _fact_frames[opId].effects = action.getEffects();
                    NodeHashMap<std::pair<SigSet, SigSet>, SigSet, SigSetPairHasher, SigSetPairEquals> condEffs;
                    condEffs[{SigSet(), SigSet()}] = action.getEffects();
                    _fact_frames[opId].conditionalEffects.push_back(condEffs);
                    change = true;
                } // else: fact frame already set

            } else if (_htn.isReduction(opId)) {
                // Reduction
                const auto& reduction = _htn.getAnonymousReduction(opId);
                FlatHashSet<int> argSet(reduction.getArguments().begin(), reduction.getArguments().end());

                // Set up (new?) fact frame with the reduction's preconditions
                FactFrame& result = _fact_frames[opId];
                result.sig = reduction.getSignature();
                result.preconditions.insert(reduction.getPreconditions().begin(), 
                                            reduction.getPreconditions().end());
                result.offsetEffects.resize(reduction.getSubtasks().size());
                size_t priorEffs = result.effects.size();
                size_t priorCondEffs = result.conditionalEffects.size();
                size_t priorCondTotalEffs = 0;
                for (auto& conditionalEffect : result.conditionalEffects) {
                    for (auto& [prereqs, effs]: conditionalEffect) {
                        priorCondTotalEffs += effs.size();
                    }
                }
                std::vector<NodeHashMap<std::pair<SigSet, SigSet>, SigSet, SigSetPairHasher, SigSetPairEquals>> newConditionalEffects;
                // For each subtask of the reduction
                for (size_t i = 0; i < reduction.getSubtasks().size(); i++) {
                    NodeHashMap<std::pair<SigSet, SigSet>, SigSet, SigSetPairHasher, SigSetPairEquals> newSubtaskCondEff;
                    // Find all possible child operations for this subtask
                    std::vector<USignature> children;
                    _util.getTraversal().getPossibleChildren(reduction.getSubtasks(), i, children);
                    
                    // For each such child operation
                    for (const auto& child : children) {

                        // Fact frame for this child already present?
                        if (_fact_frames.count(child._name_id)) {
                            // Retrieve child's fact frame
                            FactFrame childFrame = _util.getFactFrame(child);
                            SigSet normalizedEffects;
                            for (auto& eff : childFrame.effects) normalizedEffects.insert(normalizeSignature(eff, argSet));

                            Sig::unite(normalizedEffects, result.effects);
                            Sig::unite(normalizedEffects, result.offsetEffects[i]);

                            // Pull conditionalEffects from child into reduction
                            for (auto& conditionalEffect : childFrame.conditionalEffects) {
                                for (auto& [preconditions, effects]: conditionalEffect) {
                                    SigSet rigidPreconditionsNormalized;
                                    SigSet fluentPreconditionsNormalized;
                                    SigSet childRigidPreconditions = _util.filterFluentPredicates(childFrame.preconditions, _fluent_predicates);
                                    SigSet childFluentPreconditions = _util.filterRigidPredicates(childFrame.preconditions, _fluent_predicates);

                                    // Add (already filtered) prerequisites from child
                                    for (auto& prereq : preconditions.first) {
                                        rigidPreconditionsNormalized.insert(normalizeSignature(prereq, argSet));
                                    }
                                    
                                    // Add (already filtered) prerequisites from child
                                    for (auto& prereq : childRigidPreconditions) {
                                        rigidPreconditionsNormalized.insert(normalizeSignature(prereq, argSet));
                                    }

                                    for (auto& prereq : preconditions.second) {
                                        fluentPreconditionsNormalized.insert(normalizeSignature(prereq, argSet));
                                    }

                                    for (auto& prereq : childFluentPreconditions) {
                                        fluentPreconditionsNormalized.insert(normalizeSignature(prereq, argSet));
                                    }

                                    // Normalize effects
                                    SigSet newEffects;
                                    for (auto& eff : effects) {
                                        newEffects.insert(normalizeSignature(eff, argSet));
                                    }

                                    // Extend (new?) conditionalEffect entry with newEffects
                                    Sig::unite(newEffects, newSubtaskCondEff[{rigidPreconditionsNormalized, fluentPreconditionsNormalized}]);
                                }
                            }
                        }
                    }
                    newConditionalEffects.push_back(newSubtaskCondEff);
                }
                result.conditionalEffects = newConditionalEffects;

                size_t newCondTotalEffs = 0;
                for (const auto& conditionalEffect : result.conditionalEffects) {
                    for (const auto& [prereqs, effs]: conditionalEffect) {
                        newCondTotalEffs += effs.size();
                    }
                }
                // Check if the fact frame has been extended non-trivially
                Log::d("Original: Prior size: %i, new size: %i\n", priorEffs, result.effects.size());
                Log::d("Conditional: Prior size: %i, new size: %i\n", priorCondEffs, result.conditionalEffects.size());
                if (result.effects.size() > priorEffs) {
                    change = true;
                } else if (result.conditionalEffects.size() != priorCondEffs or newCondTotalEffs > priorCondTotalEffs) {
                    change = true;
                    Log::d("Effect size didn't change but conditionalEffects did:\n");
                    std::vector<int> vect{opId};
                    //testConditionalEffects(vect); TODO
                }
            } else {
                Log::d("FF %s : unmatched\n", TOSTR(opId));
            }
        }
    }
}

void FactAnalysisPreprocessing::printFactFrameBFS(int opId) {
    FactFrame& factFrame = _fact_frames[opId];
    Log::e("Root: %s\n", TOSTR(factFrame.sig));
    Log::e("Root.numNodes: %i\n", factFrame.numNodes);

    std::string subtaskArgsString = "Root subtaskArgs: ";
    for (const auto& arg: factFrame.subtaskArgs) {
        subtaskArgsString += TOSTR(arg) + std::string(", ");
    }
    subtaskArgsString += std::string("\n");
    Log::e(subtaskArgsString.c_str());

    std::vector<NodeHashMap<int, PFCNode>*> subtasks = factFrame.subtasks;
    int depth = 1;
    while (subtasks.size() > 0) {
        Log::e("Depth %i:\n", depth);
        std::vector<NodeHashMap<int, PFCNode>*> newSubtasks;
        int subtaskIdx = 0;
        for (const auto& subtask: subtasks) {
            Log::e("Subtask %i:\n", subtaskIdx);
            for (const auto& [id, child]: *subtask) {
                Log::e("Child: %s\n", TOSTR(child.sig));
                subtaskArgsString = "Child subtaskArgs: ";
                for (const auto& arg: child.subtaskArgs) {
                    subtaskArgsString += TOSTR(arg) + std::string(", ");
                }
                subtaskArgsString += std::string("\n");
                Log::e(subtaskArgsString.c_str());
                for (const auto& childSubtask: child.subtasks) {
                    newSubtasks.push_back(childSubtask);
                }
            }
            subtaskIdx++;
        }
        subtasks = newSubtasks;
        depth++;
    }
}

void FactAnalysisPreprocessing::extendPreconditions(std::vector<int>& orderedOpIds) {
    int avgBranchDegreeArithmetic = 0;
    int numReductions = 0;
    // In a next step, use the converged fact changes to infer preconditions
    for (int i = orderedOpIds.size()-1; i >= 0; i--) {
        int opId = orderedOpIds[i];
        Log::d("FF %i : %s\n", i, TOSTR(opId));
        if (_htn.isReduction(opId) && !_htn.isReductionPrimitivizable(opId)) {
            numReductions++;
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
                    avgBranchDegreeArithmetic++;
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
            // Clear unneeded cached offset effects
            result.offsetEffects.clear();
        }
    }
    avgBranchDegreeArithmetic = int(avgBranchDegreeArithmetic/numReductions);
    DEPTH_LIMIT = std::max(int(std::log(MAX_NODES) / std::log(avgBranchDegreeArithmetic)), 1);
    Log::e("avgBranchDegreeArithmetic: %i\n", avgBranchDegreeArithmetic);
    Log::e("DEPTH_LIMIT: %i\n", DEPTH_LIMIT);
}

void FactAnalysisPreprocessing::fillPFCNodes(std::vector<int>& orderedOpIds) {
    // Repeatedly extend the operations' fact frames until convergence of fact changes
    bool change = true;
    int iteration = 0;
    while (change) {
        int avgNumNodes = 0;
        change = false;
        Log::e("Iteration #%i\n", iteration);
        iteration++;
        // Iterate over each (lifted) operation in reversed order
        for (int i = orderedOpIds.size()-1; i >= 0; i--) {
            int opId = orderedOpIds[i];
            
            if (_htn.isReduction(opId)) {
                // Reduction
                const auto& reduction = _htn.getAnonymousReduction(opId);
                FlatHashSet<int> argSet(reduction.getArguments().begin(), reduction.getArguments().end());
                //Log::e("Reduction: %s\n", TOSTR(opId));

                // Set up (new?) fact frame with the reduction's preconditions
                FactFrame& result = _fact_frames[opId];
                int newMaxDepth = 0;
                int oldNumNodes = result.numNodes;
                int newNumNodes = oldNumNodes;
                if (result.subtasks.size() == 0) {
                    result.subtasks.reserve(reduction.getSubtasks().size());
                    for (size_t j = 0; j < reduction.getSubtasks().size(); j++) {
                        result.subtasks.push_back(new NodeHashMap<int, PFCNode>);
                    }
                }

                // For each subtask of the reduction`
                for (size_t i = 0; i < reduction.getSubtasks().size(); i++) {

                    // Find all possible child operations for this subtask
                    std::vector<USignature> children;
                    _util.getTraversal().getPossibleChildren(reduction.getSubtasks(), i, children);


                    // For each such child operation
                    for (const auto& child : children) {
                       // Log::e("child: %s\n", TOSTR(child));
                        FactFrame& childFrame = _fact_frames.at(child._name_id);
                        Substitution s = Substitution(childFrame.sig._args, child._args);
                        if (!(*result.subtasks[i]).count(child._name_id)) {
                            PFCNode initialNode;
                            initialNode.sig = childFrame.sig;
                            initialNode.effects = childFrame.effects;
                            initialNode.rigidPreconditions = _util.filterFluentPredicates(childFrame.preconditions, _fluent_predicates);
                            initialNode.fluentPreconditions = _util.filterRigidPredicates(childFrame.preconditions, _fluent_predicates);
                            initialNode.substitute(s);
                            std::vector<int> argsToSubstitute;
                            std::vector<int> argSubstitutions;
                            for (const auto& arg: initialNode.sig._args) {
                                if (!argSet.count(arg)) {
                                    if (result.subtaskArgs.count(arg)) {
                                        int newArgument = _htn.nameId(std::string("?_customPFCVar_") + std::to_string(_num_custom_vars));
                                        _num_custom_vars++;
                                        argsToSubstitute.push_back(arg);
                                        argSubstitutions.push_back(newArgument);
                                        result.subtaskArgs.insert(newArgument);
                                    } else {
                                        result.subtaskArgs.insert(arg);
                                    }
                                }
                            }
                            initialNode.substitute(Substitution(argsToSubstitute, argSubstitutions));
                            s = s.concatenate(Substitution(argsToSubstitute, argSubstitutions));
                            (*result.subtasks[i])[child._name_id] = initialNode;
                        } else {
                            newNumNodes -= (*result.subtasks[i])[child._name_id].numNodes;
                        }
                        PFCNode& currentChildNode = (*result.subtasks[i])[child._name_id];

                        PFCNode childNode;
                        childNode.sig = childFrame.sig;
                        childNode.effects = childFrame.effects;
                        childNode.rigidPreconditions = _util.filterFluentPredicates(childFrame.preconditions, _fluent_predicates);
                        childNode.fluentPreconditions = _util.filterRigidPredicates(childFrame.preconditions, _fluent_predicates);
                        childNode.subtasks = childFrame.subtasks;
                        childNode.maxDepth = childFrame.maxDepth;
                        childNode.numNodes = childFrame.numNodes;
                        childNode.subtaskArgs = childFrame.subtaskArgs;
                        // Retrieve child's fact frame
                        if (childNode.numNodes > currentChildNode.numNodes) {
                            //Log::e("Normalize if\n");
                            normalizeSubstituteNodeDiff(childNode, currentChildNode, result.subtaskArgs, s, DEPTH_LIMIT-1);
                        }
                        newMaxDepth = std::max(newMaxDepth, currentChildNode.maxDepth+1);
                        newNumNodes += currentChildNode.numNodes;
                    }
                }
                result.maxDepth = newMaxDepth;
                result.numNodes = newNumNodes;
                avgNumNodes += newNumNodes;
                //Log::e("newNumNodes: %i\n", newNumNodes);
                //Log::e("newMaxDepth: %i\n", newMaxDepth);
                if (result.numNodes > oldNumNodes) {
                    change = true;
                }
            } else {
                Log::d("FF %s : unmatched\n", TOSTR(opId));
            }
        }
        // for (const auto& [id, ff] : _fact_frames) {
        //     printFactFrameBFS(id);
        // }
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
            tempNode.effects = result.effects;
            tempNode.rigidPreconditions = _util.filterFluentPredicates(result.preconditions, _fluent_predicates);
            tempNode.fluentPreconditions = _util.filterRigidPredicates(result.preconditions, _fluent_predicates);
            
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
                                    childNode.effects = childFrame.effects;
                                    childNode.rigidPreconditions = _util.filterFluentPredicates(childFrame.preconditions, _fluent_predicates);
                                    childNode.fluentPreconditions = _util.filterRigidPredicates(childFrame.preconditions, _fluent_predicates);
                                    childNode.postconditions = childFrame.postconditions;
                                    childNode.negatedPostconditions = childFrame.negatedPostconditions;
                                    childNode.substitute(s);
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
                                    childNode.substitute(Substitution(argsToSubstitute, argSubstitutions));
                                    childNode.substitute(Substitution(subtaskReduction.getSignature()._args, child.sig._args));
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
        Log::d("FF %i : %s\n", i, TOSTR(opId));
        
        if (_htn.isAction(opId) || _htn.isActionRepetition(opId)) {
            int aId = opId;
            if (_htn.isActionRepetition(opId)) aId = _htn.getActionNameFromRepetition(opId);
            Action action = _htn.getAnonymousAction(aId);
            for (auto effect : action.getEffects()) {
                Log::d("Found fluent predicate: %s\n", TOSTR(effect));
                fluentPredicates.insert(effect._usig._name_id);
            }

        } else if (_htn.isReductionPrimitivizable(opId)) {
            // Primitivization of a reduction, i.e., essentially just an action
            int aId = _htn.getReductionPrimitivizationName(opId);
            Action action = _htn.getAnonymousAction(aId);
            for (auto effect : action.getEffects()) {
                Log::d("Found fluent predicate: %s\n", TOSTR(effect));
                fluentPredicates.insert(effect._usig._name_id);
            }
        }
    }
    
    return fluentPredicates;
}

// recursively extends nodeToExtend with the new nodes in newNode until the depthLimit, the new nodes are substituted and normalized
void FactAnalysisPreprocessing::normalizeSubstituteNodeDiff(const PFCNode& newNode, PFCNode& nodeToExtend, 
    FlatHashSet<int>& subtaskArgsRoot, const Substitution& s, int depthLimit) {
    if (depthLimit == 0) {
        return;
    }
    if (nodeToExtend.subtasks.size() == 0) {
        nodeToExtend.subtasks.reserve(newNode.subtasks.size());
        for (size_t i = 0; i < newNode.subtasks.size(); i++) {
            nodeToExtend.subtasks.push_back(new NodeHashMap<int, PFCNode>);
        }
    }
    int numNodes = 1;
    int maxDepth = 0;
    for (size_t i = 0; i < newNode.subtasks.size(); i++) {
        for (const auto& [id, child]: *newNode.subtasks[i]) {
            if (!(*nodeToExtend.subtasks[i]).count(id)) {
                (*nodeToExtend.subtasks[i])[id] = child.cutDepth(depthLimit-1);
                (*nodeToExtend.subtasks[i])[id].substitute(s);
                std::vector<int> argsToSubstitute;
                std::vector<int> argSubstitutions;
                for (const auto& arg: child.sig._args) {
                    if (newNode.subtaskArgs.count(arg)) {
                        if (subtaskArgsRoot.count(arg)) {
                            int newArgument = _htn.nameId(std::string("?_customPFCVar_") + std::to_string(_num_custom_vars));
                            _num_custom_vars++;
                            argsToSubstitute.push_back(arg);
                            argSubstitutions.push_back(newArgument);
                            nodeToExtend.subtaskArgs.insert(newArgument);
                            subtaskArgsRoot.insert(newArgument);
                        } else {
                            nodeToExtend.subtaskArgs.insert(arg);
                            subtaskArgsRoot.insert(arg);
                        }
                    }
                }

                for (const auto& arg: (*nodeToExtend.subtasks[i])[id].subtaskArgs) {
                    if (subtaskArgsRoot.count(arg)) {
                        int newArgument = _htn.nameId(std::string("?_customPFCVar_") + std::to_string(_num_custom_vars));
                        _num_custom_vars++;
                        argsToSubstitute.push_back(arg);
                        argSubstitutions.push_back(newArgument);
                        nodeToExtend.subtaskArgs.insert(newArgument);
                        subtaskArgsRoot.insert(newArgument);
                    } else {
                        nodeToExtend.subtaskArgs.insert(arg);
                        subtaskArgsRoot.insert(arg);
                    }
                }
                (*nodeToExtend.subtasks[i])[id].substitute(Substitution(argsToSubstitute, argSubstitutions));
            } else if (child.numNodes > (*nodeToExtend.subtasks[i])[id].numNodes) {
                normalizeSubstituteNodeDiff(child, (*nodeToExtend.subtasks[i])[id], subtaskArgsRoot, s, depthLimit-1);
            }
            PFCNode& extendedNode = (*nodeToExtend.subtasks[i])[id];
            maxDepth = extendedNode.maxDepth+1 > maxDepth ? extendedNode.maxDepth+1 : maxDepth;
            numNodes += extendedNode.numNodes;
            for (const auto& arg: extendedNode.subtaskArgs) {
                nodeToExtend.subtaskArgs.insert(arg);
            }
        }
    }
    nodeToExtend.maxDepth = maxDepth;
    nodeToExtend.numNodes = numNodes;
}
