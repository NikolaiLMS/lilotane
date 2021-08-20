
#include "util/log.h"
#include "algo/compute_fact_frame.h"
#include "data/fact_frame.h"
#include "algo/topological_ordering.h"

int DEPTH_LIMIT = 1;

void FactAnalysisPreprocessing::computeFactFramesBase() {

    std::vector<int> orderedOpIds = calcOrderedOpList();

    _fluent_predicates = findFluentPredicates(orderedOpIds);

    if (_reliable_effect_pruning) {
        fillFactFramesReliableEffects(orderedOpIds);
    }

    fillFactFramesBase(orderedOpIds);

    extendPreconditions(orderedOpIds);

    // for (const auto& [id, ff] : _fact_frames) {
    //     Log::d("FF %s effects: %s\n", TOSTR(id), TOSTR(ff.effects));
    //     Log::d("FF: %s\n", TOSTR(ff));
    // }
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

    if (_reliable_effect_pruning) {
        fillFactFramesReliableEffects(orderedOpIds);
    }

    fillFactFramesBase(orderedOpIds);

    extendPreconditions(orderedOpIds);

    fillPFCNodes(orderedOpIds);

    // for (const auto& [id, ff] : _fact_frames) {
    //     Log::d("FF %s effects: %s\n", TOSTR(id), TOSTR(ff.effects));
    //     Log::d("FF: %s\n", TOSTR(ff));
    // }
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
        _fact_frames[opId].reliableEffects = action.getEffects();
        change = true;
    } // else: fact frame already set
}

void FactAnalysisPreprocessing::fillFactFramesBase(std::vector<int>& orderedOpIds) {
    bool change = true;
    int numEffectsReductions;
    while (change) {
        numEffectsReductions = 0;
        _util.setNumEffectsErasedByReliableEffects(0);
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

                // Set up (new?) fact frame with the reduction's preconditions
                FactFrame& result = _fact_frames[opId];
                result.sig = reduction.getSignature();
                result.preconditions.insert(reduction.getPreconditions().begin(), 
                                            reduction.getPreconditions().end());
                result.offsetEffects.resize(reduction.getSubtasks().size());
                size_t priorEffs = result.effects.size();
                SigSet newReliableEffects;

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

                            bool valid = true;
                            for (auto& prec: childFrame.preconditions) {
                                Signature negatedCopy = prec;
                                negatedCopy._negated = !prec._negated;
                                if (!newReliableEffects.count(prec) && newReliableEffects.count(negatedCopy)) {
                                    valid = false;
                                    Log::e("Found illegal child: %s in reduction %s\n", TOSTR(child), TOSTR(opId));
                                    Log::e(", because of precondition %s and reliable effects %s\n", TOSTR(prec), TOSTR(newReliableEffects));
                                    break;
                                }
                            }
                            if (!valid) {
                                continue;
                            }

                            SigSet normalizedEffects;
                            for (auto& eff : childFrame.effects) normalizedEffects.insert(normalizeSignature(eff, argSet));

                            Sig::unite(normalizedEffects, result.effects);
                            Sig::unite(normalizedEffects, result.offsetEffects[i]);
                            SigSet childReliableEffects;
                            for (auto& eff : childFrame.reliableEffects) {
                                if (!hasUnboundArgs(eff, argSet)) childReliableEffects.insert(eff);
                            }
                            //Log::e("childReliableEffects: %s\n", TOSTR(childReliableEffects));
                            if (firstChild) {
                                firstChild = false;
                                childrenEffectIntersection = childReliableEffects;
                            } else {
                                for (const auto& eff: childReliableEffects) {
                                    if (!childrenEffectIntersection.count(eff)) {
                                        childrenEffectIntersection.erase(eff);
                                    }
                                }
                            }
                        }
                    }
                    if (i == 0) {
                        newReliableEffects = childrenEffectIntersection;
                    } else {
                        for (const auto& eff: newReliableEffects) {
                            Signature negatedCopy = eff;
                            negatedCopy._negated = !eff._negated;
                            if (!childrenEffectIntersection.count(negatedCopy)) {
                                childrenEffectIntersection.insert(eff);
                            }
                        }
                        newReliableEffects = childrenEffectIntersection;
                    }
                }
                for (const auto& eff: result.reliableEffects) {
                    Signature negatedCopy = eff;
                    negatedCopy._negated = !eff._negated;
                    if (!result.reliableEffects.count(negatedCopy) && result.effects.count(negatedCopy)) {
                        result.effects.erase(negatedCopy);
                        _util.incrementNumEffectsErasedByReliableEffects();
                        Log::d("Removed effect %s from effects of reduction %s\n", TOSTR(negatedCopy), TOSTR(opId));
                    }
                }

                numEffectsReductions += result.effects.size();
                if (result.effects.size() > priorEffs) {
                    change = true;
                }
            }
        }
    }
    _util.setNumEffectsReductions(numEffectsReductions);
    
}

void FactAnalysisPreprocessing::fillFactFramesReliableEffects(std::vector<int>& orderedOpIds) {
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
                fillFactFramesAction(opId, aId, change);
            } else if (_htn.isReductionPrimitivizable(opId)) {
                // Primitivization of a reduction, i.e., essentially just an action
                int aId = _htn.getReductionPrimitivizationName(opId);
                fillFactFramesAction(opId, aId, change);
            } else if (_htn.isReduction(opId)) {
                // Reduction
                const auto& reduction = _htn.getAnonymousReduction(opId);
                FlatHashSet<int> argSet(reduction.getArguments().begin(), reduction.getArguments().end());

                // Set up (new?) fact frame with the reduction's preconditions
                FactFrame& result = _fact_frames[opId];
                result.preconditions.insert(reduction.getPreconditions().begin(), 
                    reduction.getPreconditions().end());
                size_t priorReliableEffs = result.reliableEffects.size();
                SigSet newReliableEffects;
                // For each subtask of the reduction
                for (size_t i = 0; i < reduction.getSubtasks().size(); i++) {

                    // Find all possible child operations for this subtask
                    std::vector<USignature> children;
                    _util.getTraversal().getPossibleChildren(reduction.getSubtasks(), i, children);
                    SigSet childrenEffectIntersection;
                    
                    bool firstChild = true;
                    // For each such child operation
                    for (const auto& child : children) {
                        if (_fact_frames.count(child._name_id)) {
                            // Retrieve child's fact frame
                            FactFrame childFrame = _util.getFactFrame(child);
                            bool valid = true;
                            for (auto& prec: childFrame.preconditions) {
                                Signature negatedCopy = prec;
                                negatedCopy._negated = !prec._negated;
                                if (!newReliableEffects.count(prec) && newReliableEffects.count(negatedCopy)) {
                                    valid = false;
                                    Log::e("Found illegal child: %s in reduction %s\n", TOSTR(child), TOSTR(opId));
                                    Log::e(", because of precondition %s and reliable effects %s\n", TOSTR(prec), TOSTR(newReliableEffects));
                                    break;
                                }
                            }
                            if (!valid) {
                                continue;
                            }
                            SigSet childReliableEffects;
                            for (auto& eff : childFrame.reliableEffects) {
                                if (!hasUnboundArgs(eff, argSet)) childReliableEffects.insert(eff);
                            }
                            //Log::e("childReliableEffects: %s\n", TOSTR(childReliableEffects));
                            if (firstChild) {
                                firstChild = false;
                                childrenEffectIntersection = childReliableEffects;
                            } else {
                                for (const auto& eff: childReliableEffects) {
                                    if (!childrenEffectIntersection.count(eff)) {
                                        childrenEffectIntersection.erase(eff);
                                    }
                                }
                            }
                        }
                    }
                    //Log::e("childrenEffectIntersection: %s\n", TOSTR(childrenEffectIntersection));
                    if (i == 0) {
                        newReliableEffects = childrenEffectIntersection;
                    } else {
                        for (const auto& eff: newReliableEffects) {
                            Signature negatedCopy = eff;
                            negatedCopy._negated = !eff._negated;
                            if (!childrenEffectIntersection.count(negatedCopy)) {
                                childrenEffectIntersection.insert(eff);
                            }
                        }
                        newReliableEffects = childrenEffectIntersection;
                    }
                    //Log::e("newReliableEffects: %s\n", TOSTR(newReliableEffects));
                }

                result.reliableEffects = newReliableEffects;
                if (result.reliableEffects.size() > priorReliableEffs) {
                    change = true;
                }
            }
        }
    }
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
    DEPTH_LIMIT = std::max(int(std::log(_num_nodes) / std::log(avgBranchDegreeArithmetic)), 1);
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
        //Log::e("Iteration #%i\n", iteration);
        iteration++;
        // Iterate over each (lifted) operation in reversed order
        for (int i = orderedOpIds.size()-1; i >= 0; i--) {
            int opId = orderedOpIds[i];
            //Log::d("FF %i : %s\n", i, TOSTR(opId));
            
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

                        FactFrame& childFrame = _fact_frames.at(child._name_id);
                        Substitution s = Substitution(childFrame.sig._args, child._args);
                        if (!(*result.subtasks[i]).count(child._name_id)) {
                            PFCNode initialNode;
                            initialNode.sig = childFrame.sig;
                            initialNode.effects = childFrame.effects;
                            initialNode.rigidPreconditions = _util.filterFluentPredicates(childFrame.preconditions, _fluent_predicates);
                            initialNode.fluentPreconditions = _util.filterRigidPredicates(childFrame.preconditions, _fluent_predicates);
                            initialNode.substitute(s);
                            initialNode.normalize(argSet, normalizeSignature);
                            (*result.subtasks[i])[child._name_id] = initialNode;
                        } else {
                            newNumNodes -= (*result.subtasks[i])[child._name_id].numNodes;
                        }
                        PFCNode& currentChildNode = (*result.subtasks[i])[child._name_id];

                        PFCNode childNode;
                        childNode.sig = childFrame.sig;
                        childNode.effects = childFrame.effects;
                        childNode.rigidPreconditions = _util.filterFluentPredicates(childFrame.preconditions, _fluent_predicates);
                        childNode.fluentPreconditions = _util.filterRigidPredicates(childFrame.preconditions, _fluent_predicates);                        childNode.subtasks = childFrame.subtasks;
                        childNode.maxDepth = childFrame.maxDepth;
                        childNode.numNodes = childFrame.numNodes;
                        // Retrieve child's fact frame
                        if (childNode.numNodes > currentChildNode.numNodes) {
                            //Log::e("Normalize if\n");
                            normalizeSubstituteNodeDiff(childNode, currentChildNode, argSet, s, normalizeSignature, DEPTH_LIMIT-1);
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
void FactAnalysisPreprocessing::normalizeSubstituteNodeDiff(const PFCNode& newNode, PFCNode& nodeToExtend, const FlatHashSet<int>& argSet, const Substitution& s, 
        std::function<Signature(const Signature& sig, FlatHashSet<int> argSet)> normalizeFunction, int depthLimit) {
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
                (*nodeToExtend.subtasks[i])[id].normalize(argSet, normalizeFunction);
            } else if (child.numNodes > (*nodeToExtend.subtasks[i])[id].numNodes) {
                normalizeSubstituteNodeDiff(child, (*nodeToExtend.subtasks[i])[id], argSet, s, normalizeFunction, depthLimit-1);
            }
            PFCNode& extendedNode = (*nodeToExtend.subtasks[i])[id];
            maxDepth = extendedNode.maxDepth+1 > maxDepth ? extendedNode.maxDepth+1 : maxDepth;
            numNodes += extendedNode.numNodes;
        }
    }
    nodeToExtend.maxDepth = maxDepth;
    nodeToExtend.numNodes = numNodes;
}
