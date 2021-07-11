
#include "fact_analysis.h"
#include "util/log.h"

#include "algo/topological_ordering.h"

int DEPTH_LIMIT = 1;
const int NODE_LIMIT = 100;

std::vector<int> FactAnalysis::findCycle(int nodeToFind, std::vector<int>& adjacentNodes, std::map<int, std::vector<int>>& orderingOplist, std::vector<int>& traversedNodes) {
    for (const auto& adjacentNode : adjacentNodes) {
        Log::d("NodeToFind: %i, adjacentNode: %i\n", nodeToFind, adjacentNode);
        bool cycle = false;
        for (const auto& traversedNode: traversedNodes) {
            Log::d("TraversedNode: %i\n", traversedNode);
            if (traversedNode == adjacentNode) cycle = true;
        }
        if (cycle) {
            if (adjacentNode == nodeToFind) {
                Log::d("Found cycle!\n");
                traversedNodes.push_back(adjacentNode);
                return traversedNodes;
            } else {
                continue;
            }
        } else {
            std::vector<int> newTraversedNodes = traversedNodes;
            newTraversedNodes.push_back(adjacentNode);
            return findCycle(nodeToFind, orderingOplist[adjacentNode], orderingOplist, newTraversedNodes);
        }
    }
    return std::vector<int>();
}

// recursively extends nodeToExtend with the new nodes in newNode until the depthLimit, the new nodes are substituted and normalized
void FactAnalysis::normalizeSubstituteNodeDiff(const PFCNode& newNode, PFCNode& nodeToExtend, const FlatHashSet<int>& argSet, const Substitution& s, 
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

void FactAnalysis::computeFactFrames() {

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
            _traversal.getPossibleChildren(reduction.getSubtasks(), i, children);
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

    auto normalizeSignature = [&](const Signature& sig, FlatHashSet<int> argSet) {
        Signature newSig = sig;
        for (size_t j = 0; j < newSig._usig._args.size(); j++) {
            int& arg = newSig._usig._args[j];
            if (!argSet.count(arg)) arg = _htn.nameId("??_");
        }
        return newSig;
    };

    findFluentPredicates(orderedOpIds);

    // Repeatedly extend the operations' fact frames until convergence of fact changes
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
                    SigSet filteredPrereqs = filterFluentPredicates(action.getPreconditions());
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
                    SigSet filteredPrereqs = filterFluentPredicates(action.getPreconditions());
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

                // For each subtask of the reduction
                for (size_t i = 0; i < reduction.getSubtasks().size(); i++) {

                    // Find all possible child operations for this subtask
                    std::vector<USignature> children;
                    _traversal.getPossibleChildren(reduction.getSubtasks(), i, children);
                    
                    // For each such child operation
                    for (const auto& child : children) {
                        // Fact frame for this child already present?
                        if (_fact_frames.count(child._name_id)) {
                            // Retrieve child's fact frame
                            FactFrame childFrame = getFactFrame(child);
                            SigSet normalizedEffects;
                            for (auto& eff : childFrame.effects) normalizedEffects.insert(normalizeSignature(eff, argSet));

                            Sig::unite(normalizedEffects, result.effects);
                            Sig::unite(normalizedEffects, result.offsetEffects[i]);
                        }
                    }
                }

                if (result.effects.size() > priorEffs) {
                    change = true;
                }
            } else {
                Log::d("FF %s : unmatched\n", TOSTR(opId));
            }
        }
    }

    int avgBranchDegreeArithmetic = 0;
    int numRedcutions = 0;
    // In a next step, use the converged fact changes to infer preconditions
    for (int i = orderedOpIds.size()-1; i >= 0; i--) {
        int opId = orderedOpIds[i];
        Log::d("FF %i : %s\n", i, TOSTR(opId));
        if (_htn.isReduction(opId) && !_htn.isReductionPrimitivizable(opId)) {
            numRedcutions++;
            const auto& reduction = _htn.getAnonymousReduction(opId);
            FlatHashSet<int> argSet(reduction.getArguments().begin(), reduction.getArguments().end());
            FactFrame& result = _fact_frames[opId];

            // Effects which may be caused by the operation up to the current subtask
            SigSet effects;
            // For each subtask of the reduction
            for (size_t i = 0; i < reduction.getSubtasks().size(); i++) {    

                // Find all possible child operations for this subtask
                std::vector<USignature> children;
                _traversal.getPossibleChildren(reduction.getSubtasks(), i, children);
                
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
    avgBranchDegreeArithmetic = int(avgBranchDegreeArithmetic/numRedcutions);
    DEPTH_LIMIT = std::min(int(std::log(NODE_LIMIT) / std::log(avgBranchDegreeArithmetic)), 1);
    Log::e("avgBranchDegreeArithmetic: %i\n", avgBranchDegreeArithmetic);
    Log::e("DEPTH_LIMIT: %i\n", DEPTH_LIMIT);

    // Repeatedly extend the operations' fact frames until convergence of fact changes
    change = true;
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
                    _traversal.getPossibleChildren(reduction.getSubtasks(), i, children);


                    // For each such child operation
                    for (const auto& child : children) {

                        FactFrame& childFrame = _fact_frames.at(child._name_id);
                        Substitution s = Substitution(childFrame.sig._args, child._args);
                        if (!(*result.subtasks[i]).count(child._name_id)) {
                            PFCNode initialNode;
                            initialNode.sig = childFrame.sig;
                            initialNode.effects = childFrame.effects;
                            initialNode.preconditions = filterFluentPredicates(childFrame.preconditions);
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
                        childNode.preconditions = filterFluentPredicates(childFrame.preconditions);
                        childNode.subtasks = childFrame.subtasks;
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
        avgNumNodes = int(avgNumNodes / numRedcutions);
        Log::e("avgNumNodes: %i\n", avgNumNodes);
    }

    // for (const auto& [id, ff] : _fact_frames) {
    //     Log::d("FF: %s\n", TOSTR(ff));
    // }
}

FactFrame FactAnalysis::getFactFrame(const USignature& sig) {
    const FactFrame& f = _fact_frames.at(sig._name_id);
    return f.substitute(Substitution(f.sig._args, sig._args));
}

SigSet FactAnalysis::getPossibleFactChangesOld(const USignature& sig) {
    
    SigSet result;
    for (const auto& fact : getFactFrame(sig).effects) {
        if (fact._usig._args.empty()) result.insert(fact);
        else for (const USignature& groundFact : ArgIterator::getFullInstantiation(fact._usig, _htn)) {
            result.emplace(groundFact, fact._negated);
        }
    }
    Log::d("PFC %s : %s\n", TOSTR(sig), TOSTR(result));
    return result;
}

SigSet FactAnalysis::getPossibleFactChangesTree(const USignature& sig) {
    //Log::e("getPossibleFactChanges for: %s\n", TOSTR(sig));
    FlatHashMap<int, USigSet> effectsNegative;
    FlatHashMap<int, USigSet> effectsPositive;

    SigSet result;
    FactFrame& factFrame = _fact_frames.at(sig._name_id);
    Substitution s = Substitution(factFrame.sig._args, sig._args);

    int MAX_DEPTH = 1;
    if (factFrame.numNodes == 1) {
        SigSet subtitutedEffects;
        for (const auto& effect: factFrame.effects) {
            subtitutedEffects.insert(effect.substitute(s));
        }
        for (const auto& eff: subtitutedEffects) {
            if (eff._usig._args.empty()) {
                result.insert(eff);
            } else if (eff._negated) {
                effectsNegative[eff._usig._name_id].insert(eff._usig);
            } else {
                effectsPositive[eff._usig._name_id].insert(eff._usig);
            }
        }
    } else {
        std::vector<NodeHashMap<int, PFCNode>*> subtasks = factFrame.subtasks;
        for (int i = 0; i < MAX_DEPTH; i++) {
            std::vector<NodeHashMap<int, PFCNode>*> newSubtasks;
            for (const auto& subtask: subtasks) {
                bool subtaskValid = false;
                //Log::e("subtasksize: %i\n", (*subtask).size());
                for (const auto& child: *subtask) {
                    //Log::e("Checking child: %s\n", TOSTR(child.second.sig._name_id));
                    SigSet substitutedPreconditions;
                    for (const auto& prereq: child.second.preconditions) {
                        //Log::e("Unsubstituted prereq: %s\n", TOSTR(prereq));
                        substitutedPreconditions.insert(prereq.substitute(s));
                    }
                    bool preconditionsValid = true;
                    // Check if any precondition is rigid and not valid in the initState
                    for (const auto& precondition : substitutedPreconditions) {
                        //Log::d("checking precondition: %s\n", TOSTR(precondition));
                        if (_htn.isFullyGround(precondition._usig) && !_htn.hasQConstants(precondition._usig)) {
                            //Log::d("Found ground precondition without qconstants: %s\n", TOSTR(precondition));
                            preconditionsValid = !precondition._negated != !_init_state.count(precondition._usig);
                        } else {
                            preconditionsValid = false;
                            for (const USignature& groundFact : ArgIterator::getFullInstantiationQConst(precondition._usig, _htn)) {
                                //Log::d("Ground fact: %s\n", TOSTR(groundFact));
                                if (_init_state.count(groundFact) == !precondition._negated) {
                                    preconditionsValid = true;
                                    break;
                                }
                            }
                        }
                        if (!preconditionsValid) {
                            //Log::e("Found invalid rigid precondition: %s\n", TOSTR(precondition));
                            _invalid_preconditions_found++;
                            break;
                        }
                    }

                    if (preconditionsValid) {
                        subtaskValid = true;
                        if (child.second.numNodes == 1 || i+1 == MAX_DEPTH) {
                            SigSet subtitutedEffects;
                            for (const auto& effect: child.second.effects) {
                                subtitutedEffects.insert(effect.substitute(s));
                            }
                            for (const auto& eff: subtitutedEffects) {
                                if (eff._usig._args.empty()) {
                                    result.insert(eff);
                                } else if (eff._negated) {
                                    effectsNegative[eff._usig._name_id].insert(eff._usig);
                                } else {
                                    effectsPositive[eff._usig._name_id].insert(eff._usig);
                                }
                            }
                        } else {
                            for (const auto& subtask: child.second.subtasks) {
                                newSubtasks.push_back(subtask);
                            }
                        }
                    }
                }
                if (!subtaskValid) {
                    Log::e("Found invalid subtask at depth %i\n", i);
                    _invalid_subtasks_found++;
                    if (i == 0) {
                        throw std::invalid_argument("getPFC: Operator has subtask with no valid children\n");
                    }
                }
            }
            subtasks = newSubtasks;
        }
    }

    USigSet negativeEffectsToGround;
    for (const auto& [argname, effects]: effectsNegative) {
        USigSet dominatedSignatures;
        for (const auto& eff: effects) {
            if (!dominatedSignatures.count(eff)) {
                for (const auto& innerEff: effects) {
                    if (!dominatedSignatures.count(innerEff) && eff != innerEff) {
                        if (dominates(innerEff, eff)) {
                            dominatedSignatures.insert(eff);
                            break;
                        } else if (dominates(eff, innerEff)) {
                            dominatedSignatures.insert(innerEff);
                        }
                    }
                }
                if (!dominatedSignatures.count(eff)) negativeEffectsToGround.insert(eff);
            }
        }
    }

    USigSet positiveEffectsToGround;
    for (const auto& [argname, effects]: effectsPositive) {
        USigSet dominatedSignatures;
        for (const auto& eff: effects) {
            if (!dominatedSignatures.count(eff)) {
                for (const auto& innerEff: effects) {
                    if (!dominatedSignatures.count(innerEff) && eff != innerEff) {
                        if (dominates(innerEff, eff)) {
                            dominatedSignatures.insert(eff);
                            break;
                        } else if (dominates(eff, innerEff)) {
                            dominatedSignatures.insert(innerEff);
                        }
                    }
                }
                if (!dominatedSignatures.count(eff)) positiveEffectsToGround.insert(eff);
            }

        }
    }

    for (const auto& positiveEffect: positiveEffectsToGround) {
        for (const USignature& groundFact : ArgIterator::getFullInstantiation(positiveEffect, _htn)) {
            result.emplace(groundFact, false);
        }
    }
    for (const auto& negativeEffect: negativeEffectsToGround) {
        for (const USignature& groundFact : ArgIterator::getFullInstantiation(negativeEffect, _htn)) {
            result.emplace(groundFact, true);
        }
    }
    //Log::d("PFC %s : %s\n", TOSTR(sig), TOSTR(result));
    return result;
}

SigSet FactAnalysis::getPossibleFactChanges(const USignature& sig) {
    Log::d("getPossibleFactChanges for: %s\n", TOSTR(sig));
    FlatHashMap<int, USigSet> effectsNegative;
    FlatHashMap<int, USigSet> effectsPositive;
    SigSet liftedResult;
    SigSet result;
    FactFrame factFrame = getFactFrame(sig);

    // Iterate through all conditionalEffects in factFrame
    for (const auto& conditionalEffect : factFrame.conditionalEffects) {
        //Log::d("checking conditionalEffect with prereqs: %s, and effects: %s\n", TOSTR(conditionalEffect)), TOSTR(std::get<1>(conditionalEffect)));
        bool reachable = true;

        // Check if any prerequisite of the conditionalEffect is rigid and not reachable in the initState
        for (const auto& prerequisite : conditionalEffect.first) {
            //Log::d("checking conditionalEffect prereqs: %s\n", TOSTR(prerequisite));
            if (_htn.isFullyGround(prerequisite._usig) && !_htn.hasQConstants(prerequisite._usig)) {
                //Log::d("Found rigid predicate: %s\n", TOSTR(prerequisite));
                reachable = !prerequisite._negated != !_init_state.count(prerequisite._usig);

                if (!reachable) {
                    //Log::d("Found impossible rigid prereq: %s\n", TOSTR(prerequisite));
                    break;
                }
            }
        }

        // If any rigid, non-reachable prerequisite is found, don't add the conditionalEffects to the PFC,
        if (!reachable) {
            //Log::d("Not adding the following effects: %s\n", TOSTR(conditionalEffect.second));
            continue;
        }

        for (const auto& fact : conditionalEffect.second) {
            //Log::d("adding conditionalEffect effects: %s\n", TOSTR(fact));
            if (fact._usig._args.empty()) {
                result.insert(fact);
            } else if (fact._negated) {
                effectsNegative[fact._usig._name_id].insert(fact._usig);
            } else {
                effectsPositive[fact._usig._name_id].insert(fact._usig);
            }
        }
    }
    
    USigSet negativeEffectsToGround;
    for (const auto& [argname, effects]: effectsNegative) {
        USigSet dominatedSignatures;
        for (const auto& eff: effects) {
            if (!dominatedSignatures.count(eff)) {
                for (const auto& innerEff: effects) {
                    if (!dominatedSignatures.count(innerEff) && eff != innerEff) {
                        if (dominates(innerEff, eff)) {
                            dominatedSignatures.insert(eff);
                            break;
                        } else if (dominates(eff, innerEff)) {
                            dominatedSignatures.insert(innerEff);
                        }
                    }
                }
                if (!dominatedSignatures.count(eff)) negativeEffectsToGround.insert(eff);
            }
        }
    }

    USigSet positiveEffectsToGround;
    for (const auto& [argname, effects]: effectsPositive) {
        USigSet dominatedSignatures;
        for (const auto& eff: effects) {
            if (!dominatedSignatures.count(eff)) {
                for (const auto& innerEff: effects) {
                    if (!dominatedSignatures.count(innerEff) && eff != innerEff) {
                        if (dominates(innerEff, eff)) {
                            dominatedSignatures.insert(eff);
                            break;
                        } else if (dominates(eff, innerEff)) {
                            dominatedSignatures.insert(innerEff);
                        }
                    }
                }
                if (!dominatedSignatures.count(eff)) positiveEffectsToGround.insert(eff);
            }

        }
    }

    for (const auto& positiveEffect: positiveEffectsToGround) {
        for (const USignature& groundFact : ArgIterator::getFullInstantiation(positiveEffect, _htn)) {
            result.emplace(groundFact, false);
        }
    }
    for (const auto& negativeEffect: negativeEffectsToGround) {
        for (const USignature& groundFact : ArgIterator::getFullInstantiation(negativeEffect, _htn)) {
            result.emplace(groundFact, true);
        }
    }
    //Log::d("PFC %s : %s\n", TOSTR(sig), TOSTR(result));
    return result;
}


SigSet FactAnalysis::getPossibleFactChangesAlt(const USignature& sig) {
    Log::d("getPossibleFactChanges for: %s\n", TOSTR(sig));
    SigSet liftedResult;
    SigSet result;
    FactFrame factFrame = getFactFrame(sig);
    
    // Iterate through all conditionalEffects in factFrame
    for (const auto& conditionalEffect : factFrame.conditionalEffects) {
        //Log::d("checking conditionalEffect with prereqs: %s, and effects: %s\n", TOSTR(conditionalEffect)), TOSTR(std::get<1>(conditionalEffect)));
        bool reachable = true;

        // Check if any prerequisite of the conditionalEffect is rigid and not reachable in the initState
        for (const auto& prerequisite : conditionalEffect.first) {
            //Log::d("checking conditionalEffect prereqs: %s\n", TOSTR(prerequisite));
            if (_htn.isFullyGround(prerequisite._usig) && !_htn.hasQConstants(prerequisite._usig)) {
                //Log::d("Found rigid predicate: %s\n", TOSTR(prerequisite));
                reachable = !prerequisite._negated != !_init_state.count(prerequisite._usig);
                if (!reachable) {
                    //Log::d("Found impossible rigid prereq: %s\n", TOSTR(prerequisite));
                    break;
                }
            }
        }

        // If any rigid, non-reachable prerequisite is found, don't add the conditionalEffects to the PFC,
        if (!reachable) {
            //Log::d("Not adding the following effects: %s\n", TOSTR(conditionalEffect.second));
            continue;
        }

        // otherwise add them as before.
        for (const auto& fact : conditionalEffect.second) {
            //Log::d("adding conditionalEffect effects: %s\n", TOSTR(fact));
            if (!liftedResult.count(fact)) {
                liftedResult.insert(fact);
                if (fact._usig._args.empty()) result.insert(fact);
                else for (const USignature& groundFact : ArgIterator::getFullInstantiation(fact._usig, _htn)) {
                    result.emplace(groundFact, fact._negated);
                }
            }
        }
    }
    //Log::d("PFC %s : %s\n", TOSTR(sig), TOSTR(result));
    return result;
}


bool FactAnalysis::dominates(const USignature& dominator, const USignature& dominee) {
    for (size_t i = 0; i < dominator._args.size(); i++) {
        int arg = dominator._args[i];
        if (_htn.isVariable(arg)) {
            if (_htn.isQConstant(dominee._args[i])) return false;
        } else {
            if (arg != dominee._args[i]) return false;
        }
    }
    return true;
}

std::vector<FlatHashSet<int>> FactAnalysis::getReducedArgumentDomains(const HtnOp& op) {

    const std::vector<int>& args = op.getArguments();
    const std::vector<int>& sorts = _htn.getSorts(op.getNameId());
    std::vector<FlatHashSet<int>> domainPerVariable(args.size());
    std::vector<bool> occursInPreconditions(args.size(), false);

    // Check each precondition regarding its valid decodings w.r.t. current state
    //const SigSet* preSets[2] = {&op.getPreconditions(), &op.getExtraPreconditions()};
    const SigSet* preSets[1] = {&op.getPreconditions()};
    for (const auto& preSet : preSets) for (const auto& preSig : *preSet) {

        // Find mapping from precond args to op args
        std::vector<int> opArgIndices(preSig._usig._args.size(), -1);
        for (size_t preIdx = 0; preIdx < preSig._usig._args.size(); preIdx++) {
            const int& arg = preSig._usig._args[preIdx];
            for (size_t i = 0; i < args.size(); i++) {
                if (args[i] == arg) {
                    opArgIndices[preIdx] = i;
                    occursInPreconditions[i] = true;
                    break;
                }
            }
        }

        if (!_htn.hasQConstants(preSig._usig) && _htn.isFullyGround(preSig._usig)) {
            // Check base condition; if unsatisfied, discard op 
            if (!isReachable(preSig)) return std::vector<FlatHashSet<int>>();
            // Add constants to respective argument domains
            for (size_t i = 0; i < preSig._usig._args.size(); i++) {
                domainPerVariable[opArgIndices[i]].insert(preSig._usig._args[i]);
            }
            continue;
        }

        // Compute sorts of the condition's args w.r.t. op signature
        std::vector<int> preSorts(preSig._usig._args.size());
        for (size_t i = 0; i < preSorts.size(); i++) {
            assert(i < opArgIndices.size());
            assert(opArgIndices[i] < (int)sorts.size());
            assert(i < preSorts.size());
            Log::d("%s %s\n", TOSTR(op.getSignature()), TOSTR(preSig));
            preSorts[i] = sorts[opArgIndices[i]];
        }

        // Check possible decodings of precondition
        bool any = false;
        bool anyValid = false;
        for (const auto& decUSig : _htn.decodeObjects(preSig._usig, _htn.getEligibleArgs(preSig._usig, preSorts))) {
            any = true;
            assert(_htn.isFullyGround(decUSig));

            // Valid?
            if (!isReachable(decUSig, preSig._negated)) continue;
            
            // Valid precondition decoding found: Increase domain of concerned variables
            anyValid = true;
            for (size_t i = 0; i < opArgIndices.size(); i++) {
                int opArgIdx = opArgIndices[i];
                if (opArgIdx >= 0) {
                    domainPerVariable[opArgIdx].insert(decUSig._args[i]);
                }
            }
        }
        if (any && !anyValid) return std::vector<FlatHashSet<int>>();
    }

    for (size_t i = 0; i < args.size(); i++) {
        if (!occursInPreconditions[i]) domainPerVariable[i] = _htn.getConstantsOfSort(sorts[i]);
    }

    return domainPerVariable;
}

// Iterate though all operations and find all predicates occuring in any actions effects (fluent predicates)
// to fill _fluent_predicates, and thus also implicitly identify rigid predicates.
void FactAnalysis::findFluentPredicates(const std::vector<int>& orderedOpIds) {
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
                _fluent_predicates.insert(effect._usig._name_id);
            }

        } else if (_htn.isReductionPrimitivizable(opId)) {
            // Primitivization of a reduction, i.e., essentially just an action
            int aId = _htn.getReductionPrimitivizationName(opId);
            Action action = _htn.getAnonymousAction(aId);
            for (auto effect : action.getEffects()) {
                Log::d("Found fluent predicate: %s\n", TOSTR(effect));
                _fluent_predicates.insert(effect._usig._name_id);
            }
        }
    }
}

SigSet FactAnalysis::filterFluentPredicates(const SigSet& unfiltered) {
    SigSet filteredSigSet;
    for (auto& prereq :  unfiltered) {
        if (!_fluent_predicates.count(prereq._usig._name_id)) {
            filteredSigSet.insert(prereq);
        }
    }
    return filteredSigSet;
}

// Logs error if an effect in a FactFrames .effect attribute is not contained in any of its conditionalEffects
// Logs warning if it finds any duplicates (same hashvalue) in the conditionalEffect NodeHashMap
void FactAnalysis::testConditionalEffects(std::vector<int>& orderedOpIds) {
    for (int i = orderedOpIds.size()-1; i >= 0; i--) {
        int opId = orderedOpIds[i];
        for (const auto& eff: _fact_frames[opId].effects) {
            bool found = false;
            for (const auto& conditionalEffect: _fact_frames[opId].conditionalEffects) {
                if (conditionalEffect.second.count(eff)) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                Log::e("Could NOT find the original effect %s in any conditionalEffect SigSet\n", TOSTR(eff));
            } else {
                Log::d("Found the original effect %s in a conditionalEffect\n", TOSTR(eff));
            }
        }
        FlatHashMap<int, std::vector<SigSet>> duplicates;
        SigSetHasher sigSetHasher;
        for (auto & [prereqs, effects] : _fact_frames[opId].conditionalEffects) { 
            Log::d("prereqs: %s, effects: %s, hash: %i\n", TOSTR(prereqs), TOSTR(effects), sigSetHasher(prereqs));
            duplicates[sigSetHasher(prereqs)].push_back(prereqs);
        }
        for (auto & [hashvalue, duplicateKeys] : duplicates) {
            if (duplicateKeys.size() > 1) {
                Log::w("Found duplicate keys in conditionalEffect prereqs:\n");
                for (auto & key : duplicateKeys) {
                    Log::d("%s\n", TOSTR(key));
                }
                Log::w("==: %s\n", duplicateKeys[0] == duplicateKeys[1] ? "TRUE" : "FALSE");
                if (duplicateKeys[0] != duplicateKeys[1]) {
                    if (duplicateKeys[0].size() != duplicateKeys[1].size()) {
                        Log::d("Not equal cause size different %i vs %i\n", duplicateKeys[0].size(), duplicateKeys[1].size());
                    }
                    for (const auto& sig : duplicateKeys[1]) {
                        if (!duplicateKeys[1].count(sig)) {
                            Log::d("Couldn't find %s in %s\n", TOSTR(sig), TOSTR(duplicateKeys[1]));
                            for (const auto& sig_: duplicateKeys[1]) {
                                Log::d("%s ==? %s: %s \n", TOSTR(sig), TOSTR(sig_), sig == sig_ ? "TRUE" : "FALSE");
                            }
                        }
                    }
                }
            }
        }   
    }
}