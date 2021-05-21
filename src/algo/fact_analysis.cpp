
#include "fact_analysis.h"
#include "util/log.h"

#include "algo/topological_ordering.h"

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
                //Log::d("isAction Log message: FF %i : %s\n", i, TOSTR(opId));

                // Action: Setting fact frame is trivial
                int aId = opId;
                if (_htn.isActionRepetition(opId)) aId = _htn.getActionNameFromRepetition(opId);
                Action action = _htn.getAnonymousAction(aId);
                if (_fact_frames[opId].sig != action.getSignature()) {
                    _fact_frames[opId].sig = action.getSignature();
                    _fact_frames[opId].preconditions = action.getPreconditions();
                    _fact_frames[opId].effects = action.getEffects();
                    SigSet newPreReqs;
                    for (auto& prereq :  action.getPreconditions()) {
                        if (!_fluent_predicates.count(prereq._usig._name_id)) {
                            newPreReqs.insert(prereq);
                        }
                    }
                    _fact_frames[opId].conditionalEffects[newPreReqs] = action.getEffects();
                    change = true;
                } // else: fact frame already set

            } else if (_htn.isReductionPrimitivizable(opId)) {
                //Log::d("isReductionPrimitivizable Log message: FF %i : %s\n", i, TOSTR(opId));

                // Primitivization of a reduction, i.e., essentially just an action
                int aId = _htn.getReductionPrimitivizationName(opId);
                Action action = _htn.getAnonymousAction(aId);
                if (_fact_frames[opId].sig != action.getSignature()) {
                    _fact_frames[opId].sig = action.getSignature();
                    _fact_frames[opId].preconditions = action.getPreconditions();
                    _fact_frames[opId].effects = action.getEffects();
                    SigSet newPreReqs;
                    for (auto& prereq :  action.getPreconditions()) {
                        if (!_fluent_predicates.count(prereq._usig._name_id)) {
                            newPreReqs.insert(prereq);
                        }
                    }
                    _fact_frames[opId].conditionalEffects[newPreReqs] = action.getEffects();
                    change = true;
                } // else: fact frame already set

            } else if (_htn.isReduction(opId)) {
                //Log::d("isReduction Log message: FF %i : %s\n", i, TOSTR(opId));

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
                    priorCondTotalEffs += conditionalEffect.second.size();
                }
                NodeHashMap<SigSet, SigSet, SigSetHasher> oldconditionalEffects = result.conditionalEffects;
                result.conditionalEffects = NodeHashMap<SigSet, SigSet, SigSetHasher>{};
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
                            for (auto& eff : childFrame.effects) eff = normalizeSignature(eff, argSet);

                            // Add all of the child's effects to the parent's effects
                            Sig::unite(childFrame.effects, result.effects);
                            Sig::unite(childFrame.effects, result.offsetEffects[i]);

                            for (auto& conditionalEffect : childFrame.conditionalEffects) {
                                for (auto& eff : conditionalEffect.second) {
                                    eff = normalizeSignature(eff, argSet);
                                }
                            }

                            //Log::d("Preconditions size: %i\n", childFrame.conditionalEffects.size());
                            //Log::d("Reduction preconditions: %s\n", TOSTR(result.preconditions));
                            for (auto& conditionalEffect : childFrame.conditionalEffects) {
                                if (conditionalEffect.second.size() == 0) continue;
                                SigSet new_prereqs = conditionalEffect.first;
                                for (auto& prereq : new_prereqs) {
                                    prereq = normalizeSignature(prereq, argSet);
                                }
                                SigSet resultPreconditions;
                                for (auto& prereq : result.preconditions) {
                                    if (!_fluent_predicates.count(prereq._usig._name_id)) {
                                        resultPreconditions.insert(prereq);
                                    }
                                }
                                Sig::unite(resultPreconditions, new_prereqs);
                                Sig::unite(conditionalEffect.second, result.conditionalEffects[new_prereqs]);
                            }
                        }
                    }
                }
                size_t newCondTotalEffs = 0;
                for (auto& conditionalEffect : result.conditionalEffects) {
                    newCondTotalEffs += conditionalEffect.second.size();
                }
                // Check if the fact frame has been extended non-trivially
                Log::d("\nOriginal: Prior size: %i, new size: %i\n", priorEffs, result.effects.size());
                Log::d("Conditional: Prior size: %i, new size: %i\n\n", priorCondEffs, result.conditionalEffects.size());
                if (result.effects.size() > priorEffs) {
                    change = true;
                } else if (result.conditionalEffects.size() != priorCondEffs or newCondTotalEffs > priorCondTotalEffs) {
                    change = true;
                    Log::d("Effect size didn't change but conditionalEffects did:\n");
                    // SigSetHasher sigSetHasher;
                    // for (auto & [prereqs, effects] : result.conditionalEffects) { 
                    //     Log::d("Sanitycheck\n");
                    //     Log::d("prereqs: %s, effects: %s, hash: %i\n", TOSTR(prereqs), TOSTR(effects), sigSetHasher(prereqs));
                    //     //Log::d("effects: %s, hash: %i\n", TOSTR(result.conditionalEffects[prereqs]), sigSetHasher(prereqs));
                    //     Log::d("Sanitycheck\n");
                    // }
                    for (auto & [prereqs, effects] : result.conditionalEffects) { 
                        SigSetHasher sigSetHasher;
                        if (sigSetHasher(effects) != sigSetHasher(oldconditionalEffects[prereqs])) {
                            if (oldconditionalEffects[prereqs].size() != 0) {
                                Log::d("NEW: prereqs: %s, effects: %s, hash: %i\n", TOSTR(prereqs), TOSTR(effects), sigSetHasher(prereqs));
                                //Log::d("effects: %s, hash: %i\n", TOSTR(result.conditionalEffects[prereqs]), sigSetHasher(prereqs));
                                Log::d("OLD: prereqs: %s, effects: %s, hash: %i\n", TOSTR(prereqs), TOSTR(oldconditionalEffects[prereqs]), sigSetHasher(prereqs));
                            }
                        }
                    }
                }

            } else {
                Log::d("FF %s : unmatched\n", TOSTR(opId));
            }
        }
    }
    
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
                Log::d("Could NOT find the original effect %s in any conditionalEffect SigSet\n", TOSTR(eff));
            } else {
                Log::d("Found the original effect %s in a conditionalEffect\n", TOSTR(eff));
            }
            
        }
    }

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
                _traversal.getPossibleChildren(reduction.getSubtasks(), i, children);
                
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

            // Clear unneeded cached offset effects
            result.offsetEffects.clear();
        }
    }

    for (const auto& [id, ff] : _fact_frames) {
        Log::d("FF %s\n", TOSTR(ff));
    }
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

SigSet FactAnalysis::getPossibleFactChanges(const USignature& sig) {
    Log::d("getPossibleFactChanges for: %s\n", TOSTR(sig));
    SigSet liftedResult;
    SigSet result;
    FactFrame factFrame = getFactFrame(sig);
    const USigSet initState = _htn.getInitState();
    
    // Iterate through all conditionalEffects in factFrame
    for (const auto& conditionalEffect : factFrame.conditionalEffects) {
        //Log::d("checking conditionalEffect with prereqs: %s, and effects: %s\n", TOSTR(conditionalEffect)), TOSTR(std::get<1>(conditionalEffect)));
        bool reachable = true;

        // Check if any prerequisite of the conditionalEffect is rigid and not reachable in the initState
        for (const auto& prerequisite : conditionalEffect.first) {
            //Log::d("checking conditionalEffect prereqs: %s\n", TOSTR(prerequisite));
            if (_htn.isFullyGround(prerequisite._usig) && !_htn.hasQConstants(prerequisite._usig)) {
                Log::d("Found rigid predicate: %s\n", TOSTR(prerequisite));
                reachable = !prerequisite._negated != !initState.count(prerequisite._usig);
                // for (const USignature& groundFact : ArgIterator::getFullInstantiation(prerequisite._usig, _htn)) {
                //     Log::d("checking conditionalEffect prereqs: %s, groundFact: %s\n", TOSTR(prerequisite), TOSTR(groundFact));
                //     if (initState.count(groundFact)) {
                //         Log::d("Found groundfact in initstate\n");
                //         reachable = true;
                //         break;
                //     }
                // }
                if (!reachable) {
                    Log::d("Found impossible rigid prereq: %s\n", TOSTR(prerequisite));
                    break;
                }
            }
        }

        // If any rigid, non-reachable prerequisite is found, don't add the conditionalEffects to the PFC,
        if (!reachable) {
            Log::d("Not adding the following effects: %s\n", TOSTR(conditionalEffect.second));
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
            } else {
                Log::d("FACT ALREADY ADDED TO PFC\n");
            }
        }
    }
    Log::d("PFC %s : %s\n", TOSTR(sig), TOSTR(result));
    return result;
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
            // Action: Setting fact frame is trivial
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

        } //else if (_htn.isReduction(opId)) {
            // dont do anything since reduction doesn't have it's own "direct" effects (?)
    }
}