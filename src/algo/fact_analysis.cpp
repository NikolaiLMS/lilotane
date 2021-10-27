#include "fact_analysis.h"
#include "util/log.h"


void FactAnalysis::computeFactFrames() {}
SigSet FactAnalysis::getPossibleFactChanges(const USignature& sig) {}

void FactAnalysis::substituteEffectsAndAdd(const SigSet& effects, Substitution& s, NodeHashMap<int, USigSet>& positiveEffects,
     NodeHashMap<int, USigSet>& negativeEffects, NodeHashMap<int, SigSet>& postconditions, NodeHashMap<int, FlatHashSet<int>>& globalFreeArgRestrictions) {
    SigSet subtitutedEffects;
    for (const auto& effect: effects) {
        subtitutedEffects.insert(effect.substitute(s));
    }
    for (auto& eff: subtitutedEffects) {
        //Log::e("Adding effect %s\n", TOSTR(eff));
        if (postconditions.count(eff._usig._name_id)) {
            SigSet toDelete;
            for (const auto& postcondition: postconditions[eff._usig._name_id]) {
                if (postcondition._negated != eff._negated) {
                    toDelete.insert(postcondition);
                }
            }

            for (const auto& postcondition: toDelete) {
                postconditions[postcondition._usig._name_id].erase(postcondition);
            }
        }
        for (size_t argPosition = 0; argPosition < eff._usig._args.size(); argPosition++) {
            if (_htn.isVariable(eff._usig._args[argPosition]) && !globalFreeArgRestrictions.count(eff._usig._args[argPosition])) {
                eff._usig._args[argPosition] = _name_id_;
            }
        }
        if (eff._negated) {
            negativeEffects[eff._usig._name_id].insert(eff._usig);
        } else {
            positiveEffects[eff._usig._name_id].insert(eff._usig);
        }
    }
}

bool FactAnalysis::restrictNewVariables(SigSet& preconditions, SigSet& fluentPreconditions, Substitution& s, NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions, 
        FlatHashMap<int, FlatHashMap<USignature, FlatHashSet<int>, USignatureHasher>>& rigid_predicate_cache, FlatHashSet<int> nodeArgs,
        NodeHashMap<int, USigSet>& foundEffectsPositive, NodeHashMap<int, USigSet>& foundEffectsNegative,
        NodeHashMap<int, SigSet>& postconditions, Substitution& globalSub) {
    //Log::e("restrict var call\n");
    bool valid = true;
    SigSet preconditionsToRemove;
    //Log::e("Unsubstituted rigid preconditions: %s\n", TOSTR(preconditions));
    for (auto& substitutedPrecondition: preconditions) {
        substitutedPrecondition.apply(s);
        if (substitutedPrecondition._negated) {
            continue;
        }
        //Log::e("Checking rigid precondition %s\n", TOSTR(substitutedPrecondition));
        for (size_t argPosition = 0; argPosition < substitutedPrecondition._usig._args.size(); argPosition++) 
                if (nodeArgs.count(substitutedPrecondition._usig._args[argPosition])) {
            FlatHashSet<int> newRestrictions;
            int actualArg = substitutedPrecondition._usig._args[argPosition];
            substitutedPrecondition._usig._args[argPosition] = _name_id_;
            ArgIterator iter = ArgIterator::getFullInstantiation(substitutedPrecondition._usig, _htn, freeArgRestrictions, true, argPosition);
            substitutedPrecondition._usig._args[argPosition] = actualArg;
            if (iter.size() > _new_variable_domain_size_limit) continue;
            bool reachedLimit = false;
            for (const USignature& groundFact : iter) {
                //Log::d("Ground fact: %s\n", TOSTR(groundFact));
                if (rigid_predicate_cache.count(substitutedPrecondition._usig._name_id) 
                && rigid_predicate_cache[substitutedPrecondition._usig._name_id].count(groundFact)) {
                    if (rigid_predicate_cache[substitutedPrecondition._usig._name_id][groundFact].size() > _new_variable_domain_size_limit) {
                        reachedLimit = true;
                        break;
                    } else if (newRestrictions.size() == 0) {
                        newRestrictions = rigid_predicate_cache[substitutedPrecondition._usig._name_id][groundFact];
                    } else {
                        for (const auto& constant: rigid_predicate_cache[substitutedPrecondition._usig._name_id][groundFact]) {
                            newRestrictions.insert(constant);
                            if (newRestrictions.size() > _new_variable_domain_size_limit) {
                                reachedLimit = true;
                                break;
                            }
                        }
                    }
                    if (reachedLimit) break;
                }
            }
            if (reachedLimit) break;
            if (!freeArgRestrictions.count(substitutedPrecondition._usig._args[argPosition])) {
                freeArgRestrictions[substitutedPrecondition._usig._args[argPosition]] = newRestrictions;
            } else {
                FlatHashSet<int> toDelete;
                for (const auto& constant: freeArgRestrictions[substitutedPrecondition._usig._args[argPosition]]) {
                    if (!newRestrictions.count(constant)) {
                        toDelete;
                    }
                }
                for (const auto& constant: toDelete) {
                    freeArgRestrictions[substitutedPrecondition._usig._args[argPosition]].erase(constant);
                }
            }
            if (freeArgRestrictions[substitutedPrecondition._usig._args[argPosition]].size() > 0) {
                preconditionsToRemove.insert(substitutedPrecondition);
            } else {
                //Log::e("Found no possible constants for variable %s\n", TOSTR(substitutedPrecondition._usig._args[argPosition]));
                _invalid_rigid_preconditions_found++;
                freeArgRestrictions.erase(substitutedPrecondition._usig._args[argPosition]);
                valid = false;
                break;
            }
            if (freeArgRestrictions[substitutedPrecondition._usig._args[argPosition]].size() == 1) {
                globalSub[substitutedPrecondition._usig._args[argPosition]] = *newRestrictions.begin();
                s[substitutedPrecondition._usig._args[argPosition]] = *newRestrictions.begin();
            }
        }
        if (!valid) {
            break;
        }
    }
    if (!valid) return valid;
    //Log::e("Substituted rigid preconditions: %s\n", TOSTR(preconditions));
    for (const auto& precondition: preconditionsToRemove) preconditions.erase(precondition);
    //Log::e("Reduced Substituted rigid preconditions: %s\n", TOSTR(preconditions));
    preconditionsToRemove.clear();

    for (auto& substitutedPrecondition: fluentPreconditions) {
        substitutedPrecondition.apply(s);
        if (substitutedPrecondition._negated) continue;
        //Log::e("Checking fluent precondition %s\n", TOSTR(substitutedPrecondition));
        for (size_t argPosition = 0; argPosition < substitutedPrecondition._usig._args.size(); argPosition++) 
                if (nodeArgs.count(substitutedPrecondition._usig._args[argPosition])) {
            FlatHashSet<int> newRestrictions;
            ArgIterator iter = ArgIterator::getFullInstantiation(substitutedPrecondition._usig, _htn, freeArgRestrictions, true);

            if (iter.size() > _new_variable_domain_size_limit) continue;
            for (const USignature& groundFact : iter) {
                if (countPositiveGround(foundEffectsPositive[groundFact._name_id], groundFact, freeArgRestrictions)) {
                    newRestrictions.insert(groundFact._args[argPosition]);
                    if (newRestrictions.size() > _new_variable_domain_size_limit) {
                        break;
                    }
                }
            }
            if (newRestrictions.size() > _new_variable_domain_size_limit) continue;
            if (!freeArgRestrictions.count(substitutedPrecondition._usig._args[argPosition])) {
                freeArgRestrictions[substitutedPrecondition._usig._args[argPosition]] = newRestrictions;
            } else {
                FlatHashSet<int> toDelete;
                for (const auto& constant: freeArgRestrictions[substitutedPrecondition._usig._args[argPosition]]) {
                    if (!newRestrictions.count(constant)) {
                        toDelete;
                    }
                }
                for (const auto& constant: toDelete) {
                    freeArgRestrictions[substitutedPrecondition._usig._args[argPosition]].erase(constant);
                }
            }
            if (freeArgRestrictions[substitutedPrecondition._usig._args[argPosition]].size() > 0) {
                preconditionsToRemove.insert(substitutedPrecondition);
            } else {
                //Log::e("Found no possible constants for variable %s\n", TOSTR(substitutedPrecondition._usig._args[argPosition]));
                _invalid_fluent_preconditions_found++;
                freeArgRestrictions.erase(substitutedPrecondition._usig._args[argPosition]);
                valid = false;
                break;
            }
            if (freeArgRestrictions[substitutedPrecondition._usig._args[argPosition]].size() == 1) {
                globalSub[substitutedPrecondition._usig._args[argPosition]] = *newRestrictions.begin();
                s[substitutedPrecondition._usig._args[argPosition]] = *newRestrictions.begin();
            }
        }
        if (!valid) {
            break;
        }
    }
    if (!valid) return valid;

    for (const auto& precondition: preconditionsToRemove) fluentPreconditions.erase(precondition);

    return valid;
}

bool FactAnalysis::checkPreconditionValidityRigid(const SigSet& preconditions, NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions) {
    bool preconditionsValid = true;
    // Check if any precondition is rigid and not valid in the initState
    for (const auto& substitutedPrecondition : preconditions) {
        //Log::e("checking rigid precondition: %s\n", TOSTR(substitutedPrecondition));
        bool hasUnboundArg = false;
        std::vector<int> freeArgPositions;
        for (const auto& argPosition: _htn.getFreeArgPositions(substitutedPrecondition._usig._args)) {
            if (substitutedPrecondition._usig._args[argPosition] != _name_id_) {
                freeArgPositions.push_back(argPosition);
            } else {
                hasUnboundArg = true;
            }
        }
        if (_htn.isFullyGround(substitutedPrecondition._usig) && !_htn.hasQConstants(substitutedPrecondition._usig)) {
            //Log::d("Found ground precondition without qconstants: %s\n", TOSTR(substitutedPrecondition));
            preconditionsValid = !substitutedPrecondition._negated != !_init_state.count(substitutedPrecondition._usig);
        } else {
            preconditionsValid = false;
            for (const USignature& groundFact : ArgIterator::getFullInstantiation(substitutedPrecondition._usig, _htn, freeArgRestrictions, true)) {
                //Log::d("Ground fact: %s\n", TOSTR(groundFact));
                if (_init_state.count(groundFact) == !substitutedPrecondition._negated) {
                    preconditionsValid = true;
                    break;
                }
            }
        }
        if (!preconditionsValid) {
            //Log::e("Found invalid rigid precondition: %s\n", TOSTR(substitutedPrecondition));
            _invalid_rigid_preconditions_found++;
            break;
        } else {
            //Log::e("Found valid rigid precondition: %s\n", TOSTR(substitutedPrecondition));
        }
    }
    return preconditionsValid;
}

bool FactAnalysis::checkPreconditionValidityFluent(SigSet& preconditions, NodeHashMap<int, USigSet>& foundEffectsPositive, 
    NodeHashMap<int, USigSet>& foundEffectsNegative, NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions,
    NodeHashMap<int, SigSet>& postconditions) {
    bool preconditionsValid = true;
    for (auto& substitutedPrecondition : preconditions) {
        //Log::e("Checking fluent precondition: %s\n", TOSTR(substitutedPrecondition));
        substitutedPrecondition.negate();
        if (postconditions[substitutedPrecondition._usig._name_id].count(substitutedPrecondition)){
            // Log::e("Found invalid fluent precondition in postconditions: %s\n", TOSTR(substitutedPrecondition));
            // Log::e("postconditions: %s\n", TOSTR(postconditions[substitutedPrecondition._usig._name_id]));
            preconditionsValid = false;
            break;
        }
        substitutedPrecondition.negate();
        //Log::e("checking fluent precondition: %s\n", TOSTR(substitutedPrecondition));
        if (substitutedPrecondition._negated) {
            if (_htn.isFullyGround(substitutedPrecondition._usig) && !_htn.hasQConstants(substitutedPrecondition._usig)) {
                preconditionsValid = countNegativeGround(foundEffectsNegative[substitutedPrecondition._usig._name_id], substitutedPrecondition._usig, freeArgRestrictions) || !_init_state.count(substitutedPrecondition._usig);
            } else {
                preconditionsValid = false;
                for (const USignature& groundFact : ArgIterator::getFullInstantiation(substitutedPrecondition._usig, _htn, freeArgRestrictions, true)) {
                    if (countNegativeGround(foundEffectsNegative[substitutedPrecondition._usig._name_id], groundFact, freeArgRestrictions) || !_init_state.count(groundFact)) {
                        preconditionsValid = true;
                        break;
                    }
                }
            }
        } else {
            preconditionsValid = countPositive(foundEffectsPositive, substitutedPrecondition._usig, freeArgRestrictions);
        }
        if (!preconditionsValid) {
            //Log::e("Found invalid fluent precondition: %s\n", TOSTR(substitutedPrecondition));
            //Log::e("posFacts: %s\n", TOSTR(_pos_layer_facts));
            //Log::e("negFacts: %s\n",  TOSTR(_neg_layer_facts));
            // for (const auto& [predicate, signatures]: foundEffectsPositive) {
            //      Log::e("foundPos: %s\n", TOSTR(signatures));
            // }
            // for (const auto& [predicate, signatures]: foundEffectsPositive) {
            //     Log::e("foundNeg: %s\n", TOSTR(signatures));
            // }
            _invalid_fluent_preconditions_found++;
            break;
        }
    }
    return preconditionsValid;
}

USigSet FactAnalysis::removeDominated(const NodeHashMap<int, USigSet>& originalSignatures) {
    USigSet reducedSignatures;
    for (const auto& [argname, effects]: originalSignatures) {
        USigSet dominatedSignatures;
        for (const auto& eff: effects) {
            if (!dominatedSignatures.count(eff)) {
                for (const auto& innerEff: effects) {
                    if (!dominatedSignatures.count(innerEff) && eff != innerEff) {
                        if (_htn.dominates(innerEff, eff)) {
                            dominatedSignatures.insert(eff);
                            break;
                        } else if (_htn.dominates(eff, innerEff)) {
                            dominatedSignatures.insert(innerEff);
                        }
                    }
                }
                if (!dominatedSignatures.count(eff)) reducedSignatures.insert(eff);
            }
        }
        //Log::e("Dominated signatures: %s\n", TOSTR(dominatedSignatures));
    }
    return reducedSignatures;
}

SigSet FactAnalysis::groundEffects(const NodeHashMap<int, USigSet>& positiveEffects, const NodeHashMap<int, USigSet>& negativeEffects,
    NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions) {
    SigSet result = groundEffects(positiveEffects, false, freeArgRestrictions);
    Sig::unite(groundEffects(negativeEffects, true, freeArgRestrictions), result);
    return result;
}

SigSet FactAnalysis::groundEffects(const NodeHashMap<int, USigSet>& effects, bool negated, NodeHashMap<int, FlatHashSet<int>>& freeArgRestrictions) {
    USigSet effectsToGround = removeDominated(effects);
    SigSet result;

    for (const auto& effect: effectsToGround) {
        //Log::e("Grounding effect: %s\n", TOSTR(effect));
        if (effect._args.empty()) result.emplace(effect, negated);
        else for (const USignature& groundFact : ArgIterator::getFullInstantiation(effect, _htn, freeArgRestrictions)) {
            //Log::e("groundFact: %s\n", TOSTR(groundFact));
            result.emplace(groundFact, negated);
        }
    }
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
