#include "fact_analysis.h"
#include "util/log.h"


void FactAnalysis::computeFactFrames() {}
SigSet FactAnalysis::getPossibleFactChanges(const USignature& sig) {}

void FactAnalysis::substituteEffectsAndAdd(const SigSet& effects, Substitution& s, FlatHashMap<int, USigSet>& positiveEffects,
     FlatHashMap<int, USigSet>& negativeEffects) {
    SigSet subtitutedEffects;
    for (const auto& effect: effects) {
        subtitutedEffects.insert(effect.substitute(s));
    }
    for (const auto& eff: subtitutedEffects) {
        if (eff._negated) {
            negativeEffects[eff._usig._name_id].insert(eff._usig);
        } else {
            positiveEffects[eff._usig._name_id].insert(eff._usig);
        }
    }
}

bool FactAnalysis::checkPreconditionValidityRigid(SigSet& substitutedPreconditions) {
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
                Log::d("Ground fact: %s\n", TOSTR(groundFact));
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
    return preconditionsValid;
}

bool FactAnalysis::checkPreconditionValidityFluent(SigSet& substitutedPreconditions, USigSet& foundEffectsPositive, USigSet& foundEffectsNegative) {
    bool preconditionsValid = true;
    // Check if any precondition is rigid and not valid in the initState
    for (const auto& precondition : substitutedPreconditions) {
        //Log::d("checking precondition: %s\n", TOSTR(precondition));
        if (_htn.isFullyGround(precondition._usig) && !_htn.hasQConstants(precondition._usig)) {
            //Log::d("Found ground precondition without qconstants: %s\n", TOSTR(precondition));
            if (!isReachable(precondition)) {
                if (precondition._negated) {
                    preconditionsValid = foundEffectsNegative.count(precondition._usig) || !foundEffectsPositive.count(precondition._usig);
                } else {
                    preconditionsValid = foundEffectsPositive.count(precondition._usig);
                }
            }
        } else {
            preconditionsValid = false;
            for (const USignature& groundFact : ArgIterator::getFullInstantiationQConst(precondition._usig, _htn)) {
                if (!isReachable(groundFact, precondition._negated)) {
                    if (precondition._negated) {
                        preconditionsValid = foundEffectsNegative.count(groundFact) || !foundEffectsPositive.count(groundFact);
                    } else {
                        preconditionsValid = foundEffectsPositive.count(groundFact);
                    }
                } else {
                    preconditionsValid = true;
                }
                if (preconditionsValid) break;
            }
        }
        if (!preconditionsValid) {
            //Log::e("Found invalid rigid precondition: %s\n", TOSTR(precondition));
            _invalid_preconditions_found++;
            break;
        }
    }
    return preconditionsValid;
}

USigSet FactAnalysis::removeDominated(const FlatHashMap<int, USigSet>& originalSignatures) {
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
    }
    return reducedSignatures;
}

SigSet FactAnalysis::groundEffects(const FlatHashMap<int, USigSet>& positiveEffects, const FlatHashMap<int, USigSet>& negativeEffects) {
    USigSet positiveEffectsToGround = removeDominated(positiveEffects);
    USigSet negativeEffectsToGround = removeDominated(negativeEffects);
    SigSet groundEffects;

    for (const auto& positiveEffect: positiveEffectsToGround) {
        for (const USignature& groundFact : ArgIterator::getFullInstantiation(positiveEffect, _htn)) {
            groundEffects.emplace(groundFact, false);
        }
    }
    for (const auto& negativeEffect: negativeEffectsToGround) {
        for (const USignature& groundFact : ArgIterator::getFullInstantiation(negativeEffect, _htn)) {
            groundEffects.emplace(groundFact, true);
        }
    }
    return groundEffects;
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