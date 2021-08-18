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

bool FactAnalysis::checkPreconditionValidityRigid(const SigSet& preconditions, Substitution& s) {
    bool preconditionsValid = true;
    // Check if any precondition is rigid and not valid in the initState
    for (const auto& precondition : preconditions) {
        //Log::d("checking precondition: %s\n", TOSTR(precondition));
        Signature substitutedPrecondition = precondition.substitute(s);
        if (_htn.isFullyGround(substitutedPrecondition._usig) && !_htn.hasQConstants(substitutedPrecondition._usig)) {
            //Log::d("Found ground precondition without qconstants: %s\n", TOSTR(substitutedPrecondition));
            preconditionsValid = !substitutedPrecondition._negated != !_init_state.count(substitutedPrecondition._usig);
        } else {
            preconditionsValid = false;
            for (const USignature& groundFact : ArgIterator::getFullInstantiationQConst(substitutedPrecondition._usig, _htn)) {
                //Log::d("Ground fact: %s\n", TOSTR(groundFact));
                if (_init_state.count(groundFact) == !substitutedPrecondition._negated) {
                    preconditionsValid = true;
                    break;
                }
            }
        }
        if (!preconditionsValid) {
            //Log::e("Found invalid rigid precondition: %s\n", TOSTR(precondition));
            _invalid_rigid_preconditions_found++;
            break;
        }
    }
    return preconditionsValid;
}

bool FactAnalysis::checkPreconditionValidityFluent(const SigSet& preconditions, std::vector<USigSet*>& foundEffectsPositive, 
        std::vector<USigSet*>& foundEffectsNegative, Substitution& s) {
    bool preconditionsValid = true;
    for (const auto& precondition : preconditions) {
        //Log::d("checking precondition: %s\n", TOSTR(precondition));
        Signature substitutedPrecondition = precondition.substitute(s);
        if (_htn.isFullyGround(substitutedPrecondition._usig) && !_htn.hasQConstants(substitutedPrecondition._usig)) {
            //Log::d("Found ground precondition without qconstants: %s\n", TOSTR(substitutedPrecondition));
            if (substitutedPrecondition._negated) {
                preconditionsValid = countNegative(foundEffectsNegative, substitutedPrecondition._usig) || !countPositive(foundEffectsPositive, substitutedPrecondition._usig);
            } else {
                preconditionsValid = countPositive(foundEffectsPositive, substitutedPrecondition._usig);
            }
        } else {
            preconditionsValid = false;
            for (const USignature& groundFact : ArgIterator::getFullInstantiationQConst(substitutedPrecondition._usig, _htn)) {
                //Log::e("groundFact: %s\n", TOSTR(groundFact));
                if (substitutedPrecondition._negated) {
                    preconditionsValid = countNegative(foundEffectsNegative, groundFact) || !countPositive(foundEffectsPositive, groundFact);
                } else {
                    preconditionsValid = countPositive(foundEffectsPositive, groundFact);
                }
                if (preconditionsValid) break;
            }
        }
        if (!preconditionsValid) {
            // Log::e("Found invalid fluent precondition: %s\n", TOSTR(substitutedPrecondition));
            // Log::e("posFacts: %s\n", TOSTR(_pos_layer_facts));
            // Log::e("negFacts: %s\n",  TOSTR(_neg_layer_facts));
            // Log::e("foundPos: %s\n", TOSTR(foundEffectsPositive));
            // Log::e("foundNeg: %s\n", TOSTR(foundEffectsNegative));
            _invalid_fluent_preconditions_found++;
            break;
        }
    }
    return preconditionsValid;
}

bool FactAnalysis::checkPreconditionValidityFluent(const SigSet& preconditions, USigSet& foundEffectsPositive, USigSet& foundEffectsNegative, Substitution& s) {
    bool preconditionsValid = true;
    for (const auto& precondition : preconditions) {
        //Log::d("checking precondition: %s\n", TOSTR(precondition));
        Signature substitutedPrecondition = precondition.substitute(s);
        if (_htn.isFullyGround(substitutedPrecondition._usig) && !_htn.hasQConstants(substitutedPrecondition._usig)) {
            //Log::d("Found ground precondition without qconstants: %s\n", TOSTR(substitutedPrecondition));
            if (substitutedPrecondition._negated) {
                preconditionsValid = (_neg_layer_facts.count(substitutedPrecondition._usig) || foundEffectsNegative.count(substitutedPrecondition._usig)) || !(_pos_layer_facts.count(substitutedPrecondition._usig) || foundEffectsPositive.count(substitutedPrecondition._usig));
            } else {
                preconditionsValid = (_pos_layer_facts.count(substitutedPrecondition._usig) || foundEffectsPositive.count(substitutedPrecondition._usig));
            }
        } else {
            preconditionsValid = false;
            for (const USignature& groundFact : ArgIterator::getFullInstantiationQConst(substitutedPrecondition._usig, _htn)) {
                //Log::e("groundFact: %s\n", TOSTR(groundFact));
                if (substitutedPrecondition._negated) {
                    preconditionsValid = (_neg_layer_facts.count(groundFact) || foundEffectsNegative.count(groundFact)) || !(_pos_layer_facts.count(groundFact) || foundEffectsPositive.count(groundFact));
                } else {
                    if (_pos_layer_facts.count(substitutedPrecondition._usig)) Log::e("Found groundfact%s in posFacts\n", TOSTR(groundFact));
                    preconditionsValid = (_pos_layer_facts.count(groundFact) || foundEffectsPositive.count(groundFact));
                }
                if (preconditionsValid) break;
            }
        }
        if (!preconditionsValid) {
            // Log::e("Found invalid fluent precondition: %s\n", TOSTR(substitutedPrecondition));
            // Log::e("posFacts: %s\n", TOSTR(_pos_layer_facts));
            // Log::e("negFacts: %s\n",  TOSTR(_neg_layer_facts));
            // Log::e("foundPos: %s\n", TOSTR(foundEffectsPositive));
            // Log::e("foundNeg: %s\n", TOSTR(foundEffectsNegative));
            _invalid_fluent_preconditions_found++;
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


void FactAnalysis::groundEffectsQConstIntoTarget(const FlatHashMap<int, USigSet>& effects, USigSet* target) {
    USigSet effectsToGround = removeDominated(effects);

    for (const auto& effect: effectsToGround) {
        //Log::e("Grounding effect: %s\n", TOSTR(effect));
        if (effect._args.empty()) (*target).emplace(effect);
        else for (const USignature& groundFact : ArgIterator::getFullInstantiationQConst(effect, _htn)) {
            (*target).emplace(groundFact);
        }
    }
}


SigSet FactAnalysis::groundEffectsQConst(const FlatHashMap<int, USigSet>& positiveEffects, const FlatHashMap<int, USigSet>& negativeEffects) {
    SigSet result = groundEffectsQConst(positiveEffects, false);
    Sig::unite(groundEffectsQConst(negativeEffects, true), result);
    return result;
}

SigSet FactAnalysis::groundEffectsQConst(const FlatHashMap<int, USigSet>& effects, bool negated) {
    USigSet effectsToGround = removeDominated(effects);
    SigSet result;

    for (const auto& effect: effectsToGround) {
        if (effect._args.empty()) result.emplace(effect, negated);
        else for (const USignature& groundFact : ArgIterator::getFullInstantiationQConst(effect, _htn)) {
            result.emplace(groundFact, negated);
        }
    }

    return result;
}

USigSet FactAnalysis::groundEffectsQConst(const FlatHashMap<int, USigSet>& effects) {
    USigSet effectsToGround = removeDominated(effects);
    USigSet result;

    for (const auto& effect: effectsToGround) {
        //Log::e("Grounding effect: %s\n", TOSTR(effect));
        if (effect._args.empty()) result.emplace(effect);
        else for (const USignature& groundFact : ArgIterator::getFullInstantiationQConst(effect, _htn)) {
            result.emplace(groundFact);
        }
    }

    return result;
}

SigSet FactAnalysis::groundEffects(const FlatHashMap<int, USigSet>& positiveEffects, const FlatHashMap<int, USigSet>& negativeEffects) {
    SigSet result = groundEffects(positiveEffects, false);
    Sig::unite(groundEffects(negativeEffects, true), result);
    return result;
}

SigSet FactAnalysis::groundEffects(const FlatHashMap<int, USigSet>& effects, bool negated) {
    USigSet effectsToGround = removeDominated(effects);
    SigSet result;

    for (const auto& effect: effectsToGround) {
        if (effect._args.empty()) result.emplace(effect, negated);
        else for (const USignature& groundFact : ArgIterator::getFullInstantiation(effect, _htn)) {
            result.emplace(groundFact, negated);
        }
    }

    return result;
}

USigSet FactAnalysis::groundEffects(const FlatHashMap<int, USigSet>& effects) {
    USigSet effectsToGround = removeDominated(effects);
    USigSet result;

    for (const auto& effect: effectsToGround) {
        if (effect._args.empty()) result.emplace(effect);
        else for (const USignature& groundFact : ArgIterator::getFullInstantiation(effect, _htn)) {
            result.emplace(groundFact);
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
