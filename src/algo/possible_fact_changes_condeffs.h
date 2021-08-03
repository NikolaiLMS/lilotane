
#include "algo/fact_analysis.h"
#include "util/log.h"

class PFCCondEffs: public FactAnalysis {
private:
    FactAnalysisPreprocessing _preprocessing;
public:
    PFCCondEffs(HtnInstance& htn): FactAnalysis(htn), _preprocessing(htn, _fact_frames, _util) {

    }

    void computeFactFrames() {
        _preprocessing.computeFactFramesCondEffs();
    }

    SigSet getPossibleFactChanges(const USignature& sig) {
        //Log::d("getPossibleFactChanges for: %s\n", TOSTR(sig));
        FlatHashMap<int, USigSet> effectsPositive;
        FlatHashMap<int, USigSet> effectsNegative;
        SigSet liftedResult;
        SigSet result;
        FactFrame factFrame = _util.getFactFrame(sig);

        // Iterate through all conditionalEffects in factFrame
        for (const auto& conditionalEffect : factFrame.conditionalEffects) {
            //Log::d("checking conditionalEffect with prereqs: %s, and effects: %s\n", TOSTR(conditionalEffect.first), TOSTR(conditionalEffect.second));
            bool reachable = true;

            // Check if any prerequisite of the conditionalEffect is rigid and not reachable in the initState
            for (const auto& prerequisite : conditionalEffect.first) {
                //Log::d("checking conditionalEffect prereqs: %s\n", TOSTR(prerequisite));
                if (_htn.isFullyGround(prerequisite._usig) && !_htn.hasQConstants(prerequisite._usig)) {
                    //Log::d("Found rigid predicate: %s\n", TOSTR(prerequisite));
                    reachable = !prerequisite._negated != !_init_state.count(prerequisite._usig);
                } else {
                    reachable = false;
                    for (const auto& groundFact : ArgIterator::getFullInstantiationQConst(prerequisite._usig, _htn)) {
                        //Log::d("Ground fact: %s\n", TOSTR(groundFact));
                        if (_init_state.count(groundFact) == !prerequisite._negated) {
                            reachable = true;
                            break;
                        }
                    }
                }
                if (!reachable) {
                    //Log::d("Found impossible rigid prereq: %s\n", TOSTR(prerequisite));
                    _invalid_preconditions_found++;
                    break;
                }
            }

            // If any rigid, non-reachable prerequisite is found, don't add the conditionalEffects to the PFC,
            if (!reachable) {
                //Log::d("Not adding the following effects: %s\n", TOSTR(conditionalEffect.second));
                continue;
            }

            for (const auto& fact : conditionalEffect.second) {
                //Log::d("adding conditionalEffect effects: %s\n", TOSTR(fact));
                if (fact._negated) {
                    effectsNegative[fact._usig._name_id].insert(fact._usig);
                } else {
                    effectsPositive[fact._usig._name_id].insert(fact._usig);
                }
            }
        }
        return groundEffects(effectsPositive, effectsNegative);
    }
};