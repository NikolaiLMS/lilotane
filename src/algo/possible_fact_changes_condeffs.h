
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
        //Log::e("getPossibleFactChanges for: %s\n", TOSTR(sig));
        FlatHashMap<int, USigSet> effectsPositive;
        FlatHashMap<int, USigSet> effectsNegative;
        FactFrame& factFrame = _fact_frames.at(sig._name_id);
        Substitution s = Substitution(factFrame.sig._args, sig._args);

        for (const auto& conditionalEffectSubtask: factFrame.conditionalEffects) {
            bool subtaskValid = false;
            // Iterate through all conditionalEffects in factFrame
            for (const auto& conditionalEffect : conditionalEffectSubtask) {
                //Log::d("checking conditionalEffect with prereqs: %s, and effects: %s\n", TOSTR(conditionalEffect.first), TOSTR(conditionalEffect.second));
                bool reachable = checkPreconditionValidityRigid(conditionalEffect.first.first, s);

                // If any rigid, non-reachable prerequisite is found, don't add the conditionalEffects to the PFC,
                if (reachable) {
                    subtaskValid = true;
                    substituteEffectsAndAdd(conditionalEffect.second, s, effectsPositive, effectsNegative);
                }
            }
            if (!subtaskValid) {
                _invalid_subtasks_found++;
                throw std::invalid_argument("getPFC: Operator has subtask with no valid children\n");
            } 
        }
        return groundEffects(effectsPositive, effectsNegative);
    }
};