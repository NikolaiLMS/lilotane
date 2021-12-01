
#include "algo/fact_analysis.h"
#include "util/log.h"

class PFCBase: public FactAnalysis {
private:
    FactAnalysisPreprocessing _preprocessing;
public:
    PFCBase(HtnInstance& htn, Parameters& params): FactAnalysis(htn, params), _preprocessing(htn, _fact_frames, _util, params, _init_state) {

    }

    void computeFactFrames() {
        _preprocessing.computeFactFramesBase();
    }

    SigSet getPossibleFactChanges(const USignature& sig) {
        SigSet result;
        for (const auto& fact : _util.getFactFrame(sig).effects) {
            if (fact._usig._args.empty()) result.insert(fact);
            else for (const USignature& groundFact : ArgIterator::getFullInstantiation(fact._usig, _htn)) {
                result.emplace(groundFact, fact._negated);
            }
        }
        //Log::d("PFC %s : %s\n", TOSTR(sig), TOSTR(result));
        return result;
    }
};