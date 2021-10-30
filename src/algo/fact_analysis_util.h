
#include "util/log.h"

class FactAnalysisUtil {

private:
    HtnInstance& _htn;
    NodeHashMap<int, FactFrame>& _fact_frames;
    NetworkTraversal& _traversal;
    int _num_effects = 0;

public:

    NetworkTraversal& getTraversal() {
        return _traversal;
    }

    FactAnalysisUtil(HtnInstance& htn, NodeHashMap<int, FactFrame>& fact_frames, NetworkTraversal& traversal) : _htn(htn), _fact_frames(fact_frames), _traversal(traversal) {
    }

    FactFrame getFactFrame(const USignature& sig) {
        const FactFrame& f = _fact_frames.at(sig._name_id);
        return f.substitute(Substitution(f.sig._args, sig._args));
    }

    void setNumEffects(int newNum) {
        _num_effects = newNum;
    }

    int getNumEffects() {
        return _num_effects;
    }
};