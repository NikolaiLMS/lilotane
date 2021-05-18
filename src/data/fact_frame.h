
#ifndef DOMPASCH_LILOTANE_FACT_FRAME_H
#define DOMPASCH_LILOTANE_FACT_FRAME_H

#include <vector>

#include "data/signature.h"

struct FactFrame {
    NodeHashMap<SigSet, SigSet, SigSetHasher> conditionalEffects;
    USignature sig;
    SigSet preconditions;
    SigSet effects;
    std::vector<SigSet> offsetEffects;

    FactFrame substitute(const Substitution& s) const {
        FactFrame f;
        f.sig = sig.substitute(s);
        for (const auto& pre : preconditions) f.preconditions.insert(pre.substitute(s));
        for (const auto& eff : effects) f.effects.insert(eff.substitute(s));
        f.offsetEffects.resize(offsetEffects.size());
        for (size_t i = 0; i < offsetEffects.size(); i++) 
            for (const auto& eff : offsetEffects[i]) 
                f.offsetEffects[i].insert(eff.substitute(s));
        for (auto& conditionalEffect : conditionalEffects) {
            SigSet new_prereqs;
            SigSet new_effects;
            for (const auto& prereq : conditionalEffect.first) new_prereqs.insert(prereq.substitute(s));
            for (const auto& effect : conditionalEffect.second) new_effects.insert(effect.substitute(s));
            f.conditionalEffects[new_prereqs] = new_effects;
        }
        return f;
    }
};

#endif