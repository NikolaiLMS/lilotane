
#ifndef DOMPASCH_LILOTANE_FACT_FRAME_H
#define DOMPASCH_LILOTANE_FACT_FRAME_H

#include <vector>

#include "data/signature.h"

struct FactFrame {
    NodeHashMap<SigSet, SigSet, SigSetHasher, SigSetEquals> conditionalEffects;
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
            SigSet newPrereqs;
            SigSet newEffects;
            for (const auto& prereq : conditionalEffect.first) newPrereqs.insert(prereq.substitute(s));
            for (const auto& effect : conditionalEffect.second) newEffects.insert(effect.substitute(s));
            Sig::unite(newEffects, f.conditionalEffects[newPrereqs]);
        }
        return f;
    }
};

#endif