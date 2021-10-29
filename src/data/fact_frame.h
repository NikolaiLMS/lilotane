
#ifndef DOMPASCH_LILOTANE_FACT_FRAME_H
#define DOMPASCH_LILOTANE_FACT_FRAME_H

#include <vector>
#include <algorithm>
#include "data/signature.h"

struct PFCNode {
    Substitution substitution;
    USignature sig;
    std::vector<NodeHashMap<int, PFCNode>*> subtasks;
    FlatHashSet<int> newArgs;
    int numDirectChildren = 0;
    void substitute(const Substitution& s) {
        sig = sig.substitute(s);
    }
};

struct FactFrame {
    FlatHashSet<int> subtaskArgs;
    USignature sig;
    SigSet preconditions;
    SigSet rigidPreconditions;
    SigSet fluentPreconditions;
    SigSet effects;
    SigSet negatedPostconditions;
    SigSet postconditions;
    std::vector<SigSet> offsetEffects;
    std::vector<NodeHashMap<int, PFCNode>*> subtasks;
    int maxDepth = 0;
    int numNodes = 1;
    int numDirectChildren = 0;

    FactFrame substitute(const Substitution& s) const {
        FactFrame f;
        f.sig = sig.substitute(s);
        for (const auto& pre : preconditions) f.preconditions.insert(pre.substitute(s));
        for (const auto& eff : effects) f.effects.insert(eff.substitute(s));
        for (const auto& eff : postconditions) f.postconditions.insert(eff.substitute(s));
        for (const auto& eff : negatedPostconditions) f.negatedPostconditions.insert(eff.substitute(s));
        f.offsetEffects.resize(offsetEffects.size());
        for (size_t i = 0; i < offsetEffects.size(); i++) 
            for (const auto& eff : offsetEffects[i]) 
                f.offsetEffects[i].insert(eff.substitute(s));
        f.subtasks = subtasks;
        return f;
    }
};

#endif