
#ifndef DOMPASCH_LILOTANE_FACT_FRAME_H
#define DOMPASCH_LILOTANE_FACT_FRAME_H

#include <vector>

#include "data/signature.h"

struct PFCNode {
    USignature sig;
    SigSet preconditions;
    SigSet effects;
    std::vector<FlatHashMap<int, PFCNode>> subtasks;
    int maxDepth = 0;
    int numNodes = 1;

    PFCNode normalize(FlatHashSet<int> argSet, std::function<Signature(const Signature& sig, FlatHashSet<int> argSet)> normalizeFunction) const {
        PFCNode normalizedNode;
        for (const auto& precond: preconditions) {
            normalizedNode.preconditions.insert(normalizeFunction(precond, argSet));
        }

        for (const auto& effect: effects) {
            normalizedNode.effects.insert(normalizeFunction(effect, argSet));
        }

        for (const auto& subtask: subtasks) {
            FlatHashMap<int, PFCNode> normalizedChildren;
            for (const auto& child: subtask) {
                normalizedChildren[child.first] = child.second.normalize(argSet, normalizeFunction);
            }
            normalizedNode.subtasks.push_back(normalizedChildren);
        }
        return normalizedNode;
    }

    PFCNode substitute(const Substitution& s) const {
        PFCNode substitutedNode;
        for (const auto& pre : preconditions) substitutedNode.preconditions.insert(pre.substitute(s));
        for (const auto& eff : effects) substitutedNode.effects.insert(eff.substitute(s));
        for (const auto& subtask: subtasks) {
            FlatHashMap<int, PFCNode> substitutedChildren;
            for (const auto& child: subtask) {
                substitutedChildren[child.first] = child.second.substitute(s);
            }
            substitutedNode.subtasks.push_back(substitutedChildren);
        }
        return substitutedNode;
    }
};

struct FactFrame {
    NodeHashMap<SigSet, SigSet, SigSetHasher, SigSetEquals> conditionalEffects;
    USignature sig;
    SigSet preconditions;
    SigSet effects;
    std::vector<SigSet> offsetEffects;
    std::vector<FlatHashMap<int, PFCNode>> subtasks;
    int maxDepth = 0;
    int numNodes = 1;
    
    FactFrame substitute(const Substitution& s) const {
        FactFrame f;
        f.sig = sig.substitute(s);
        for (const auto& pre : preconditions) f.preconditions.insert(pre.substitute(s));
        for (const auto& eff : effects) f.effects.insert(eff.substitute(s));
        f.offsetEffects.resize(offsetEffects.size());
        for (size_t i = 0; i < offsetEffects.size(); i++) 
            for (const auto& eff : offsetEffects[i]) 
                f.offsetEffects[i].insert(eff.substitute(s));
        return f;
        f.subtasks.resize(subtasks.size());
        for (size_t i = 0; i < subtasks.size(); i++) {
            for (auto& child: subtasks[i]) {
                f.subtasks[i][child.first] = child.second.substitute(s);
            }
        }
    }
};

#endif