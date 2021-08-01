
#ifndef DOMPASCH_LILOTANE_FACT_FRAME_H
#define DOMPASCH_LILOTANE_FACT_FRAME_H

#include <vector>
#include <algorithm>
#include "data/signature.h"

struct PFCNode {
    USignature sig;
    SigSet rigidPreconditions;
    SigSet fluentPreconditions;
    SigSet effects;
    std::vector<NodeHashMap<int, PFCNode>*> subtasks;
    int maxDepth = 0;
    int numNodes = 1;
    
    PFCNode cutDepth(int depth) const {
        PFCNode cutNode;
        cutNode.sig = sig;
        cutNode.rigidPreconditions = rigidPreconditions;
        cutNode.fluentPreconditions = fluentPreconditions;
        cutNode.effects = effects;
        if (depth > 0) {
            cutNode.subtasks.reserve(subtasks.size());
            for (size_t i = 0; i < subtasks.size(); i++) {
                NodeHashMap<int, PFCNode>* cutSubtask = new NodeHashMap<int, PFCNode>;
                for (const auto& [id, child]: *subtasks[i]) {
                    PFCNode cutChild = child.cutDepth(depth-1);
                    (*cutSubtask)[id] = cutChild;
                    cutNode.maxDepth = cutNode.maxDepth >= cutChild.maxDepth+1 ? cutNode.maxDepth : cutChild.maxDepth+1;
                    cutNode.numNodes += cutChild.numNodes;
                }
                cutNode.subtasks.push_back(cutSubtask);
            }
        }
        return cutNode;
    }

    void normalize(const FlatHashSet<int>& argSet, std::function<Signature(const Signature& sig, FlatHashSet<int> argSet)> normalizeFunction) {
        SigSet normalizedPreconditions;
        for (const auto& precond: rigidPreconditions) {
            normalizedPreconditions.insert(normalizeFunction(precond, argSet));
        }
        rigidPreconditions = normalizedPreconditions;

        normalizedPreconditions = SigSet();
        for (const auto& precond: fluentPreconditions) {
            normalizedPreconditions.insert(normalizeFunction(precond, argSet));
        }
        fluentPreconditions = normalizedPreconditions;

        SigSet normalizedEffects;
        for (const auto& effect: effects) {
            normalizedEffects.insert(normalizeFunction(effect, argSet));
        }
        effects = normalizedEffects;

        for (const auto& subtask: subtasks) {
            std::vector<int> keyVector;
            for (const auto& [id, child]: *subtask) {
                keyVector.push_back(id);
            }
            for (int& id: keyVector) {
                (*subtask)[id].normalize(argSet, normalizeFunction);
            }
        }
    }

    void substitute(const Substitution& s) {
        sig = sig.substitute(s);

        SigSet substitutedPreconditions;
        for (const auto& precond: rigidPreconditions) {
            substitutedPreconditions.insert(precond.substitute(s));
        }
        rigidPreconditions = substitutedPreconditions;

        substitutedPreconditions = SigSet();
        for (const auto& precond: fluentPreconditions) {
            substitutedPreconditions.insert(precond.substitute(s));
        }
        fluentPreconditions = substitutedPreconditions;

        SigSet substitutedEffects;
        for (const auto& effect: effects) {
            substitutedEffects.insert(effect.substitute(s));
        }
        effects = substitutedEffects;

        for (const auto& subtask: subtasks) {
            std::vector<int> keyVector;
            for (const auto& [id, child]: *subtask) {
                keyVector.push_back(id);
            }
            for (int& id: keyVector) {
                (*subtask)[id].substitute(s);
            }
        }
    }
};

struct FactFrame {
    NodeHashMap<SigSet, SigSet, SigSetHasher, SigSetEquals> conditionalEffects;
    USignature sig;
    SigSet preconditions;
    SigSet effects;
    std::vector<SigSet> offsetEffects;
    std::vector<NodeHashMap<int, PFCNode>*> subtasks;
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
        for (auto& conditionalEffect : conditionalEffects) {
            SigSet newPrereqs;
            SigSet newEffects;
            for (const auto& prereq : conditionalEffect.first) newPrereqs.insert(prereq.substitute(s));
            for (const auto& effect : conditionalEffect.second) newEffects.insert(effect.substitute(s));
            Sig::unite(newEffects, f.conditionalEffects[newPrereqs]);
        }
        f.subtasks = subtasks;
        return f;
    }
};

#endif