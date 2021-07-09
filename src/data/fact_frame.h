
#ifndef DOMPASCH_LILOTANE_FACT_FRAME_H
#define DOMPASCH_LILOTANE_FACT_FRAME_H

#include <vector>
#include <algorithm>
#include "data/signature.h"

struct PFCNode {
    USignature sig;
    SigSet preconditions;
    SigSet effects;
    std::vector<NodeHashMap<int, PFCNode>*> subtasks;
    int maxDepth = 0;
    int numNodes = 1;
    
    PFCNode cutDepth(int depth) const {
        PFCNode cutNode;
        cutNode.sig = sig;
        cutNode.preconditions = preconditions;
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

    PFCNode normalizeConst(const FlatHashSet<int>& argSet, std::function<Signature(const Signature& sig, FlatHashSet<int> argSet)> normalizeFunction) const {
        PFCNode normalizedNode;
        normalizedNode.maxDepth = maxDepth;
        normalizedNode.numNodes = numNodes;
        normalizedNode.sig = sig;

        for (const auto& precond: preconditions) {
            normalizedNode.preconditions.insert(normalizeFunction(precond, argSet));
        }

        for (const auto& effect: effects) {
            normalizedNode.effects.insert(normalizeFunction(effect, argSet));
        }

        for (const auto& subtask: subtasks) {
            NodeHashMap<int, PFCNode>* newSubtask = new NodeHashMap<int, PFCNode>;
            for (const auto& [id, child]: *subtask) {
                PFCNode newChild = child.normalizeConst(argSet, normalizeFunction); 
                (*newSubtask)[id] = newChild;
            }
            normalizedNode.subtasks.push_back(newSubtask);
        }
        return normalizedNode;
    }

    PFCNode substituteConst(const Substitution& s) const {
        PFCNode substitutedNode;
        substitutedNode.maxDepth = maxDepth;
        substitutedNode.numNodes = numNodes;
        substitutedNode.sig = sig.substitute(s);

        for (const auto& precond: preconditions) {
            substitutedNode.preconditions.insert(precond.substitute(s));
        }

        for (const auto& effect: effects) {
            substitutedNode.effects.insert(effect.substitute(s));
        }

        for (const auto& subtask: subtasks) {
            NodeHashMap<int, PFCNode>* newSubtask = new NodeHashMap<int, PFCNode>;
            for (const auto& [id, child]: *subtask) {
                PFCNode newChild = child.substituteConst(s); 
                (*newSubtask)[id] = newChild;
            }
            substitutedNode.subtasks.push_back(newSubtask);
        }
        return substitutedNode;
    }

    void normalize(const FlatHashSet<int>& argSet, std::function<Signature(const Signature& sig, FlatHashSet<int> argSet)> normalizeFunction) {
        SigSet normalizedPreconditions;
        for (const auto& precond: preconditions) {
            normalizedPreconditions.insert(normalizeFunction(precond, argSet));
        }
        preconditions = normalizedPreconditions;

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
        for (const auto& precond: preconditions) {
            substitutedPreconditions.insert(precond.substitute(s));
        }
        preconditions = substitutedPreconditions;

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
        f.subtasks = subtasks;
        return f;
    }
};

#endif