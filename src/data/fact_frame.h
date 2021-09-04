
#ifndef DOMPASCH_LILOTANE_FACT_FRAME_H
#define DOMPASCH_LILOTANE_FACT_FRAME_H

#include <vector>
#include <algorithm>
#include "data/signature.h"

struct PFCNode {
    USignature sig;
    FlatHashSet<int> subtaskArgs;
    SigSet rigidPreconditions;
    SigSet fluentPreconditions;
    SigSet effects;
    SigSet postconditions;
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
                    for (const auto& arg: cutChild.subtaskArgs) {
                        cutNode.subtaskArgs.insert(arg);
                    }
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
    
        FlatHashSet<int> substitutedSubtaskArgs = subtaskArgs;
        for (const auto& arg: subtaskArgs) {
            auto it = s.find(arg);
            if (it != s.end()) {
                substitutedSubtaskArgs.erase(arg);
                substitutedSubtaskArgs.insert(it->second);
            }
        }
        subtaskArgs = substitutedSubtaskArgs;

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
    FlatHashSet<int> subtaskArgs;
    std::vector<NodeHashMap<std::pair<SigSet, SigSet>, SigSet, SigSetPairHasher, SigSetPairEquals>> conditionalEffects;
    USignature sig;
    SigSet preconditions;
    SigSet effects;
    SigSet postconditions;
    std::vector<SigSet> offsetEffects;
    std::vector<NodeHashMap<int, PFCNode>*> subtasks;
    int maxDepth = 0;
    int numNodes = 1;
    
    FactFrame substitute(const Substitution& s) const {
        FactFrame f;
        f.sig = sig.substitute(s);
        for (const auto& pre : preconditions) f.preconditions.insert(pre.substitute(s));
        for (const auto& eff : effects) f.effects.insert(eff.substitute(s));
        for (const auto& eff : postconditions) f.postconditions.insert(eff.substitute(s));
        f.offsetEffects.resize(offsetEffects.size());
        for (size_t i = 0; i < offsetEffects.size(); i++) 
            for (const auto& eff : offsetEffects[i]) 
                f.offsetEffects[i].insert(eff.substitute(s));
        for (auto& conditionalEffect : conditionalEffects) {
            NodeHashMap<std::pair<SigSet, SigSet>, SigSet, SigSetPairHasher, SigSetPairEquals> newHashMap;
            for (const auto& [preconditions, effects]: conditionalEffect) {
                SigSet newRigidPredicates;
                SigSet newFluentPredicates;
                SigSet newEffects;
                for (const auto& rigidPredicate : preconditions.first) newRigidPredicates.insert(rigidPredicate.substitute(s));
                for (const auto& fluentPredicate : preconditions.second) newFluentPredicates.insert(fluentPredicate.substitute(s));
                for (const auto& effect : effects) newEffects.insert(effect.substitute(s));
                Sig::unite(newEffects, newHashMap[{newRigidPredicates, newFluentPredicates}]);
            }
            f.conditionalEffects.push_back(newHashMap);
        }
        f.subtasks = subtasks;
        return f;
    }
};

#endif