
#ifndef DOMPASCH_TREE_REXX_ENCODING_H
#define DOMPASCH_TREE_REXX_ENCODING_H

extern "C" {
    #include "sat/ipasir.h"
}

#include <initializer_list>
#include <fstream>
#include <string>
#include <iostream>

#include "util/params.h"
#include "data/layer.h"
#include "data/signature.h"
#include "data/htn_instance.h"
#include "data/action.h"
#include "sat/variable_domain.h"

#define PRINT_TO_FILE true

typedef NodeHashMap<int, SigSet> State;

struct PlanItem {
    PlanItem() {
        id = -1;
        abstractTask = Position::NONE_SIG;
        reduction = Position::NONE_SIG;
        subtaskIds = std::vector<int>(0);
    }
    PlanItem(int id, const USignature& abstractTask, const USignature& reduction, const std::vector<int> subtaskIds) :
        id(id), abstractTask(abstractTask), reduction(reduction), subtaskIds(subtaskIds) {}
    int id = -1;
    USignature abstractTask;
    USignature reduction;
    std::vector<int> subtaskIds;
};

class Encoding {

private:
    Parameters& _params;
    HtnInstance& _htn;
    std::vector<Layer*>& _layers;
    
    size_t _layer_idx;
    size_t _pos;
    size_t _old_pos;
    size_t _offset;

    NodeHashMap<USignature, int, USignatureHasher> _substitution_variables;
    NodeHashSet<Substitution, Substitution::Hasher> _forbidden_substitutions;
    FlatHashSet<int> _new_fact_vars;

    void* _solver;
    std::ofstream _out;

    USignature _sig_primitive;
    USignature _sig_substitution;
    int _substitute_name_id;

    FlatHashSet<int> _q_constants;
    FlatHashMap<std::pair<int, int>, int, IntPairHasher> _q_equality_variables;
    std::vector<int> _primitive_ops;
    std::vector<int> _nonprimitive_ops;

    std::vector<int> _last_assumptions;
    std::vector<int> _no_decision_variables;

    const bool _print_formula;
    const bool _use_q_constant_mutexes;
    const bool _implicit_primitiveness;

    int _num_cls;
    int _num_lits;
    int _num_asmpts;

    int STAGE_ACTIONCONSTRAINTS = 0;
    int STAGE_ACTIONEFFECTS = 1;
    int STAGE_ATLEASTONEELEMENT = 2;
    int STAGE_ATMOSTONEELEMENT = 3;
    int STAGE_AXIOMATICOPS = 4;
    int STAGE_EXPANSIONS = 5;
    int STAGE_FACTVARENCODING = 6;
    int STAGE_FORBIDDENPARENTS = 7;
    int STAGE_FRAMEAXIOMS = 8;
    int STAGE_INITSUBSTITUTIONS = 9;
    int STAGE_PREDECESSORS = 10;
    int STAGE_QCONSTEQUALITY = 11;
    int STAGE_QFACTSEMANTICS = 12;
    int STAGE_QTYPECONSTRAINTS = 13;
    int STAGE_REDUCTIONCONSTRAINTS = 14;
    int STAGE_SUBSTITUTIONCONSTRAINTS = 15;
    int STAGE_TRUEFACTS = 16;
    int STAGE_ASSUMPTIONS = 17;
    const char* STAGES_NAMES[18] = {"actionconstraints","actioneffects","atleastoneelement","atmostoneelement",
        "axiomaticops","expansions","factvarencoding","forbiddenparents","frameaxioms","initsubstitutions",
        "predecessors","qconstequality","qfactsemantics","qtypeconstraints","reductionconstraints",
        "substitutionconstraints","truefacts","assumptions"};
    std::map<int, int> _num_cls_per_stage;
    std::vector<int> _current_stages;
    int _num_cls_at_stage_start = 0; 

    float _sat_call_start_time;

public:
    Encoding(Parameters& params, HtnInstance& htn, std::vector<Layer*>& layers);
    ~Encoding();

    void encode(size_t layerIdx, size_t pos);
    void addAssumptions(int layerIdx);
    void setTerminateCallback(void * state, int (*terminate)(void * state));
    int solve();

    float getTimeSinceSatCallStart();

    void begin(int stage);
    void end(int stage);
    void printStages();

    std::pair<std::vector<PlanItem>, std::vector<PlanItem>> extractPlan();
    std::vector<PlanItem> extractClassicalPlan();
    std::vector<PlanItem> extractDecompositionPlan();

    void printFailedVars(Layer& layer);
    void printSatisfyingAssignment();

private:

    void clearDonePositions();

    void encodeFactVariables(Position& pos, const Position& left, Position& above);
    void encodeFrameAxioms(Position& pos, const Position& left);
    void initSubstitutionVars(int opVar, int qconst, Position& pos);

    void setVariablePhases(const std::vector<int>& vars);
    
    std::set<std::set<int>> getCnf(const std::vector<int>& dnf);

    inline void addClause(int lit);
    inline void addClause(int lit1, int lit2);
    inline void addClause(int lit1, int lit2, int lit3);
    inline void addClause(const std::initializer_list<int>& lits);
    inline void addClause(const std::vector<int>& cls);

    inline void appendClause(int lit);
    inline void appendClause(int lit1, int lit2);
    inline void appendClause(const std::initializer_list<int>& lits);
    
    inline void endClause();
    inline void assume(int lit);

    int varPrimitive(int layer, int pos);
    int varSubstitution(const USignature& sigSubst);
    int varQConstEquality(int q1, int q2);
    const USignature& sigSubstitute(int qConstId, int trueConstId);

    bool isEncoded(int layer, int pos, const USignature& sig);
    bool isEncodedSubstitution(const USignature& sig);
    
    inline int getVariable(const Position& pos, const USignature& sig);
    inline int getVariable(int layer, int pos, const USignature& sig);
    inline int encodeVariable(Position& pos, const USignature& sig, bool decisionVar = true);

    std::string varName(int layer, int pos, const USignature& sig);
    void printVar(int layer, int pos, const USignature& sig);

    bool value(int layer, int pos, const USignature& sig);
    USignature getDecodedQOp(int layer, int pos, const USignature& sig);
    
};

#endif