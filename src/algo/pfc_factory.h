
#include "algo/fact_analysis.h"
#include "util/log.h"
#include "algo/possible_fact_changes_base.h"
#include "algo/possible_fact_changes_condeffs.h"
#include "algo/possible_fact_changes_tree.h"
#include "memory"

class PFCFactory {
public:
    static std::unique_ptr<FactAnalysis> create(std::string pfcType, HtnInstance& htn, Parameters& params) {
        std::unique_ptr<FactAnalysis> factAnalysis = NULL;
        
        if (pfcType == "condeffs") {
            factAnalysis = std::make_unique<PFCCondEffs>(htn, params);
        } else if (pfcType == "tree") {
            factAnalysis = std::make_unique<PFCTree>(htn, params);
        } else {
            factAnalysis = std::make_unique<PFCBase>(htn, params);
        }

        return factAnalysis;
    }
};