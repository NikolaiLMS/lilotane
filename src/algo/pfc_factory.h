
#include "algo/fact_analysis.h"
#include "util/log.h"
#include "algo/possible_fact_changes_base.h"
#include "algo/possible_fact_changes_tree_dfs.h"
#include "memory"

class PFCFactory {
public:
    static std::unique_ptr<FactAnalysis> create(std::string pfcType, HtnInstance& htn, Parameters& params) {
        std::unique_ptr<FactAnalysis> factAnalysis = NULL;
        if (pfcType == "treedfs") {
            factAnalysis = std::make_unique<PFCTreeDFS>(htn, params);
        } else {
            factAnalysis = std::make_unique<PFCBase>(htn, params);
        }

        return factAnalysis;
    }
};