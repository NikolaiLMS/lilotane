
#include "algo/fact_analysis.h"
#include "util/log.h"
#include "algo/possible_fact_changes_base.h"
#include "algo/possible_fact_changes_condeffs.h"
#include "algo/possible_fact_changes_tree.h"
#include "memory"

class PFCFactory {
public:
    static std::unique_ptr<FactAnalysis> create(std::string pfcType, HtnInstance& htn) {
        std::unique_ptr<FactAnalysis> factAnalysis = NULL;
        
        if (pfcType == "condeffs") {
            factAnalysis = std::make_unique<PFCCondEffs>(htn);
        } else if (pfcType == "tree") {
            factAnalysis = std::make_unique<PFCTree>(htn);
        } else {
            factAnalysis = std::make_unique<PFCBase>(htn);
        }

        return factAnalysis;
    }
};