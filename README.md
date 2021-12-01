# Pruning Techniques for Lifted SAT-Based Hierarchical Planning

This project is a fork of Lilotane (https://github.com/domschrei/lilotane) and represents the practical contribution of the Master's Thesis "Hierarchical Task Network Planning
Using SAT Techniques" (see Thesis.pdf).

Our experimental data can be found at https://github.com/NikolaiLMS/mastersthesis-experimental-data.

## Abstract

The very universal and generic problem of automated planning deals with nding sequences
of actions to be executed by autonomous agents to achieve certain goals. Automated
planning is applied in many elds that benet from autonomous decision making and
plan nding. In recent years, hierarchical planning formalized by HTN (Hierarchical Task
Network) planning has become a more popular approach for automated planning, which can
be used to create planning problems with a hierarchical structure using expert knowledge.
A recently popularized approach to solving HTN planning problems is SAT-based HTN
planning, where an increasing portion of an HTN planning problem is encoded into a
SAT formula, the SAT formula is solved by a SAT solver, and the resulting solution to the
SAT formula is decoded back into a solution for the planning problem. Most SAT-based
HTN planners use a grounding step as part of their algorithm which can introduce an
exponential overhead. However a recently introduced lifted SAT-based HTN planner called
Lilotane skips this grounding step and operates on lifted (parametrized) tasks and methods
instead of a at representation. While this approach is often benecial regarding runtimes,
the techniques for reducing the size of the encoding as used by ground SAT-based HTN
planners are not trivially transferable to Lilotane. Hence, in this thesis we introduce
pruning techniques for lifted SAT-based HTN planning in Lilotane that replace the existing
techniques with more sophisticated algorithms and invest additional work before the
encoding step to reduce the size of the resulting SAT formula. Our main approach is a
more sophisticated reachability analysis consisting of a look-ahead traversal of the HTN
hierarchy during runtime as well as procedures to infer postconditions. An evaluation of
our approach using the benchmarks from the IPC 2020 shows that it improves the overall
performance of Lilotane. On some domains of the benchmark set, our approach achieves a
pruning in the number of clauses in the SAT formula of up to two orders of magnitude and
runtime improvements of up to one order of magnitude. When comparing our approach
to other state-of-the-art TOHTN planners, it improves on Lilotane’s advantage in terms
of performance to previously beaten planners and makes Lilotane the best performing
planner on seven to previously only ve out of 24 domains.
