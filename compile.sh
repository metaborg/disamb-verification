echo COMPILING COQ FILES
coqc InfixGrammar.v
coqc PosTree.v
coqc Reordering.v
coqc MyUtils.v
coqc PosTreeTheorems.v
coqc ReorderingTheorems.v
coqc Lib/StrongInduction.v
coqc GloballyFiniteReorderings.v
read -p FINISHED
