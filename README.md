# disamb-verification

Supplementary Coq code for proofs related to semantics of disambiguation relations. Created as part of a master thesis.

## Compiling the code

Requires [The Coq Proof Assistant](https://coq.inria.fr/) to be installed, tested on version 8.11.0.
Running the file `compile.sh` compiles everything. Note: This project uses version 1.5.0 of the [coq-std++](https://gitlab.mpi-sws.org/iris/stdpp) library. The `compile.sh` script should automatically clone this repository using Git and then compile that library using the `make` command.

## Files

1. `IGrammar.v` contains all definitions related to *Infix Expression Grammars*.
2. `IGrammarTheorems.v` contains lemmas and theorems related to Infix Expression Grammars. This includes proofs for *safety* and *completeness*.
3. Similarly `IPGrammar.v` and `IPGrammarTheorems.v` are related to expression grammars containing Infix and Prefix productions.
4. `IPPGrammar.v` and `IPPGrammarTheorems.v` also allow Postfix productions.
