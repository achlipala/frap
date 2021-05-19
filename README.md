# Formal Reasoning About Programs

This is an in-progress, open-source book by [Adam Chlipala](http://adam.chlipala.net/) simultaneously introducing [the Coq proof assistant](http://coq.inria.fr/) and techniques for proving correctness of programs.  That is, the game is doing completely rigorous, machine-checked mathematical proofs, showing that programs meet their specifications.

Just run `make` here to build everything, including the book `frap_book.pdf` and the accompanying Coq source modules.  Alternatively, run `make lib` to build just the book library, not the chapter example files or PDF.

# Code associated with the different chapters

The main narrative, also present in the book PDF, presents standard program-proof ideas, without rigorous proofs.  Matching Coq files here show how to make it rigorous.  Interleaved with that narrative, there are also other lectures' worth of material, for building up more practical background on Coq itself.  That secondary track appears in this list, too, at a higher level of indentation.

* Chapter 2: `BasicSyntax.v`
  * `Polymorphism.v`: polymorphism and generic data structures
* Chapter 3: `DataAbstraction.v`
* Chapter 4: `Interpreters.v`
  * `FirstClassFunctions.v`: functions as data; continuations and continuation-passing style
* Chapter 5: `RuleInduction.v`
* Chapter 6: `TransitionSystems.v`
  * `IntroToProofScripting.v`: writing scripts to find proofs in Coq
* Chapter 7: `ModelChecking.v`
  * `ProofByReflection.v`: writing verified proof procedures in Coq
* Chapter 8: `OperationalSemantics.v`
  * `LogicProgramming.v`: 'eauto' and friends, to automate proofs via logic programming
* Chapter 9: `AbstractInterpretation.v`
* Chapter 10: `CompilerCorrectness.v`
* Chapter 11: `LambdaCalculusAndTypeSoundness.v`
* Chapter 12: `EvaluationContexts.v`
* Chapter 13: `TypesAndMutation.v`
* Chapter 14: `HoareLogic.v`
* Chapter 15: `DeepAndShallowEmbeddings.v`
* Chapter 16: `SeparationLogic.v`
* Chapter 17: `Connecting.v`
* Chapter 18: `ProgramDerivation.v`
* Chapter 19: `SharedMemory.v`
* Chapter 20: `ConcurrentSeparationLogic.v`
* Chapter 21: `MessagesAndRefinement.v`
* Chapter 22: `SessionTypes.v`

There are also two supplementary files that are independent of the main narrative, for introducing programming with dependent types, a distinctive Coq feature that we neither use nor recommend for the problem sets, but which many students find interesting (and useful in other contexts).
* `SubsetTypes.v`: a first introduction to dependent types by attaching predicates to normal types (used after `CompilerCorrectness.v` in the last course offering)
* `DependentInductiveTypes.v`: building type dependency into datatype definitions (used after `LambdaCalculusAndTypeSoundness.v` in the last course offering)
