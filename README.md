# Formal Reasoning About Programs

This is an in-progress, open-source book by [Adam Chlipala](http://adam.chlipala.net/) simultaneously introducing [the Coq proof assistant](http://coq.inria.fr/) and techniques for proving correctness of programs.  That is, the game is doing completely rigorous, machine-checked mathematical proofs, showing that programs meet their specifications.

Just run `make` here to build everything, including the book `frap_book.pdf` and the accompanying Coq source modules.  Alternatively, run `make lib' to build just the book library, not the chapter example files or PDF.

# Code associated with the different chapters

The main narrative, also present in the book PDF, presents standard program-proof ideas, without rigorous proofs.  Matching Coq files here show how to make it rigorous.  Interleaved with that narrative, there are also other lectures' worth of material, for building up more practical background on Coq itself.  That secondary track appears in this list, too, at a higher level of indentation.

* Chapter 2: `BasicSyntax.v`
  * `Polymorphism.v`: polymorphism and generic data structures
* Chapter 3: `DataAbstraction.v`
* Chapter 4: `Interpreters.v`
* Chapter 5: `TransitionSystems.v`
  * `IntroToProofScripting.v`: writing scripts to find proofs in Coq
* Chapter 6: `ModelChecking.v`
  * `ProofByReflection.v`: writing verified proof procedures in Coq
* Chapter 7: `OperationalSemantics.v`
  * `LogicProgramming.v`: 'eauto' and friends, to automate proofs via logic programming
* Chapter 8: `AbstractInterpretation.v`
* Chapter 9: `CompilerCorrectness.v`
* Chapter 10: `LambdaCalculusAndTypeSoundness.v`
* Chapter 11: `TypesAndMutation.v`
* Chapter 12: `HoareLogic.v`
* Chapter 13: `DeepAndShallowEmbeddings.v`
* Chapter 14: `SeparationLogic.v`
* Chapter 15: `SharedMemory.v`
* Chapter 16: `ConcurrentSeparationLogic.v`
* Chapter 17: `MessagesAndRefinement.v`

There are also two supplementary files that are independent of the main narrative, for introducing programming with dependent types, a distinctive Coq feature that we neither use nor recommend for the problem sets, but which many students find interesting (and useful in other contexts).
* `SubsetTypes.v`: a first introduction to dependent types by attaching predicates to normal types (used after `CompilerCorrectness.v` in the last course offering)
* `DependentInductiveTypes.v`: building type dependency into datatype definitions (used after `LambdaCalculusAndTypeSoundness.v` in the last course offering)
