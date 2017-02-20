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
* Chapter 6: `ModelChecking.v`
* Chapter 7: `OperationalSemantics.v`
* Chapter 8: `AbstractInterpretation.v`
* Chapter 9: `LambdaCalculusAndTypeSoundness.v`
* Chapter 10: `TypesAndMutation.v`
* Chapter 11: `HoareLogic.v`
* Chapter 12: `DeepAndShallowEmbeddings.v`
* Chapter 13: `SeparationLogic.v`
* Chapter 14: `SharedMemory.v`
* Chapter 15: `ConcurrentSeparationLogic.v`
* Chapter 16: `MessagesAndRefinement.v`
