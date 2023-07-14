# lean-auto
Experiments in automation for Lean

## Coding Style
* ``Array``/``List``: We only use ``Array``. Functions whose signature contains ``List`` should be declared as ``private``.
* IR: Logic-oriented IR can be found in ```TRanslation/ReifTerm.lean```, and Solver-oriented IR can be found in ```Auto/IR/..```. Each IR should be equipped with its ``TransM``.
* Translation: Translation code from ``A`` to ``B`` should be written in ```Translation/A2B.lean```