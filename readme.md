# Comparing shapes of randomly generated binary search trees without balancing

This repository contains the code for a research project, regarding the balancedness of a random tree, as part of a course of the University of Utrecht.

## Abstract
When binary search trees are generated from an uniformly shuffled list of numbers using only random inserts they become balanced. Interestingly enough not much is known about also performing random deletions. Using several different methods of generating binary search trees, such as for every random insertion also performing a random deletion, we can deduce if such trees end up balanced. This would mean that trees generated by random inputs and deletes do not necessarily need a balancing algorithm. By comparing the results of these different methods our research concludes that most trees likely become balanced, our research is however limited by the amount of nodes we can realistically add or remove.

## How to run
- Install the Haskell platform
- Build using GHC: `ghc trees.hs -threaded -rtsopts`
- Run: `time ./trees +RTS -N4 -M7G`. The last number specifies the maximum heap size, set this depending on the amount of RAM on your computer.