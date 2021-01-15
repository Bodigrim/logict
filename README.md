# logict [![Build Status](https://github.com/Bodigrim/logict/workflows/Haskell-CI/badge.svg)](https://github.com/Bodigrim/logict/actions?query=workflow%3AHaskell-CI) [![Hackage](http://img.shields.io/hackage/v/logict.svg)](https://hackage.haskell.org/package/logict) [![Stackage LTS](http://stackage.org/package/logict/badge/lts)](http://stackage.org/lts/package/logict) [![Stackage Nightly](http://stackage.org/package/logict/badge/nightly)](http://stackage.org/nightly/package/logict)

Provides support for logic-based evaluation.  Logic-based programming
uses a technique known as backtracking to consider alternative values
as solutions to logic statements, and is exemplified by languages
such as [Prolog](https://wikipedia.org/wiki/Prolog) and
[Datalog](https://wikipedia.org/wiki/Datalog).

Logic-based programming replaces explicit iteration and sequencing
code with implicit functionality that internally "iterates" (via
backtracking) over a set of possible values that satisfy explicitly
provided conditions.

This package adds support for logic-based programming in Haskell using
the continuation-based techniques adapted from the paper
[Backtracking, Interleaving, and Terminating Monad Transformers](http://okmij.org/ftp/papers/LogicT.pdf)
by Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry.
This paper extends previous research into using `MonadPlus`
functionality—where `mplus` is used to specify value alternatives
for consideration and `mzero` use used to specify the lack of any
acceptable values—to add support for fairness and pruning using a
set of operations defined by a new `MonadLogic` class.

# Background

In a typical example for Prolog logic programming, there are a set of
facts (expressed as unconditional statements):

```prolog
parent(sarah, john).
parent(arnold, john).
parent(john, anne).
```

and a set of rules that apply if their conditions (body clause) are satisfied:

```prolog
grandparent(Person, Grandchild) :- parent(Person, X), parent(X, Grandchild).
```

Execution of a query for this rule `grandparent(G, anne)` would result in the following "values":

```prolog
grandparent(sarah, anne).
grandparent(arnold, anne).
```

For this query execution, `Person` and `X` are "free" variables where
`Grandchild` has been fixed to `anne`. The Prolog engine internally
"backtracks" to the `parent(Person, X)` statement to try different
known values for each variable, executing forward to see if the values
satisfy all the results and produce a resulting value.

# Haskell logict Package

The Haskell equivalent for the example above, using the `logict` package
might look something like the following:

```haskell
import Control.Applicative
import Control.Monad.Logic

parents :: [ (String, String) ]
parents = [ ("Sarah",  "John")
          , ("Arnold", "John")
          , ("John",   "Anne")
          ]

grandparent :: String -> Logic String
grandparent grandchild = do (p, c) <- choose parents
                            (c', g) <- choose parents
                            guard (c == c')
                            guard (g == grandchild)
                            pure p

choose = foldr ((<|>) . pure) empty

main = do let grandparents = observeAll (grandparent "Anne")
          putStrLn $ "Anne's grandparents are: " <> show grandparents
```

In this simple example, each of the `choose` calls acts as a
backtracking choice point where different entries of the `parents`
array will be generated.  This backtracking is handled automatically
by the `MonadLogic` instance for `Logic` and does not need to be
explicitly written into the code.  The `observeAll` function collects
all the values "produced" by `Logic`, allowing this program to
display:

```
Anne's grandparents are: ["Sarah","Arnold"]
```

This example is provided as the `grandparents` executable built by the
`logict` package so you can run it yourself and try various
experimental modifications.

The example above is very simplistic and is just a brief introduction
into the capabilities of logic programming and the `logict` package.
The `logict` package provides additional functionality such as:

 * Fair conjunction and disjunction, which can help with potentially
   infinite sets of inputs.

 * A `LogicT` monad stack that lets logic operations be performed
   along with other monadic actions (e.g. if the parents sample was
   streamed from an input file using the `IO` monad).

 * A `MonadLogic` class which allows other monads to be defined which
   provide logic programming capabilities.

## Additional Notes

The implementation in this `logict` package provides the backtracking
functionality at a lower level than that defined in the associated
paper.  The backtracking is defined within the `Alternative` class as
`<|>` and `empty`, whereas the paper uses the `MonadPlus` class and
the `mplus` and `mzero` functions; since `Alternative` is a
requirement (constraint) for `MonadPlus`, this allows both
nomenclatures to be supported and used as appropriate to the client
code.

More details on using this package as well as other functions
(including fair conjunction and disjunction) are provided in the
[Haddock documentation](https://hackage.haskell.org/package/logict).
