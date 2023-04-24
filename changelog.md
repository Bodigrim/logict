# 0.8.1.0

* Add `instance MonadLogic (Control.Monad.Writer.CPS.WriterT w m)`.

# 0.8.0.0

* Breaking change:
  do not re-export `Control.Monad` and `Control.Monad.Trans` from `Control.Monad.Logic`.
* Generalize `instance Traversable (LogicT Identity)`
  to `instance (Traversable m, Monad m) => Traversable (LogicT m)`.
* Add conversion functions `fromLogicT` and `fromLogicTWith` to facilitate
  interoperation with [`list-t`](https://hackage.haskell.org/package/list-t)
  and [`logict-sequence`](https://hackage.haskell.org/package/logict-sequence) packages.
* Add `hoistLogicT` and `embedLogicT` to convert `LogicT` computations
  from one underlying monad to another.

# 0.7.1.0

* Improve documentation.
* Breaking change:
  relax superclasses of `MonadLogic` to `Monad` and `Alternative` instead of `MonadPlus`.

# 0.7.0.3

* Support GHC 9.0.

# 0.7.0.2

* Add `Safe` pragmas.

# 0.7.0.1

* Fix `MonadReader r (LogicT m)` instance again.

# 0.7.0.0

* Remove unlawful `MonadLogic (Writer T w m)` instances.
* Fix `MonadReader r (LogicT m)` instance.
* Move `lnot` into `MonadLogic` class.

# 0.6.0.3

* Comply with MonadFail proposal.
