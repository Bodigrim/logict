# 0.7.1.0

* Improve documentation.
* Relax superclasses of `MonadLogic` to `Monad` and `Alternative` instead of `MonadPlus`.

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
