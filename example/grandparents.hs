{-# LANGUAGE CPP #-}

import Control.Applicative
import Control.Monad.Logic
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid (..))
#endif
#if MIN_VERSION_base(4,9,0)
import Data.Semigroup (Semigroup (..))
#endif


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
          putStrLn $ "Anne's grandparents are: " ++ show grandparents
