
module Control.Monad.Refinement.Combinators where

import Control.Monad.Refinement
import Control.Monad.Refinement.Class
import qualified Data.Foldable as F
import qualified Data.Map as Map
import Data.Semigroup
import Prelude hiding ((*))


unique ::
  ( Propositional c, Letter c
  , Monoidal c, Unital c
  , Additive c, Multiplicative c
  , Ord c, Group c
  , Additive p, Monoid p
  , Foldable f, Monad m
  ) => p -> f c -> RefinementT p c m ()
unique p c = constraintUnique (F.toList c) p

constraintUnique ::
  ( Propositional c, Letter c
  , Monoidal c, Unital c
  , Additive c, Multiplicative c
  , Ord c, Group c
  , Additive p, Monoid p, Monad m
  ) => [c] -> p -> RefinementT p c m ()
constraintUnique (a : b : cs) p = do
  mapM_ (rule p . (*) a) (b : cs)
  constraintUnique (b : cs) p
constraintUnique _ _ = return ()

knownComponents :: Monad m => RefinementT p c m [c]
knownComponents = RefinementT $ \(n, s) -> pure (Map.keys s, (n, s))

