
module Control.Monad.Refinement where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Refinement.Class
import Control.Monad.Refinement.DNF
import Control.Monad.Trans.Class 
import Data.Copointed
import Data.Functor.Alt (Alt(..))
import Data.Functor.Bind (Bind(..))
import Data.Functor.Identity
import Data.Functor.Plus (Plus, Apply, (<.>))
import qualified Data.Functor.Plus as Plus
import Data.Maybe
import Data.Map as Map hiding (foldr)
import Data.IntMap (IntMap)
import qualified Data.IntMap as I
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Semigroup
import Numeric.Algebra
import Prelude hiding ((+), (*), negate, minimum, maximum, lookup)

-- | To map a category of unrefined products to a category of refined products:
-- Rules have effects on such a refinement

-- | p  the product
--   c  an algebra of components over said product
--   m  monad transformer loophole
--   r  a return value
type RuleMap c p = Map c (IntMap (Heuristic c, p))
newtype RefinementT p c m r = RefinementT
  { unRefinementT :: (Int, RuleMap c p) -> m (r, (Int, RuleMap c p)) }
type Refinement p c = RefinementT p c Identity

data Heuristic c = MinTerm (Set c) deriving Show

evalRefinement :: Ord c => Refinement p c a -> a
evalRefinement = copoint . evalRefinementT

evalRefinementT :: (Ord c, Functor m) => RefinementT p c m a -> m a
evalRefinementT (RefinementT f) = fst <$> f (0, mempty)

refinement ::
  ( Propositional c, Quantifiable c, Letter c, Unital c, Group c, Ord c
  , Monoidal p, Multiplicative p
  ) => Refinement p c () -> c -> p
refinement x = copoint . refinementT x . reduce . toDNF

refinementT ::
  ( Group c, Unital c, Propositional c, Quantifiable c, Letter c, Ord c
  , Monoidal p, Multiplicative p, Monad m
  ) => RefinementT p c m () -> c -> m p
refinementT (RefinementT f) uc = do
  ~(_, (_, ma)) <- f (0, mempty)
  pure . foldr1 (*) $ refinementA ma <$> disjunctions uc

refinementA
  :: (Ord c, Group c, Unital c, Propositional c, Quantifiable c, Letter c, Monoidal p)
  => RuleMap c p -> c -> p
refinementA ma c
  | c == zero
  = foldr (\(_, a) b -> a + b) zero
  $ foldl' mappend mempty ma
refinementA ma c
  = foldr g zero
  . mconcat . catMaybes
  $ lookup one ma : [letter d `lookup` ma | d <- conjunctions c]
  where
  g (MinTerm xs, a) b | foldr (\e v -> v && sufficient e c) True xs = a + b
  g _ b = b

rule
  :: (Propositional c, Letter c, Unital c, Ord c, Group c, Monad m, Additive p)
  => p -> c -> RefinementT p c m ()
rule p = ruleDNF p . reduce . toDNF

ruleDNF
  :: (Propositional c, Letter c, Ord c, Monoidal c, Monad m, Additive p)
  => p -> c -> RefinementT p c m ()
ruleDNF = flip constraintDNF

constraint
  :: (Propositional c, Letter c, Unital c, Ord c, Group c, Monad m, Additive p)
  => c -> p -> RefinementT p c m ()
constraint = flip rule

-- | Only rules with given component-algebra in DNF are fully effective
--
constraintDNF
  :: (Propositional c, Letter c, Ord c, Monoidal c, Monad m, Additive p)
  => c -> p -> RefinementT p c m ()
constraintDNF c p | Just (a, b) <- disjunction c = constraintDNF a p >> constraintDNF b p
constraintDNF c p = do
  i <- ruleCount
  j:_ <- (++[i]) . I.keys . I.filter criteria <$> ruleSet c
  addRule $ fromList [(letter d, I.singleton j (MinTerm distinct, p)) | d <- conjunctions c]
  where
    distinct = Set.fromList $ conjunctions c
    criteria (MinTerm xs, _) = xs == distinct

modifyRuleSet :: Monad m => (Int -> Int) -> (RuleMap c p -> RuleMap c p) -> RefinementT p c m ()
modifyRuleSet g f = RefinementT $ \(n, s) -> pure ((), (g n, f s))

addRule :: (Ord c, Additive p, Monad m) => RuleMap c p -> RefinementT p c m ()
addRule = modifyRuleSet succ . unionWith (I.unionWith $ \(h, p) (_, q) -> (h, p + q))

ruleCount :: Monad m => RefinementT p c m Int 
ruleCount = RefinementT $ \(n, s) -> pure (n, (n, s))

ruleSet :: (Letter c, Ord c, Monad m) => c -> RefinementT p c m (IntMap (Heuristic c, p))
ruleSet c = RefinementT $ \(n, s) -> pure (maybe mempty id $ letter c `lookup` s, (n, s))


instance Functor m => Functor (RefinementT p c m) where
  fmap f m = RefinementT $ \s -> g <$> unRefinementT m s
    where g ~(r, s') = (f r, s')

instance Monad m => Apply (RefinementT p c m) where
  RefinementT mf <.> RefinementT mx = RefinementT $ \s -> do
    ~(f, s')  <- mf s
    ~(x, s'') <- mx s'
    return (f x, s'')

instance Alt m => Alt (RefinementT p c m) where
  RefinementT mx <!> RefinementT my = RefinementT $ \s -> mx s <!> my s

instance Monad m => Applicative (RefinementT p c m) where
  pure a = RefinementT $ \s -> return (a, s)
  (<*>)  = (<.>) 

instance Monad m => Bind (RefinementT p c m) where
  m >>- k = RefinementT $ \s -> do
    ~(r, s') <- unRefinementT m s
    unRefinementT (k r) s'

instance Monad m => Monad (RefinementT p c m) where
  return = pure
  (>>=)  = (>>-)

instance Plus m => Plus (RefinementT p c m) where
  zero = RefinementT $ const Plus.zero

instance (Monad m, Plus m) => Alternative (RefinementT p c m) where
  empty = Plus.zero
  (<|>) = (<!>)

instance (Monad m, Plus m) => MonadPlus (RefinementT p c m) where
  mzero = Plus.zero
  mplus = (<!>)

instance MonadTrans (RefinementT p c) where
  lift m = RefinementT $ \s -> do
    a <- m
    return (a, s)

instance (MonadIO m) => MonadIO (RefinementT p c m) where
  liftIO = lift . liftIO

-- | Print the internals of RefinementT to stdout
showRuleSet :: (Copointed m, Ord c, Show c, Show p) => RefinementT p c m () -> IO () 
showRuleSet (RefinementT s) = putStr $
  showTreeWith showElem False True . snd . snd . copoint $ s (0, mempty)
  where showElem k a = show k ++" := "++ show a

