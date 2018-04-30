{-# LANGUAGE FlexibleContexts #-}

module Control.Monad.Refinement.HardSAT where

import Data.Matrix hiding ((!), trace)
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set, member, union, foldl')
import Data.Array.ST
import Data.Array.IArray
import Data.Array.MArray()
import Data.STRef
import qualified Data.Vector as Boxed
import qualified Data.Vector as V
import Control.Monad
import Control.Monad.Refinement.Class hiding ((*), (+), product)
import Control.Monad.ST
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Prelude as List hiding (negate)
import System.Random.Mersenne


type Assignment = (Bool, Int)

data Convergence = Converged | Unconverged
  deriving Eq

-- | Matrix representation of SAT formulae
--   paired with removed rows and columns
--   (M, V, F)
type Formula s = STRef s (Matrix Int, [Int], [Int])
 
-- | Effectful survey propagation through strict state and access to random numbers
--
type SP s = StateT Seed (ST s)

type Seed = [Double]


type Survey s = STUArray s Int Double

type Belief s = STUArray s Int Double
type Beliefs s = (Belief s, Belief s, Belief s)


newtype FactorGraph s = Factor (Indexed (VarNode s), Indexed (FunNode s), [Edge s])

type Indexed n = Array Int n

type Edge s = (FunNode s, VarNode s, Beliefs s, Survey s)

data VarNode s = Var Int [Edge s] (Boxed.Vector Int)

instance Eq (VarNode s) where
  Var i _ _ == Var j _ _ = i == j


data FunNode s = Fun Int [Edge s] (Boxed.Vector Int)

instance Eq (FunNode s) where
  Fun a _ _ == Fun b _ _ = b == a



-- | User interface
--
--  `evalSP` uses an infinite list of random numbers:
--  IO effects are interleaved in the evaluation of that list
--
--  Use `evalSPWithSeed` to seperate pure code.
--
evalSP :: Matrix Int -> Int -> Double -> IO [Assignment]
evalSP f tmax e
  = evalSPWithSeed
      <$> (randoms =<< getStdGen)
      <*> pure f
      <*> pure tmax
      <*> pure e

evalSPWithSeed :: Seed -> Matrix Int -> Int -> Double -> [Assignment]
evalSPWithSeed g f tmax e = runST $ evalStateT (sp (f, tmax, e)) g

-- | Lifted utility
--
newRef :: a -> SP s (STRef s a)
newRef = lift . newSTRef

readRef :: STRef s a -> SP s a
readRef = lift . readSTRef

writeRef :: STRef s a -> a -> SP s ()
writeRef r = lift . writeSTRef r

modifyRef :: STRef s a -> (a -> a) -> SP s ()
modifyRef r = lift . modifySTRef r

ix :: STUArray s Int Double -> Int -> SP s Double
ix a = lift . readArray a

write :: STUArray s Int Double -> Int -> Double -> SP s ()
write a i = lift . writeArray a i

-- | Survey propagation
--
sp :: (Matrix Int, Int, Double) -> SP s [Assignment]
sp (f, tmax, e) = do

  -- copy of sat matrix
  f' <- newRef (f, [], [])
  -- cancel computation when this references to `Unconverged`
  c' <- newRef Converged

  -- assignment vector
  a' <- newRef []

  -- iterate through all columns
  sequence_ $ replicate (ncols f) $ do

    c <- readRef c'
    unless (c == Unconverged) $ do

      (d, (s, t)) <- convergence (f', tmax, e)

      -- break when `Unconverged` is returned
      writeRef c' d

      when (d == Converged) $ do

         (v, i) <- assignment (s, t)
         modifyRef a' ((v, i) :)

         decimation (f', v, i)

  -- return assignment vector
  readRef a'


-- | Convergence
--
--   returns `Converged`, the factor graph state and iteration step t
--   where all surveys converged
--   OR `Unconverged` and _|_
--
convergence :: (Formula s, Int, Double) -> SP s (Convergence, (FactorGraph s, Int))
convergence (f', tmax, e) = do

  g@(Factor graph@(_, _, edges)) <- convert (f', tmax)

  c' <- newRef Unconverged
  s' <- newRef (error "UNCONVERGED", 0)

  (numbers, gen) <- splitAt (length edges) <$> get
  mapM_ ( \ (rnd, (_, _, _, survey)) -> write survey 0 rnd) (zip numbers edges)
  put gen

  forM_ [1..tmax] $ \t -> do

    c <- readRef c'
    unless (c == Converged) $ forM_ edges $ \ (fun, var, (bunsat, bsat, bstar), _) -> do

      -- warnings
      nowarnUnsat <- sequence $ join
           [ [ (1-) <$> ix survey (t - 1) | (_, _, _, survey) <- neighbours]
           | Fun _ neighbours _ <- unsat g var fun
           ]
      nowarnSat <- sequence $ join
           [ [ (1-) <$> ix survey (t - 1) | (_, _, _, survey) <- neighbours]
           | Fun _ neighbours _ <- sat g var fun
           ]
      nowarn <- sequence $ join
           [ [ (1-) <$> ix survey (t - 1) | (_, _, _, survey) <- neighbours]
           | Fun _ neighbours _ <- nextFuns g var fun
           ]

      -- set belief for unsat 
      write bunsat t $ product nowarnSat * (1 - product nowarnUnsat)

      -- set belief for sat
      write bsat t $ product nowarnUnsat * (1 - product nowarnSat)

      -- set belief for unconstrained
      write bstar t $ product nowarn

    unless (c == Converged) $ forM_ edges $ \ (fun, var, _, survey) -> do

      -- evaluate and set survey value for this round
      result <- sequence $ join
           [ [ (/) <$> ix bu t <*> (sum <$> sequence [ix bu t, ix ba t, ix bs t])
             | (_, _, (bu, ba, bs), _) <- neighbours ]
           | Var _ neighbours _ <- nextVars g fun var
           ]
      write survey t $ product result

    -- check for convergence with accuracy tolerance e
    unless (c == Converged) $ do
      converged <- all (< e) . map abs <$> sequence
          [(-) <$> ix s t <*> ix s (t - 1) | (_, _, _, s) <- edges]
      when (converged && edges /= []) $ do
        writeRef c' Converged
        writeRef s' (Factor graph, t)

  -- return point of convergence when converged otherwise return "UNCONVERGED"
  (,) <$> readRef c' <*> readRef s'


-- | Assignment
--
assignment :: (FactorGraph s, Int) -> SP s Assignment
assignment (g@(Factor (vars, _, _)), t) = do

  -- accumulation
  d' <- newRef 0
  i' <- newRef 1

  -- bias references
  bp' <- newRef 0
  bn' <- newRef 0

  forM_ vars $ \ var@(Var i _ _) -> do

      nowarnPositive <- sequence $ join
           [ [(1-) <$> ix survey t | (_, _, _, survey) <- neighbours]
           | Fun _ neighbours _ <- positive g var
           ]
      nowarnNegative <- sequence $ join
           [ [(1-) <$> ix survey t | (_, _, _, survey) <- neighbours]
           | Fun _ neighbours _ <- negative g var
           ]
      nowarn <- sequence $ join
           [ [(1-) <$> ix survey t | (_, _, _, survey) <- neighbours]
           | Fun _ neighbours _ <- allFuns g var
           ]

      let pplus  = (1 - product nowarnPositive) * product nowarnNegative
          pminus = (1 - product nowarnNegative) * product nowarnPositive
          pstar  = product nowarn

          biasPositive = pplus  / (pplus + pminus + pstar)
          biasNegative = pminus / (pplus + pminus + pstar)

          d = abs $ biasPositive - biasNegative

      dmax <- readRef d'
      when (d > dmax) $ do
          writeRef d' d
          writeRef i' i
          writeRef bp' biasPositive
          writeRef bn' biasNegative

  biasp <- readRef bp'
  biasn <- readRef bn'
  i <- readRef i'

  pure (biasp > biasn, i)


-- | Edge traversal
--

-- return all positive nodes when `i` is positive in `a` otherwise return all negative nodes
-- except `a` itself
sat :: FactorGraph s -> VarNode s -> FunNode s -> [FunNode s]
sat g var@(Var i _ _) a@(Fun _ _ v)
  | v V.! i == 1
  = filter (/= a) $ positive g var
sat g var@(Var i _ _) a@(Fun _ _ v)
  | v V.! i == -1
  = filter (/= a) $ negative g var
sat _ _ _ = []

-- return all neighbouring function nodes with positive polarity in `i`
positive :: FactorGraph s -> VarNode s -> [FunNode s]
positive (Factor (_, funs, _)) (Var i edges _)
  = [funs ! a | (Fun a _ v, _, _, _) <- edges, v V.! i == 1]

-- return all negative nodes when `i` is positive in `a` otherwise return all positive nodes
-- except `a` itself
unsat :: FactorGraph s -> VarNode s -> FunNode s -> [FunNode s]
unsat g var@(Var i _ _) a@(Fun _ _ v)
  | v V.! i == 1
  = filter (/= a) $ negative g var
unsat g var@(Var i _ _) a@(Fun _ _ v)
  | v V.! i == -1
  = filter (/= a) $ positive g var
unsat _ _ _ = [] 

-- return all neighbouring function nodes with negative polarity in `i`
negative :: FactorGraph s -> VarNode s -> [FunNode s]
negative (Factor (_, funs, _)) (Var i edges _)
  = [funs ! a | (Fun a _ v, _, _, _) <- edges, v V.! i == -1]

-- returns all neighbouring variable nodes except `i`
nextVars :: FactorGraph s -> FunNode s -> VarNode s -> [VarNode s]
nextVars g fun i
  = filter (/= i) $ allVars g fun

-- returns all neighbouring variable nodes
allVars :: FactorGraph s -> FunNode s -> [VarNode s]
allVars (Factor (vars, _, _)) (Fun _ edges _)
  = [vars ! i | (_, Var i _ _, _, _) <- edges]

-- returns all neighbouring function nodes
allFuns :: FactorGraph s -> VarNode s -> [FunNode s]
allFuns (Factor (_, funs, _)) (Var _ edges _)
  = [funs ! a | ((Fun a _ _), _, _, _) <- edges]

-- return all neighbouring function nodes except `a`
nextFuns :: FactorGraph s -> VarNode s -> FunNode s -> [FunNode s]
nextFuns g var a
  = filter (/= a) $ allFuns g var


-- | Decimation
--
decimation :: (Formula s, Bool, Int) -> SP s ()
decimation (f', b, i) = writeRef f' . delete =<< readRef f'
  where
    delete (f, rvars, rfuns) = (f, rvars, elim f ++ rfuns)
    elim f =
      [ a | a <- [1..nrows f]
      , let v = getRow a f
      , b && v V.! (i - 1) == 1 || v V.! (i - 1) == -1
      ]


-- | Factor graph conversion
--
convert :: (Formula s, Int) -> SP s (FactorGraph s)
convert (f', tmax) = do

  (f, rvars, rfuns) <- readRef f'

  let unn = error "neighbours not initialized"
      une = minBound
  let vars = [(i, Var i unn $ V.cons une $ getCol i f) | i <- [1..ncols f], notElem i rvars]
      funs = [(a, Fun a unn $ V.cons une $ getRow a f) | a <- [1..nrows f], notElem a rfuns]
  
  let arr = lift $ newArray (0, tmax) 0
      initSurvey = arr
      initBeliefs = (,,) <$> arr <*> arr <*> arr

  edges <- sequence
      [ (,,,) <$> pure fun <*> pure var <*> initBeliefs <*> initSurvey
      | var@(Var _ _ vector) <- map snd vars
      , (fun, polarity) <- map snd funs `zip` Boxed.toList vector
      , polarity /= 0
      ]

  let graph =
        [ ( Fun a [edge | edge@(Fun b _ _, _, _, _) <- edges, b == a] row
          , Var i [edge | edge@(_, Var j _ _, _, _) <- edges, j == i] col
          , beliefs
          , survey
          ) | (Fun a _ row, Var i _ col, beliefs, survey) <- edges ]

  let v = array (1, ncols f)
        [ (i, Var i [edge | edge@(_, Var j _ _, _, _) <- edges, j == i] col)
        | (i, Var _ _ col) <- vars ]
      e = array (1, nrows f)
        [ (a, Fun a [edge | edge@(Fun b _ _, _, _, _) <- edges, b == a] row)
        | (a, Fun _ _ row) <- funs ]

  pure $ Factor (v, e, graph)


-- | Matrix representation
--
toFormula ::
  ( Ord c, Group c
  , Monoidal c, Unital c
  , Propositional c
  ) => Set (Set c) -> Matrix Int
toFormula cnf = fromLists [polarities term | term <- Set.toList cnf]
  where
    polarities s = [member v s `polarity` member (negate v) s | v <- Set.toList variables]
    variables = foldl' ( \ b a -> union b $ Set.map pos a) Set.empty cnf
    pos c = maybe c id $ negation c
    polarity True False = 1
    polarity False True = -1
    polarity _ _ = 0


