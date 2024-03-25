{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
module ZTest where

import Zilly
import Basic
import Prelude hiding (Show(..))
import Prelude qualified as P
import Data.Tree
import Control.Exception (SomeException)
import Control.Monad.Catch (catch, throwM)
import Data.Function ((&))
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Catch (MonadCatch (..))
example1 :: forall m. Constraints m => m ()
example1 = do
  x   <- val 5
  y   <- val 9

  ----------------------
  -- Basic operations --
  ----------------------

  z0  <- declare $ minus x y                 -- -4
  z1  <- declare $ minus (val @m 5) y        -- -4
  z2  <- declare $ val @m 5 `minus` val @m 9 -- -4

  --
  -- Every non negative value is truish.
  --
  z3 <- declare $ x `less` y -- 1

  --
  -- Every negative value is falseish.
  --
  z4 <- declare $ val @m 10 `less` y -- -1


  -- if then else

  z5 <- declare $ ifX (val @m 5 `less` val @m 9) (val @m 10) (val @m 20) -- 10
  z6 <- declare $ ifX (val @m 9 `less` val @m 5) (val @m 10) (val @m 20) -- 20
  let bottom = error "Bottom Value" :: EmbeddedValue m (Z' m)
  z7 <- declare $ ifX (val @m 5 `less` val @m 9) (val @m 10) bottom -- 10
  z8 <- declare $ ifX (val @m 9 `less` val @m 5) bottom (val @m 20) -- 20

  ----------------------
  -- Basic Actions    --
  ----------------------

  -- Debugging
  show "z0 ==> " z0 -- -4
  show "z1 ==> " z1 -- -4
  show "z2 ==> " z2 -- -4
  show "z3 ==> " z3 --  1
  show "z4 ==> " z4 -- -1
  show "z5 ==> " z5 -- 10
  show "z6 ==> " z6 -- 20
  show "z7 ==> " z7 -- 10
  show "z8 ==> " z8 -- 20

  -- variable setting
  z7 ~~ val @m 100000

  show "z7 ==> " z7 -- 100000


example2 :: forall m. Constraints m => m ()
example2 = do

  -------------------------------------------------
  -- Reactive values via the Lazy defer function --
  -------------------------------------------------

  x <- declare $ val @m 50
  y <- declare $ val @m 100

  -- The value changes whenever a variable changes


  z0 <- declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m))))
    $ defer @m x
  z1 <- declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m))))
    $ defer y
  z2 <- declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m))))
    $ defer $ x `minus` y
  z3 <- declare @m @(VariableData m (Value m (Z' m))) @(VariableData m (Value m (Z' m)))
    $ x


  show "z0 ==> " z0 -- 50
  show "z1 ==> " z1 -- 100
  show "z2 ==> " z2 -- -50
  show "z3 ==> " z3 -- 50 

  -- Let's introduce change
  x ~~ val @m 1000
  y ~~ val @m 600

  show "z0 ==> " z0 -- 1000
  show "z0 ==> " z0 -- 1000
  show "z1 ==> " z1 -- 600
  show "z2 ==> " z2 -- 400
  show "z3 ==> " z3 -- 50

  pure ()

example3 :: forall m. (Constraints m, MonadIO m) => m ()
example3 = do
  ---------------------------------------------------
  -- Reactive values via the Lazy formula function --
  ---------------------------------------------------

  -- Lazy function only works over things that posses an l-value (left value)
  -- Thus we introduce some variables 
  x  <- declare $ val @m 50
  y  <- declare $ val @m 20
  r0 <- declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m))))
    $ defer x
  r1 <- declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m))))
    $ defer $ x `minus` y

  -- x = 50 => formula(x) = 50
  fx <- declare @m @(m (Value m (Z' m))) @(VariableData m (Value m (Z' m)))
    $ formula x
  -- r0 = 'x' => formula(r0) = x
  -- this means f0 changes whenever x changes.
  f0 <- declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m))))
    $ formula r0
  -- r1 = 'x - y' => formula(r1) = x - y
  -- this means f1 changes whenever x or y changes.
  f1 <- declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m))))
    $ formula r1


  show "x  ==> " x  -- 50
  show "r0 ==> " r0 -- 50
  show "r1 ==> " r1 -- 30

  show "fx ==> " fx -- 50
  show "f0 ==> " f0 -- 50
  show "f1 ==> " f1 -- 30
  separator
  -- This will make f0 and f1 to be recomputed since 
  -- x is a dependency for both.
  x  ~~ val @m 1000
  -- r0 is NOT a dependency for f0, this changing r0 will not
  -- make f0 change.
  -- This is the main diference between `defer` and `formula`.
  r0 ~~ defer @m @(m (Value m (Z' m))) @(Value m (Z' m)) (val @m 90)
  r1 ~~ defer @m @(m (Value m (Z' m))) @(Value m (Z' m)) (val @m 900)


  show "x  ==> " x  -- 1000
  show "r0 ==> " r0 -- 90
  show "r1 ==> " r1 -- 900

  -- as expected, fx never changes.
  -- remember that formula(x) = 50, and 50 never changes.
  show "fx ==> " fx -- 50
  -- formula('x') = x, so when x changes to 1000, so does f0.
  show "f0 ==> " f0 -- 1000
  -- formula('x - y') = x - y, so when x changes to 1000, so does f1.
  show "f1 ==> " f1 -- 980


  pure ()
  where
    separator = liftIO . putStrLn $ "-------------"


example4 :: forall m. (Constraints m, MonadIO m, MonadCatch m) => m ()
example4 = do
  ------------------------------------
  -- Reactive functions and bottoms --
  ------------------------------------

  -- we need monomorphic values in order to play around with bottoms.
  -- Otherwise, we get into issues due to Undecidable Instances
  let bottomValue    = bottom @m @(Value m (Z' m))
      bottomVariable = bottom @m @(VariableData m (Lazy m (Value m (Z' m))))


  x  <- declare @_ @_ @(VariableData m (Value m (Z' m))) $ val @m 50
  _  <- declare @_ @_ @(VariableData m (Value m (Z' m))) $ bottomValue `catch` \(e :: SomeException)
    -> (liftIO . putStrLn) "declaring a bottom, bottoms."
    >> val @m 50
  -- declaring a defered bottom doesnt yield an exception
  z0 <- declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m))))
    $ defer bottomValue

  z2 <- declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m))))
    $ defer $ x `minus` bottomValue
  z1 <- (declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m)))) . formula =<<  bottomVariable) `catch` \(e :: SomeException)
    -> (liftIO . putStrLn) "In our eDSL, it's outright impossible to pass impure variables without resorting to bottoming"
    >> declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m)))) (formula z2)
  z3 <- declare @m @(m (Lazy m (Value m (Z' m)))) @(VariableData m (Lazy m (Value m (Z' m))))
    $ formula z2


  show "'bottom'" z0              `catch` \(e :: SomeException)
    -> (liftIO . putStrLn) "evaluating a defered bottom bottoms."

  show "'x - bottom'" z2          `catch` \(e :: SomeException)
    -> (liftIO . putStrLn) "evaluating a defered expression who has a bottom subexpression bottoms."
  show "formula('x - bottom')" z3 `catch` \(e :: SomeException)
    -> (liftIO . putStrLn) "evaluating the formula that has a bottom subexpression bottoms"

example5 :: forall m. (Constraints m, MonadIO m, MonadCatch m) => m ()
example5 = do
  --------------------------------------
  -- User defined Top level functions --
  --------------------------------------

  lambda' (\x -> minus @m (val @m 0) x) >>= \chs -> do
    x  <- declare @_ @_ @(VariableData m (Value m (Z' m))) $ val @m 50
    y  <- val @m (-90)
    z0 <- chs $.. (val @m 42)
    z1 <- chs $.. y
    z2 <- chs $.. x
    show "z0 ==> " z0
    show "z1 ==> " z1
    show "z2 ==> " z2
    lambda' (\x -> do y <- chs $.. x; chs $.. y) >>= \id' -> do
      zz3 <- id' $.. x
      z3  <- zz3
      show "z3 ==> " z3



{- example6 :: forall m. (Constraints m, MonadIO m, MonadCatch m) => m ()
example6 = do
  ------------------------------------
  -- Second Order Limitation        --
  ------------------------------------
  {-
  Cannot instantiate unification variable ‘b0’
  with a type involving polytypes
  -}
  lambda' (\x -> minus @m (val @m 0) x) >>= \chs -> do
    lambda' (\x -> lambda' (\y -> do y0 <- chs $.. y; minus x y0)) >>= \add -> do
      pure ()

  pure () -}



b1 :: IO ()
b1 =  runZES example1

b2 :: IO ()
b2 = runZES example2

b3 :: IO ()
b3 = runZES example3

b4 :: IO ()
b4 = runZES example4


b5 :: IO ()
b5 = runZES example5