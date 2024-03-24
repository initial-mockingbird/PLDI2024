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


b1 :: IO ()
b1 =  runZES example1 

b2 :: IO ()
b2 = runZES example2





