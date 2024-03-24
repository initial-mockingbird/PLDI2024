{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}
-- {-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Zilly where

import Prelude hiding (Show, show)
import Prelude qualified as P
import Control.Concurrent.MVar
import Data.Functor.Identity
import Data.Kind (Type)


type Symbol = String


-- Lifting evaluation to the type levels gives us the
-- ability to provide extensible strategies that are easily swappable
class RValue a b  | a -> b where
  rvalue :: a -> b

-- Also allows us to have multiple types of evaluation, not just rvalues, but contents too.
class CValue a b  | a -> b where
  cvalue :: a -> b

class LValue a b | a -> b where
  lvalue :: a -> b


type EmbeddedValue m a = m (Value m a)
type EmbeddedLazy m a = m (Lazy m a) 

class ZEXP m where
  -- Result values useful for:
  -- + Modeling alternative data modes such as reactive mutable state.
  -- + Provides flexibility (can be a data thats not exposed, 
  --   making impossible to inject haskell values into the DSL, or a type allowing the DSL 
  --   to interact more freely with haskell code)
  -- + Composable: every function in our DSL recieves a value of this type, effectively 
  data Value m a :: Type
  data Lazy  m a :: Type
  data Z'    m   :: Type
  
  val     :: Int -> m (Value m (Z' m))
  minus   :: (RValue a (EmbeddedValue m (Z' m)), RValue b (EmbeddedValue m (Z' m)))
    => a -> b -> m (Value m (Z' m))
  
  defer  :: (CValue a (m b))
    => a -> m (Lazy m b)

  ifX :: 
    ( RValue a (EmbeddedValue m (Z' m))
    , RValue b (EmbeddedValue m x)
    , RValue c (EmbeddedValue m x)
    )
    => a -> b -> c -> EmbeddedValue m x
  
  less :: 
    ( RValue a (EmbeddedValue m (Z' m))
    , RValue b (EmbeddedValue m (Z' m))
    )
    => a -> b -> EmbeddedValue m (Z' m)

class ZEXP m => ZFunc m where 
  lambda  :: (RValue c (m a))
    => (m a -> b) -> EmbeddedValue m (c -> b) 

  infixr 0 $.
  ($.) :: (RValue f (EmbeddedValue m (c -> b)), RValue x (m c)) 
    => f -> x -> m b

class ZEXP m => ZFunc' m where 
  lambda'
    :: forall a b. (m a -> b) 
    -> m  ( Value m (forall c . (RValue c (m a)) => (c -> b) ))

  infixr 0 $..
  ($..) :: forall x a b. (RValue x (m a)) 
    => (Value m (forall c . (RValue c (m a)) => c -> b)) -> x -> m b

class AltShow m a where
  altShow :: a -> m String

class Assignable m b a | m b -> a where
  infix 0 ~~
  (~~) :: a -> b -> m ()

class Declarable m b a | m b -> a where
  declare :: b -> m a

class ZEXP m => ZACT m where

  data VariableData m a :: Type
  formula :: (LValue a (m b))
    => VariableData m a -> m b
  halt :: m ()
  show :: forall a b. (AltShow m a, RValue b (m a)) => String -> b -> m ()

class ZBottom m where
  bottom :: m a

-----------------------
-- Type Judgments
-----------------------

type ZEXPConstraints m =
  ( Monad m
  , ZEXP m
  -- RValues
  , m (Lazy m (Value m (Z' m))) `RValue` EmbeddedValue m (Z' m)  
  , forall a. m (Lazy m (Lazy m a)) `RValue` EmbeddedLazy m a
  , EmbeddedValue m (Z' m) `RValue` EmbeddedValue m (Z' m)
  , Value m (Z' m) `RValue` EmbeddedValue m (Z' m)
  , Lazy m (Value m (Z' m)) `RValue` m (Value m (Z' m))
  , forall a. Lazy m (Lazy m a) `RValue` EmbeddedLazy m a
  -- Variable Data RValue Unfold
  , VariableData m (m (Lazy m (Value m (Z' m)))) `RValue` EmbeddedValue m (Z' m)  
  , forall a. VariableData m (m (Lazy m (Lazy m a))) `RValue` EmbeddedLazy m a
  , VariableData m (EmbeddedValue m (Z' m)) `RValue` EmbeddedValue m (Z' m)
  , VariableData m (Value m (Z' m)) `RValue` EmbeddedValue m (Z' m)
  , VariableData m (Lazy m (Value m (Z' m))) `RValue` m (Value m (Z' m))
  -- LValue
  , forall a. m (Value m a) `LValue` m (Value m a)
  , forall a. Value m a `LValue` m (Value m a)
  , forall a. Lazy m a `LValue` m (Lazy m a)
  , forall a. m (Lazy m a) `LValue` m (Lazy m a)
  -- Variable Data LValue Unfold
  , forall a. VariableData m (Value m a) `LValue` m (Value m a)
  , forall a. VariableData m (Lazy m a) `LValue` m (Lazy m a)
  {- , forall a. m (VariableData m (Value m a)) `LValue` m (Value m a)
  , forall a. m (VariableData m (Lazy m a)) `LValue` m (Lazy m a) -}
  -- CValue
  , forall a. m (Value m a) `CValue` m (Value m a)
  , forall a. Value m a `CValue` m (Value m a)
  , forall a. VariableData m (Value m a) `CValue` m (Value m a)
  , forall a. Lazy m a `CValue` m (Lazy m a)
  , forall a. m (Lazy m a) `CValue` m (Lazy m a)
  , forall a. VariableData m (Lazy m a) `CValue` m (Lazy m a)
  )

type ZFuncConstraints m =
  ( ZEXPConstraints m
  )

type AssignableConstraints m =
  ( Monad m 
  , Assignable m (m (Value m (Z' m))) (VariableData m (Value m (Z' m)))
  , Assignable m (VariableData m (Value m (Z' m))) (VariableData m (Value m (Z' m)))
  , forall a. Assignable m (m (Lazy m a)) (VariableData m (Lazy m a))
  )

type DeclarableConstraints m =
  ( Monad m 
  , forall a. Declarable m (m (Value m a)) (VariableData m (Value m a))
  , forall a. Declarable m (Value m a) (VariableData m (Value m a))
  , forall a. Declarable m (VariableData m (Value m a)) (VariableData m (Value m a))
  , forall a. Declarable m (m (Lazy m a)) (VariableData m (Lazy m a))
  , forall a. Declarable m (Lazy m a) (VariableData m (Lazy m a))
  , forall a. Declarable m (VariableData m (Lazy m a)) (VariableData m (Lazy m a))
  )

type ZACTConstraints m = 
  ( ZEXPConstraints m
  , ZACT m
  -- AltShow
  , AltShow m (Value m (Z' m))
  )

type Constraints m =
  ( ZEXPConstraints m
  , ZFuncConstraints m
  , AssignableConstraints m
  , DeclarableConstraints m
  , ZACTConstraints m
  )