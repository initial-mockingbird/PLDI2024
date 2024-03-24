{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE DerivingStrategies     #-}
-- {-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE UndecidableInstances   #-}

module Basic where

import Zilly
import Data.Tree
import Data.Functor
import Control.Concurrent.MVar
import Control.Exception hiding (catch)
import Data.Functor.Identity
import Control.Monad.State.Strict
import Control.Applicative
import Control.Monad.Catch
import Prelude hiding (show)
import Prelude qualified as P

-- | Interpreter monad.
newtype Basic a = Basic {runBasic' :: StateT BasicState IO a}
  deriving newtype (Functor, Applicative, Monad, MonadState BasicState, MonadIO, MonadThrow, MonadCatch, MonadFail )

-- | Interpreter State.
data BasicState = BST 
  { cycleST     :: !Int
  }


getCycle :: (MonadState BasicState m) => m Int
getCycle = gets cycleST

nextCycle :: (MonadState BasicState m) => m ()
nextCycle = modify (\s@BST{cycleST=n} -> s{cycleST=n+1})

---------------------------
-- Types
---------------------------

type Z = Z' Basic

class HasValue a b | a -> b where
  yieldValue :: a -> b


--
data BasicVal a = BasicVal
  { serializedRvalueBV :: Tree String
  , serializedCValueBV :: Tree String
  , cvalueBV           :: Basic (Value Basic a) 
  , rvalueBV           :: a
  }

data BasicLazy a = BasicLazy
  { tagBL  :: Tag
  , wrapBL :: Basic a
  }

type Tag = String

newLazy :: BasicLazy a -> Basic (Lazy Basic a)
newLazy = fmap Lazy . liftIO . newMVar

newValue :: BasicVal a -> Basic (Value Basic a)
newValue = fmap Value . liftIO . newMVar

readBasicVal :: Value Basic a -> Basic (BasicVal a)
readBasicVal = liftIO . readMVar . runValue

readValue :: Value Basic a -> Basic a
readValue = pure . rvalueBV <=< readBasicVal

readBasicLazy :: Lazy Basic a -> Basic (BasicLazy a)
readBasicLazy = liftIO . readMVar . runLazy

readLazy :: Lazy Basic a -> Basic a
readLazy = wrapBL <=< readBasicLazy

cloneValue :: Value Basic a -> Basic (Value Basic a)
cloneValue = newValue <=< readBasicVal

cloneLazy :: Lazy Basic a -> Basic (Lazy Basic a)
cloneLazy = newLazy <=< readBasicLazy

runZES :: Basic a -> IO a
runZES x =  evalStateT  (runBasic' x) defST
  where
    defST = BST 0

instance ZEXP Basic where
  newtype instance Value Basic a = Value { runValue :: MVar (BasicVal  a) }
  newtype instance Lazy  Basic a = Lazy  { runLazy  :: MVar (BasicLazy a) }
  newtype instance Z' Basic   = Z {getZ :: Int } deriving newtype (Eq,Show,Ord,Num)
  val n = do
    var <- liftIO newEmptyMVar 
    let node  = Node ("val " <> P.show n ) []
        rval  = Value $ var 
        result = BasicVal node node (pure rval) . Z $ n

    (liftIO . putMVar var)  result $> rval
  minus ra rb = do
    BasicVal ta ta' ca va <- readBasicVal <=< rvalue $ ra 
    BasicVal tb tb' cb vb <- readBasicVal <=< rvalue $ rb 
    let 
      diff = va - vb
      content = minus @Basic ca cb
      rnode = Node "minus" [ta,tb]
      cnode = Node "minus" [ta',tb']

    newValue . BasicVal rnode cnode content $ diff

  defer = newLazy . BasicLazy "defer" . cvalue

  ifX cond bt bf = do
    BasicVal tc tc' cc vc <- readBasicVal <=< rvalue $ cond
    if vc >= 0  then rvalue bt else rvalue bf
  
  less ma mb = do
    a <- readValue <=< rvalue $ ma
    b <- readValue <=< rvalue $ mb
    if a < b then val @Basic 1 else val @Basic (-1)
  
  

instance ZFunc Basic where
  lambda f = newValue $ BasicVal t t undefined g 
    where
      g = f . rvalue
      t = Node "func" []
  f $. x = do
    g <- readValue <=< rvalue $ f
    y <-  rvalue $ x
    pure $ g y

instance ZFunc' Basic where
  lambda' :: forall a b
    . (Basic a -> b) 
    -> Basic  ( Value Basic (forall c . (RValue c (Basic a)) => (c -> b) ))
  lambda' f = newValue $ BasicVal t t undefined g 
    where
      g :: forall c. RValue c (Basic a) => c -> b
      g = f . rvalue @c @(Basic a)
      t = Node "func" []
  ($..) :: forall x a b. (RValue x (Basic a)) 
    => (Value Basic (forall c . (RValue c (Basic a)) => c -> b)) -> x -> Basic b
  f $.. x = do
    readValue  f >>= \g -> pure (g x)
    --pure $ undefined

data ZillyExceptions = HaltedZ | BottomZ deriving Show

instance Exception ZillyExceptions

instance ZACT Basic where
  data VariableData Basic a = VD { getVarData :: a }

  halt = throwM  HaltedZ

  show s mb = do
    b <- rvalue mb >>= altShow
    liftIO . putStrLn $ s <>  b 

  formula = lvalue

instance ZBottom Basic where
  bottom = throwM BottomZ

-- RValue cases

instance RValue
  (Basic (Lazy Basic (Value Basic Z)))
  (EmbeddedValue Basic Z) where
    rvalue ml = do
      BasicVal _ _ cvalue _ <- readBasicVal =<< readLazy =<< ml
      cvalue

instance RValue
  (Lazy Basic (Lazy Basic a))
  (EmbeddedLazy Basic a) where
    rvalue = readLazy 

instance RValue
  (Basic (Lazy Basic (Lazy Basic a)))
  (EmbeddedLazy Basic a) where
    rvalue = rvalue <=< id 

instance RValue
  (Basic (Value Basic Z)) 
  (EmbeddedValue Basic Z) where
    rvalue  =  id

instance RValue
  (Value Basic Z)
  (EmbeddedValue Basic Z) where
    rvalue = pure

instance RValue
  (Lazy Basic (Value Basic Z)) 
  (Basic (Value Basic Z)) where
    rvalue =  readLazy

instance (RValue a b) => RValue (VariableData Basic a) b where
  rvalue = rvalue . getVarData

-- LValue cases

-- lift (m value) = m value
instance CValue 
  (Basic (Value Basic a))
  (Basic (Value Basic a)) where
  cvalue = id

-- lift a = b => lift (Var a) = b
instance (CValue a b) => CValue (VariableData Basic a) b where
  cvalue = cvalue . getVarData


-- lift (value) = m value
instance CValue 
  (Value Basic a) 
  (Basic (Value Basic a)) where
    cvalue = pure 

instance CValue 
  (Lazy Basic a) 
  (Basic (Lazy Basic a)) where
    cvalue = pure 

instance CValue 
  (Basic (Lazy Basic a))
  (Basic (Lazy Basic a)) where
    cvalue = id

-- CValues cases

-- lift (m value) = m value
instance LValue 
  (Basic (Value Basic a)) 
  (Basic (Value Basic a)) where
  lvalue = cloneValue <=< id

-- lift a = b => lift (Var a) = b
instance (LValue a b) => LValue (VariableData Basic a) b where
  lvalue = lvalue . getVarData

-- lift (value) = m value
instance LValue 
  (Value Basic a) 
  (Basic (Value Basic a)) where
    lvalue = cloneValue 

instance LValue 
  (Lazy Basic a) 
  (Basic (Lazy Basic a)) where
    lvalue = cloneLazy 

instance LValue 
  (Basic (Lazy Basic a))
  (Basic (Lazy Basic a)) where
    lvalue = cloneLazy <=< id 

-- Assignable cases

instance Assignable Basic
  (Basic (Value Basic Z))
  (VariableData Basic (Value Basic Z)) where
    (VD a) ~~ b = liftIO . void . swapMVar (runValue a) =<< readBasicVal =<< b
   

instance Assignable Basic
  (VariableData Basic (Value Basic Z))
  (VariableData Basic (Value Basic Z)) where
    (VD a) ~~ (VD b) = liftIO . void . swapMVar (runValue a) =<< readBasicVal b

instance Assignable Basic
  (Basic (Lazy Basic a))
  (VariableData Basic (Lazy Basic a)) where
    (VD a) ~~ b = liftIO . void . swapMVar (runLazy a) =<< readBasicLazy =<< b


-- Declarable cases

instance Declarable Basic
  (Basic (Value Basic a))
  (VariableData Basic (Value Basic a)) where
     declare = fmap VD . cloneValue <=< id

instance Declarable Basic
  (Value Basic a)
  (VariableData Basic (Value Basic a)) where
     declare = fmap VD . cloneValue 

instance Declarable Basic
  (VariableData Basic (Value Basic a))
  (VariableData Basic (Value Basic a)) where
    declare =  (fmap VD . cloneValue . getVarData)


instance Declarable Basic
  (Basic (Lazy Basic a))
  (VariableData Basic (Lazy Basic a)) where
     declare = fmap VD . cloneLazy <=< id

instance Declarable Basic
  (Lazy Basic a)
  (VariableData Basic (Lazy Basic a)) where
     declare = fmap VD . cloneLazy 

instance Declarable Basic
  (VariableData Basic (Lazy Basic a))
  (VariableData Basic (Lazy Basic a)) where
    declare =  (fmap VD . cloneLazy . getVarData)

-- AltShow cases

instance Show a => AltShow Basic (Value Basic a) where
  altShow = fmap P.show . readValue

instance (Show b, HasValue a (Basic (BasicVal b))) 
  =>  AltShow Basic (Lazy Basic a) where
    altShow ml =  do
      BasicLazy tag mval <- readBasicLazy ml
      BasicVal _ t _ _   <- yieldValue =<< mval
      let 
        t'  = Node tag [t]
      pure . drawTree $ t'

-- HasValue cases


instance (Value Basic a) `HasValue` (Basic (BasicVal a)) where
  yieldValue = readBasicVal

instance (Basic (Value Basic a)) `HasValue` (Basic (BasicVal a)) where
  yieldValue = yieldValue <=< id

instance (a `HasValue` Basic (BasicVal b)) 
  => (Lazy Basic a) `HasValue` (Basic (BasicVal b)) where
  yieldValue ml = do
    BasicLazy tag mval <- readBasicLazy ml
    BasicVal t0 t1 cv rv <- yieldValue =<< mval
    let t1' = Node tag [t1]
    pure $ BasicVal t0 t1' cv rv


