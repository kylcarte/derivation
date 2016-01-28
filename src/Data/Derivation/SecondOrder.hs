{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Data.Derivation.SecondOrder where

import Data.Type.Combinator
import Data.Type.Product
import Data.Type.Quantifier
import Type.Class.HFunctor
import Type.Class.Witness
import Type.Family.List
import Type.Family.Tuple
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.List as L
import Data.Maybe
import Unsafe.Coerce

data Deriv2 (v :: k -> *)
  (rule  :: [([k],k)] -> [k] -> k -> *)
  (deriv :: [k] -> k -> *) :: [k] -> k -> * where
  (:$) :: !(rule subs gam a)
       -> !(Args deriv subs)
       -> Deriv2 v rule deriv gam a
  Var  :: !(v a)
       -> Deriv2 v rule deriv gam a
  Bind :: !(v a)
       -> Deriv2 v rule deriv gam b
       -> Deriv2 v rule deriv (a :< gam) b
infix 1 :$

class Monad m => MonadFresh v m | v -> m where
  named :: String -> m (v a)
  fresh :: m (v a)

type Args d = Prod (Uncur d)

pattern (:*) :: p a b -> Args p ps -> Args p (a#b :< ps)
pattern a :* as = Uncur a :< as
infixr 5 :*

data Derivation2 v r gam a = Derivation2
  { viewDeriv2 :: forall m. MonadFresh v m => m (Deriv2 v r (Derivation2 v r) gam a)
  }

($$) :: r subs gam a -> Args (Derivation2 v r) subs -> Derivation2 v r gam a
r $$ s = Derivation2 $ return $ r :$ s
infixl 1 $$

bind :: Maybe String -> (Derivation2 v r gam a -> Derivation2 v r gam b) -> Derivation2 v r (a :< gam) b
bind mx f = Derivation2 $ do
  x <- maybe fresh named mx
  Bind x <$> viewDeriv2 (f $ Derivation2 $ return $ Var x)

data STLC :: [([*],*)] -> [*] -> * -> * where
  Lam :: STLC '[ (a :< gam) # b ]
         gam (a -> b)
  App :: STLC '[ gam # (a -> b), gam # a ]
         gam b

{-

type E = Derivation2 Var STLC

lam :: (E gam a -> E gam b) -> E gam (a -> b)
lam f = Lam $$ (bind Nothing f) :* Ø

(#) :: E gam (a -> b) -> E gam a -> E gam b
f # a = App $$ f :* a :* Ø
infixl 8 #

e0 :: E gam ((a -> b) -> a -> b)
e0 = lam $ \f -> lam $ \x -> f # x

-- Vars {{{

newtype Vars a = Vars
  { unVars :: Int -> Set String -> (Int,a)
  }

runVars :: Vars a -> (Int,a)
runVars m = unVars m 0 S.empty

evalVars :: Vars a -> a
evalVars = snd . runVars

instance Functor Vars where
  fmap f (Vars g) = Vars $ \i -> fmap f . g i

instance Applicative Vars where
  pure a = Vars $ \i _ -> (i,a)
  Vars f <*> Vars a = Vars $ \i0 xs -> let
    (i1,f') = f i0 xs
    (i2,a') = a i1 xs
    in (i2,f' a')

instance Monad Vars where
  Vars m >>= f = Vars $ \i0 xs -> let
    (i1,a) = m i0 xs
    in unVars (f a) i1 xs

used :: Vars (Set String)
used = Vars $ \i xs -> (i,xs)

useds :: (Set String -> r) -> Vars r
useds f = do
  xs <- used
  return $ f xs

tick :: Vars Int
tick = Vars $ \i _ -> (i+1,i)

-- }}}

-- V {{{

data V = V
  { vId   :: Int
  , vName :: Maybe String
  } deriving (Eq,Ord)

instance Show V where
  show (V i mn) = fromMaybe "x" mn ++ show i

-- }}}

-- Type {{{

data Type :: * -> * where
  Base  :: Type a
  (:->) :: !(Type a)
        -> !(Type b)
        -> Type (a -> b)
  (:+:) :: !(Type a)
        -> !(Type b)
        -> Type (Either a b)
  (:*:) :: !(Type a)
        -> !(Type b)
        -> Type (a,b)
infixr 1 :->
infixr 2 :+:
infixr 3 :*:

deriving instance Eq   (Type a)
deriving instance Show (Type a)

instance Show1 Type

instance TestEquality Type where
  testEquality a = \case
    Base    -> case a of
      Base -> Just $ unsafeCoerce Refl
      _    -> sym <$> testEquality Base a
    b :-> c -> testArr  a b c
    b :+: c -> testSum  a b c
    b :*: c -> testProd a b c

testArr :: Type a -> Type b -> Type c -> Maybe (a :~: (b -> c))
testArr a b c = case a of
  b' :-> c' -> testEquality b b' /? testEquality c c' /? qed
  Base      -> Just $ unsafeCoerce Refl
  _         -> Nothing

testSum :: Type a -> Type b -> Type c -> Maybe (a :~: Either b c)
testSum a b c = case a of
  b' :+: c' -> testEquality b b' /? testEquality c c' /? qed
  Base      -> Just $ unsafeCoerce Refl
  _         -> Nothing

testProd :: Type a -> Type b -> Type c -> Maybe (a :~: (b,c))
testProd a b c = case a of
  b' :*: c' -> testEquality b b' /? testEquality c c' /? qed
  Base      -> Just $ unsafeCoerce Refl
  _         -> Nothing

-- }}}

data Var a = V_
  { getVar  :: V
  , varType :: Type a
  } deriving (Eq)

instance Show (Var a) where
  show = show . getVar

instance Show1 Var

instance TestEquality Var where
  testEquality x y = testEquality (varType x) (varType y)

mkV :: String -> Int -> Var a
mkV x i = V_ (V i $ Just x) Base

mkV_ :: Int -> Var a
mkV_ i = V_ (V i Nothing) Base

instance MonadFresh Var Vars where
  fresh   = mkV_  <$> tick
  named x = useds (elem x) >>= \b -> if b then named (x ++ "'") else mkV x <$> tick

filter' :: (forall x. f x -> Bool) -> Prod f as -> Some (Prod f)
filter' f = \case
  Ø       -> Some Ø
  a :< as -> some (filter' f as) $ \as' -> if f a
    then Some $ a :< as'
    else Some as'

newtype Coll f = Coll
  { getColl :: Some (Prod f)
  }

deriving instance Show1 f => Show (Coll f)

instance Show1 f => Show (Some f) where
  showsPrec d (Some a) = showsPrec1 d a

instance Show1 f => Show1 (Prod f) where
  showsPrec1 _ p = showString "⟦" . go p . showString "⟧"
    where
    go :: Prod f as -> ShowS
    go = \case
      Ø       -> id
      a :< Ø  -> shows1 a
      a :< as -> shows1 a . showString ", " . go as

freeVars :: forall gam a. Derivation2 Var STLC gam a -> Vars (Coll Var)
freeVars (Derivation2 md) = go =<< md
  where
  go :: Deriv2 Var STLC (Derivation2 Var STLC) g x -> Vars (Coll Var)
  go = \case
    _ :$ s   -> foldMapM' (\(Uncur d) -> freeVars d) s
    Var  x   -> return $ Coll $ Some $ x :< Ø
    Bind x e -> do
      Coll xs <- go e
      return $ Coll $ some xs $ filter' $ \y ->
          fromMaybe False
        $ testEquality x y /? Just (x == y)

instance Monoid (Coll f) where
  mempty = Coll $ Some Ø
  mappend (Coll as) (Coll bs) = some as $ \as' -> some bs $ \bs' -> Coll $ Some $ append' as' bs'

freshVar :: Coll Var -> Maybe String -> Var a
freshVar xs mn = V_ (freshV (getVs xs) mn) Base

getVs :: Coll Var -> Set V
getVs (Coll xs) = some xs $ foldMap' $ S.singleton . getVar

freshV :: Set V -> Maybe String -> V
freshV = V . nextAvail . S.map vId

nextAvail :: Set Int -> Int
nextAvail = head . foldl (flip L.delete) [0..]

render :: Derivation2 Var STLC gam a -> IO ()
render d = putStrLn $ evalVars (rendersPrec 0 d) ""

rendersPrec :: forall m v gam a. (MonadFresh v m, Show1 v) => Int -> Derivation2 v STLC gam a -> m ShowS
rendersPrec d (Derivation2 md) = go md
  where
  go :: m (Deriv2 v STLC (Derivation2 v STLC) g x) -> m ShowS
  go drv = drv >>= \case
    Var  x   -> return $ shows1 x
    Bind x e -> do
      body <- go $ return e
      return $ showParen (d > 0)
        $ shows1 x
        . showString ". "
        . body
    r :$ s -> case (r,s) of
      (Lam,Uncur e :< Ø) -> do
        body <- rendersPrec 0 e
        return $ showParen (d > 1)
          $ showString "λ"
          . body
      (App,Uncur f :< Uncur a :< Ø) -> do
        f' <- rendersPrec 11 f
        a' <- rendersPrec 11 a
        return $ showParen (d > 10)
          $ f'
          . showChar ' '
          . a'
      _ -> error "impossible"

foldMapM' :: (Monad m, Monoid r, HTraversable t) => (forall x. f x -> m r) -> t f a -> m r
foldMapM' f = fmap (foldMap' getC) . traverse' (fmap C . f)

-- Show{1,2,3} {{{

class Show1 f where
  showsPrec1 :: Int -> f a -> ShowS
  default showsPrec1 :: Show (f a) => Int -> f a -> ShowS
  showsPrec1 = showsPrec

shows1 :: Show1 f => f a -> ShowS
shows1 = showsPrec1 0

show1 :: Show1 f => f a -> String
show1 = ($ "") . shows1


class Show2 f where
  showsPrec2 :: Int -> f a b -> ShowS
  default showsPrec2 :: Show (f a b) => Int -> f a b -> ShowS
  showsPrec2 = showsPrec

shows2 :: Show2 f => f a b -> ShowS
shows2 = showsPrec2 0

show2 :: Show2 f => f a b -> String
show2 = ($ "") . shows2


class Show3 f where
  showsPrec3 :: Int -> f a b c -> ShowS
  default showsPrec3 :: Show (f a b c) => Int -> f a b c -> ShowS
  showsPrec3 = showsPrec

shows3 :: Show3 f => f a b c -> ShowS
shows3 = showsPrec3 0

show3 :: Show3 f => f a b c -> String
show3 = ($ "") . shows3

-- }}}
-}

