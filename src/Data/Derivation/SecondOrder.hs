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
import Type.Family.List
import Type.Family.Tuple
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe

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

type E = Derivation2 Var STLC

lam :: (E gam a -> E gam b) -> E gam (a -> b)
lam f = Lam $$ (bind Nothing f) :* Ø

(#) :: E gam (a -> b) -> E gam a -> E gam b
f # a = App $$ f :* a :* Ø
infixl 8 #

e0 :: E gam ((a -> b) -> a -> b)
e0 = lam $ \f -> lam $ \x -> f # x

class Show1 f where
  showsPrec1 :: Int -> f a -> ShowS

shows1 :: Show1 f => f a -> ShowS
shows1 = showsPrec1 0

show1 :: Show1 f => f a -> String
show1 = ($ "") . shows1

newtype Vars a = Vars
  { unVars :: Int -> Set String -> (Int,a)
  }

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

data V = V
  { vId   :: Int
  , vName :: Maybe String
  } deriving (Eq,Ord)

instance Show V where
  show (V i mn) = fromMaybe "x" mn ++ show i

type Var = C V

mkV :: String -> Int -> Var a
mkV x i = C $ V i $ Just x

mkV_ :: Int -> Var a
mkV_ i = C $ V i Nothing

instance MonadFresh Var Vars where
  fresh   = mkV_  <$> tick
  named x = useds (elem x) >>= \b -> if b then named (x ++ "'") else mkV x <$> tick

freeVars :: forall gam a. Derivation2 Var STLC gam a -> Vars (Set V)
freeVars (Derivation2 md) = go =<< md
  where
  go :: Deriv2 Var STLC (Derivation2 Var STLC) g x -> Vars (Set V)
  go = \case
    Var (C x) -> return $ S.singleton $ V (vId x) (vName x)
    Bind (C x) e  -> do
      xs <- go e
      return $ S.delete x xs
    r :$ s -> _

{-
render :: Derivation2 V STLC gam a -> String
render d = 
-}

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
        . showString " . "
        . body
    r :$ s -> case (r,s) of
      (Lam,e :* Ø) -> do
        body <- rendersPrec 0 e
        return $ showParen (d > 1)
          $ showString "\\ "
          . body
      (App,f :* a :* Ø) -> do
        f' <- rendersPrec 11 f
        a' <- rendersPrec 11 a
        return $ showParen (d > 10)
          $ f'
          . showChar ' '
          . a'

