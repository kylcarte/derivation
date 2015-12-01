{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Data.Derivation.STLC where

import Data.Derivation
import Data.Evaluation

import Prelude hiding (init)
import Control.Arrow ((>>>))
import Data.Type.Nat hiding (nat,(.+))
import qualified Data.Type.Nat as N

data Ty
  = Natural
  | Ty :-> Ty
  deriving (Eq,Ord,Show)
infixr 4 :->

data Val :: Ty -> * where
  Nat  :: Nat n -> Val Natural
  Clos :: (Val a -> Val b) -> Val (a :-> b)

data STLC :: [([Ty],Ty)] -> [Ty] -> Ty -> * where
  NAT :: !(Nat n)
      -> STLC '[]                                  gam  Natural
  ADD :: STLC '[ '(gam,Natural) , '(gam,Natural) ] gam  Natural
  VAR :: !(Index gam a)
      -> STLC '[]                                  gam   a
  LAM :: STLC '[ '(a :< gam,b) ]                    gam  (a :-> b)
  APP :: STLC '[ '(gam,a :-> b) , '(gam,a) ]       gam   b

type (|-) = Derivation STLC
infix 1 |-

var :: Index gam a -> (gam |- a)
var x = base $ VAR x

lam :: (a :< gam |- b) -> (gam |- a :-> b)
lam e = only e ==> LAM

nat :: Nat n -> (gam |- Natural)
nat n = base $ NAT n

(.+) :: (gam |- Natural) -> (gam |- Natural) -> (gam |- Natural)
x .+ y = x *: y ==> ADD
infixr 5 .+

(.@) :: (gam |- a :-> b) -> (gam |- a) -> (gam |- b)
f .@ x = f *: x ==> APP
infixl 8 .@

instance Eval STLC Val where
  eval = viewDeriv >>> \case
    rule :$ subs -> case (rule,subs) of
      (NAT n,_)            -> \_ -> Nat n
      (VAR x,_)            -> index x
      (ADD  ,x :* y :* ØA) -> \gam -> case (eval x gam, eval y gam) of
        (Nat x',Nat y')  -> Nat $ x' N..+ y'
      (LAM  ,e :* ØA)      -> \gam -> Clos $ \a -> eval e (a :< gam)
      (APP  ,f :* x :* ØA) -> \gam -> case eval f gam of
        Clos g -> g $ eval x gam
      _ -> error "impossible"

e0 = lam $ lam $ var (IS IZ) .@ var IZ
e1 = lam $ var IZ .+ var IZ
e2 = nat $ S_ $ S_ $ Z_
e3 = e1 .@ e2

