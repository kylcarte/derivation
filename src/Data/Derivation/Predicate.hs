{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

module Data.Derivation.Predicate where

import Data.Type.Nat hiding (nat,(.+),(.*))
import Data.Type.Nat.Quote
import Data.Type.Product
import Type.Class.HFunctor (map')
import Type.Class.Witness hiding (type (==))
import Type.Family.Constraint
import Type.Family.List
import Type.Family.Nat hiding (type (+),type (*),type (==))

data P p f
  = Pr p [T f]
  | Neg  (P p f)
  | Conj (P p f) (P p f)
  | Disj (P p f) (P p f)
  | Cond (P p f) (P p f)
  | Bic  (P p f) (P p f)
  | Uni  (P p f)
  | Exi  (P p f)
  deriving (Eq,Ord,Show)

data T a
  = F a [T a]
  | B N
  deriving (Eq,Ord,Show)

data Fin :: N -> N -> * where
  FZ :: Fin (S x) Z
  FS :: !(Fin x y)
     -> Fin (S x) (s y)

data Term (f :: k -> N -> *) :: N -> T k -> * where
  Bound :: !(Fin n x)
        -> Term f n (B x)
  Free  :: HasLength as x
        => !(f a x)
        -> !(Terms f n as)
        -> Term f n (F a as)

class    (CheckLength as n, InferLength as n) => HasLength (as :: [k]) n
instance (CheckLength as n, InferLength as n) => HasLength (as :: [k]) n

class ChkLenC as n => CheckLength (as :: [k]) (n :: N) where
  type ChkLenC as n :: Constraint

instance (as ~ Ø) => CheckLength as Z where
  type ChkLenC as Z = (as ~ Ø)

instance (as ~ (a :< as'),CheckLength as' n) => CheckLength as (S n) where
  type ChkLenC as (S n) = (IsCons as, CheckLength (Tail as) n)

class InfLenC as n => InferLength (as :: [k]) (n :: N) | as -> n where
  type InfLenC as n :: Constraint

instance InferLength Ø Z where
  type InfLenC Ø Z = ØC

instance (n ~ S n', InferLength as n') => InferLength (a :< as) n where
  type InfLenC (a :< as) n = (n ~ S (Pred n), InferLength as (Pred n))

type Terms f n = Prod (Term f n)

data Exp (p :: l -> [T k] -> *) (f :: k -> N -> *) :: N -> P l k -> * where
  Pred   :: !(p b as)
         -> !(Terms f n as)
         -> Exp p f n (Pr b as)
  Forall :: !(Exp p f (S n) a)
         -> Exp p f n (Uni a)
  Exists :: !(Exp p f (S n) a)
         -> Exp p f n (Exi a)
  Not    :: !(Exp p f n a)
         -> Exp p f n (Neg a)
  (:&:)  :: !(Exp p f n a)
         -> !(Exp p f n b)
         -> Exp p f n (Conj a b)
  (:|:)  :: !(Exp p f n a)
         -> !(Exp p f n b)
         -> Exp p f n (Disj a b)
  (:->)  :: !(Exp p f n a)
         -> !(Exp p f n b)
         -> Exp p f n (Cond a b)
infixr 3 :&:
infixr 2 :|:
infixr 1 :->

type x <  y = Pr LT '[x,y]
type x == y = Pr EQ '[x,y]
type x >  y = Pr GT '[x,y]
infix 4 <, ==, >

data NatC
  = Plus
  | Times
  | Zero
  | Succ
  deriving (Eq,Ord,Show)

type x + y = F Plus  '[x,y]
type x * y = F Times '[x,y]
infixl 6 +
infixl 7 *

data NatCon :: NatC -> N -> * where
  Add :: NatCon Plus  [n|2|]
  Mul :: NatCon Times [n|2|]
  NZ  :: NatCon Zero  [n|0|]
  NS  :: NatCon Succ  [n|1|]

data NatPred :: Ordering -> [T NatC] -> * where
  Less  :: NatPred LT '[x,y]
  Equal :: NatPred EQ '[x,y]
  More  :: NatPred GT '[x,y]

type NatT  = Term NatCon
type NatE  = Exp NatPred NatCon
type NatT' = NatT Z
type NatE' = NatE Z

(.+) :: NatT xs x -> NatT xs y -> NatT xs (x + y)
x .+ y = Free Add $ x :< y :< Ø
infixl 6 .+

(.*) :: NatT xs x -> NatT xs y -> NatT xs (x * y)
x .* y = Free Mul $ x :< y :< Ø
infixl 7 .*

(.<) :: NatT xs x -> NatT xs y -> NatE xs (x < y)
x .< y = Pred Less $ x :< y :< Ø
infix 4 .<

(.=) :: NatT xs x -> NatT xs y -> NatE xs (x == y)
x .= y = Pred Equal $ x :< y :< Ø
infix 4 .=

(.>) :: NatT xs x -> NatT xs y -> NatE xs (x > y)
x .> y = Pred More $ x :< y :< Ø
infix 4 .>

type f $ x = f x
infixr 0 $

{-
addClosure :: NatE' $ Uni $ Uni $ Exi $ B [n|0|] == B [n|2|] + B [n|1|]
addClosure = Forall $ Forall $ Exists $ Bound [n|0|] .= Bound [n|2|] .+ Bound [n|1|]

mulClosure :: NatE' $ Uni $ Uni $ Exi $ B [n|0|] == B [n|2|] * B [n|1|]
mulClosure = Forall $ Forall $ Exists $ Bound [n|0|] .= Bound [n|2|] .* Bound [n|1|]
-}

type family SubstT (n :: N) (t :: T k) (u :: T k) :: T k where
  SubstT n t (F o as) = F o (SubstTs n t as)
  SubstT n t (B n)    = t
  SubstT n t (B m)    = B m

substT :: Nat x -> Term f n t -> Term f n u -> Term f n (SubstT x t u)
substT x t = \case
  Free f us -> Free f $ substTs x t us

substTs :: Nat x -> Term f n t -> Terms f n us -> Terms f n (SubstTs x t us)
substTs x t = \case
  Ø       -> Ø
  u :< us -> substT x t u :< substTs x t us

weakenFin :: Fin n x -> Fin (S n) x
weakenFin = \case
  FZ   -> FZ
  FS n -> FS $ weakenFin n

weaken1 :: Term f n t -> Term f (S n) t
weaken1 = \case
  Bound n    -> Bound  $ weakenFin n
  Free  f as -> Free f $ map' weaken1 as

type family SubstTs (n :: N) (t :: T k) (us :: [T k]) :: [T k] where
  SubstTs n t Ø         = Ø
  SubstTs n t (u :< us) = SubstT n t u :< SubstTs n t us

type family Subst (n :: N) (t :: T k) (p :: P l k) :: P l k where
  Subst n t (Pr r ts)  = Pr r (SubstTs n t ts)
  Subst n t (Neg  p)   = Neg (Subst n t p)
  Subst n t (Conj p q) = Conj (Subst n t p) (Subst n t q)
  Subst n t (Disj p q) = Disj (Subst n t p) (Subst n t q)
  Subst n t (Cond p q) = Cond (Subst n t p) (Subst n t q)
  Subst n t (Bic  p q) = Bic  (Subst n t p) (Subst n t q)
  Subst n t (Uni  p)   = Uni (Subst (S n) t p)
  Subst n t (Exi  p)   = Exi (Subst (S n) t p)

-- Indexes {{{

type IsCons as = (as ~ (Head as :< Tail as))

type family Head (as :: [k]) :: k where
  Head (a :< as) = a

type family Tail (as :: [k]) :: [k] where
  Tail (a :< as) = as

class IxC as n a => Indexes (as :: [k]) (n :: N) (a :: k) | as n -> a where
  type IxC as n a :: Constraint
  (!) :: Prod f as -> Nat n -> f a
infix 4 !

instance (as ~ (a :< as')) => Indexes as Z a where
  type IxC as Z a = (IsCons as, a ~ Head as)
  as ! _ = head' as

instance (as ~ (b :< as'), Indexes as' n a) => Indexes as (S n) a where
  type IxC as (S n) a = (IsCons as, Indexes (Tail as) n a)
  as ! (S_ n) = tail' as ! n

-- }}}

