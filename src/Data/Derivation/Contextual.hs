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

module Data.Derivation.Contextual where

import Data.Derivation

data Ty a
  = C a
  | Ty a :-> Ty a
  | Ty a :@ [Ty a]
  deriving (Eq,Ord,Show)
infixr 3 :->
infixl 2 :@

data Subst :: [Ty k] -> *

data J a
  = ([Ty a],[Ty a]) ::: (Ty a)
  | ([Ty a],[Ty a]) ::/ [Ty a]
infix 1 :::
infix 1 ::/

data ModalType :: [J k] -> [Ty k] -> [Ty k] -> Ty k -> * where
  Hyp    :: !(Index γ a)
         -> ModalType '[]
                       -----
                       δ γ a
  ----
  CtxHyp :: !(Index δ a)
         -> ModalType '[ δ # γ ::/ bs ]
                       ----------------
                       δ γ a
  ----
  ArrI   :: ModalType '[ δ # (a :< γ) ::: b ]
                       ----------------------
                       δ γ (a :-> b)
  ----
  ArrE   :: ModalType '[ δ # γ ::: a :-> b , δ # γ ::: a ]
                       -----------------------------------
                       δ γ b
  ----
  CtxI   :: ModalType '[ δ # ψ ::: a ]
                       ---------------
                       δ γ (a :@ ψ)
  ----
  CtxE   :: ModalType '[ δ # γ ::: a :@ ψ , ((a :@ ψ) :< δ) # γ ::: b ]
                       ------------------------------------------------
                       δ γ b
                       

data ModalSubst :: [J k] -> [Ty k] -> [Ty k] -> [Ty k] -> * where

data Modal :: [J k] -> J k -> * where
  HasType   :: !(ModalType as δ γ a)
            -> Modal as (δ#γ ::: a)
  SubstType :: !(ModalSubst as δ γ bs)
            -> Modal as (δ#γ ::/ bs)

{-
data Subset (p :: k -> l -> *) :: [k] -> [l] -> * where
  ØS   :: Subset p Ø Ø
  (:+) :: !(p a b)
       -> !(Subset p as bs)
       -> Subset p (a :< as) (b :< bs)
  Skip :: !(Subset p as bs)
       -> Subset p (a :< as) bs
infixr 5 :+

mapSub :: (forall x y. p x y -> q x y) -> Subset p as bs -> Subset q as bs
mapSub f = \case
  ØS     -> ØS
  Skip s -> Skip $ mapSub f s
  a :+ s -> f a :+ mapSub f s

mapProd :: (forall x y. p x y -> f x -> g y) -> Subset p as bs -> Prod f as -> Prod g bs
mapProd f = \case
  ØS     -> \_ -> Ø
  Skip s -> mapProd f s . tail'
  a :+ s -> uncurry' $ \x -> (f a x :<) . mapProd f s

foo :: Subset (->) '[a,b,c] '[d -> b,c]
foo = Skip $ const :+ id :+ ØS

bar :: Prod I '[a,b,c] -> Prod I '[d -> b,c]
bar = mapProd (\f -> I . f . getI) foo
-}

{-
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
  LAM :: STLC '[ '(a & gam,b) ]                    gam  (a :-> b)
  APP :: STLC '[ '(gam,a :-> b) , '(gam,a) ]       gam   b

type (|-) = Derivation STLC
infix 1 |-

var :: Index gam a -> (gam |- a)
var x = base $ VAR x

lam :: (a & gam |- b) -> (gam |- a :-> b)
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
-}

