{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

module Data.Derivation.Simple where

import Data.Type.Fin.Indexed
import Data.Type.Nat
import Data.Type.Sym
import Data.Type.Sym.Quote
import Type.Class.Higher
import Type.Class.Known
import Type.Class.Witness hiding (forall)
import Type.Family.Constraint
import Type.Family.Nat
import Data.Type.Bool (type If)
import Data.Type.Equality (type (==))

-- E {{{

data E a
  = V N
  | A a
  | Neg   (E a) 
  | Conj  (E a) (E a)
  | Disj  (E a) (E a)
  | Cond  (E a) (E a)
  | Uni N (E a) 
  | Exi N (E a) 
  deriving (Eq,Ord,Show)

type (/\) = Conj
type (\/) = Conj
type (~>) = Cond
infixr 3 /\
infixr 2 \/
infixr 1 ~>

-- }}}

-- Valid {{{

data Exp (at :: k -> *) :: N -> E k -> * where
  Var    :: !(IFin n x)
         -> Exp at n (V x)
  Atom   :: !(at a)
         -> Exp at n (A a)
  Not    :: !(Exp at n a)
         -> Exp at n (Neg a)
  (:&:)  :: !(Exp at n a)
         -> !(Exp at n b)
         -> Exp at n (a /\ b)
  (:|:)  :: !(Exp at n a)
         -> !(Exp at n b)
         -> Exp at n (a \/ b)
  (:->)  :: !(Exp at n a)
         -> !(Exp at n b)
         -> Exp at n (a ~> b)
  Forall :: !(IFin n x)
         -> !(Exp at (S n) a)
         -> Exp at n (Uni x a)
  Exists :: !(IFin n x)
         -> !(Exp at (S n) a)
         -> Exp at n (Exi x a)
infixr 3 :&:
infixr 2 :|:
infixr 1 :->

instance Show1 at => Show (Exp at n a) where
  showsPrec d = \case
    Var x      -> showChar 'x'
                . shows (ifinVal x)
    Atom a     -> shows1 a
    Not e      -> showParen (d > 10)
      $ showString "¬ "
      . showsPrec 11 e
    e1 :&: e2  -> showParen (d > 3)
      $ showsPrec 4 e1
      . showString " ∧ "
      . showsPrec 3 e2
    e1 :|: e2  -> showParen (d > 2)
      $ showsPrec 3 e1
      . showString " ∨ "
      . showsPrec 2 e2
    e1 :-> e2  -> showParen (d > 1)
      $ showsPrec 2 e1
      . showString " → "
      . showsPrec 1 e2
    Forall x e -> showParen (d > 9)
      $ showString "∀x"
      . shows (ifinVal x)
      . showString "."
      . showsPrec 9 e
    Exists x e -> showParen (d > 9)
      $ showString "∃ x"
      . shows (ifinVal x)
      . showString ". "
      . showsPrec 9 e

-- }}}

-- Builders {{{

closed :: Exp at Z a -> Exp at Z a
closed = id

{-
forall :: Known Nat n => (IFin (S n) n -> Exp at (S n) a) -> Exp at n (Uni n a)
forall f = Forall known $ f ifinMax

exists :: Known Nat n => (IFin (S n) n -> Exp at (S n) a) -> Exp at n (Exi n a)
exists f = Exists known $ f ifinMax
-}

{-
instantiate :: Exp at n (Uni x e) -> Exp at (S n) t -> Exp at (S n) (Subst x t e)
instantiate (Forall x e) t = subst x t e
-}

ifinMax :: Known Nat x => IFin (S x) x
ifinMax = ifinMax' known

ifinMax' :: Nat x -> IFin (S x) x
ifinMax' = \case
  Z_   -> IFZ
  S_ x -> IFS $ ifinMax' x

var :: LessEq m n => IFin m x -> Exp at n (V x)
var = Var . liftIFin

-- }}}

type Closed f = f Z
type Term = Exp Sym

{-
eId = closed $
  forall $ \x ->
  Var x :-> Var x

eConst = closed $
  forall $ \x ->
  forall $ \y -> 
  var x :-> var y :-> var x
-}

foo = closed $ Atom [qS|A|] :&: Atom [qS|B|]

-- Weaken {{{

{-
type family Weaken (e :: E k) :: E k where
  Weaken (V x)        = V (S x)
  Weaken (A a)        = A a
  Weaken (Neg  e)     = Neg  (Weaken e)
  Weaken (Conj e1 e2) = Conj (Weaken e1) (Weaken e2)
  Weaken (Disj e1 e2) = Disj (Weaken e1) (Weaken e2)
  Weaken (Cond e1 e2) = Cond (Weaken e1) (Weaken e2)
  Weaken (Uni x e)    = Uni x (Weaken e)
  Weaken (Exi x e)    = Exi x (Weaken e)
-}

weakenExp :: Exp at n a -> Exp at (S n) a
weakenExp = \case
  Var  x     -> Var $ weaken x
  Atom a     -> Atom a
  Not  e     -> Not  (weakenExp e)
  e1 :&: e2 -> weakenExp e1 :&: weakenExp e2
  e1 :|: e2 -> weakenExp e1 :|: weakenExp e2
  e1 :-> e2 -> weakenExp e1 :-> weakenExp e2
  Forall x e -> Forall (weaken x) $ weakenExp e
  Exists x e -> Exists (weaken x) $ weakenExp e

-- }}}

-- Subst {{{

type family Subst (x :: N) (t :: E k) (e :: E k) :: E k where
  Subst x t (V y)        = If (x == y) t (V y)
  Subst x t (A a)        = A a
  Subst x t (Neg  e)     = Neg  (Subst x t e)
  Subst x t (Conj e1 e2) = Conj (Subst x t e1) (Subst x t e2)
  Subst x t (Disj e1 e2) = Disj (Subst x t e1) (Subst x t e2)
  Subst x t (Cond e1 e2) = Cond (Subst x t e1) (Subst x t e2)
  Subst x t (Uni y e)    = If (x == y)
                              (Uni y e)
                              (If (x < y)
                                  (Uni (Pred y) (Subst x t e))
                                  (Uni y (Subst x t e)))
  Subst x t (Exi y e)    = If (x == y)
                              (Exi y e)
                              (If (x < y)
                                  (Exi (Pred y) (Subst x t e))
                                  (Exi y (Subst x t e)))

{-
subst :: forall at x n t e. Nat x -> Exp at n t -> Exp at n e -> Exp at (Pred n) (Subst x t e)
subst x t = \case
  Var  y     -> undefined -- case natEq x (ifinNat y) of
    -- True_  -> t
    -- False_ -> Var y
  Atom a     -> Atom a
  Not  e     -> Not $ subst x t e
  e1 :&: e2 -> subst x t e1 :&: subst x t e2
  e1 :|: e2 -> subst x t e1 :|: subst x t e2
  e1 :-> e2 -> subst x t e1 :-> subst x t e2
  Forall (y :: IFin n y) (e :: Exp at (S n) a) -> case natCompare x (ifinNat y) of
    Left         lt  -> lt // (Forall (ifinPred lt _) undefined :: Exp at (Pred n) (Uni (Pred y) (Subst x t a)))
    Right (Left  eq) -> eq // e'
      where
      e' :: Exp at (Pred n) (Uni y a)
      e' = undefined
    Right (Right gt) -> gt // e'
      where
      e' :: Exp at (Pred n) (Uni y (Subst (S (Pred x)) t a))
      e' = undefined
  Exists y e -> undefined
-}


ifinPred :: NatLT x y -> IFin x y -> IFin (Pred x) (Pred y)
ifinPred = \case
  LTZ   -> absurd . ifinZ
  LTS _ -> \(IFS x) -> x

{-
  Exists y e -> case natEq x y of
    True_  -> Exists y e
    False_ -> Exists y $ subst x (weakenExp t) e
-}

-- }}}

-- Nat {In}Equality {{{

data B :: Bool -> * where
  True_  :: B True
  False_ :: B False

type family (x :: N) < (y :: N) :: Bool where
  Z   < Z   = False
  Z   < S y = True
  S x < Z   = False
  S x < S y = x < y
infix 4 <

type family (x :: N) > (y :: N) :: Bool where
  Z   > Z   = False
  Z   > S y = False
  S x > Z   = True
  S x > S y = x > y
infix 4 >

data NatLT :: N -> N -> * where
  LTZ :: NatLT Z (S y)
  LTS :: !(NatLT x y)
      -> NatLT (S x) (S y)

data NatEQ :: N -> N -> * where
  EQZ :: NatEQ Z Z
  EQS :: !(NatEQ x y)
      -> NatEQ (S x) (S y)

data NatGT :: N -> N -> * where
  GTZ :: NatGT (S x) Z
  GTS :: !(NatGT x y)
      -> NatGT (S x) (S y)

instance (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y), y' ~ Pred y) => Witness ØC (y ~ S y', Known Nat x, lt ~ True, eq ~ False, gt ~ False) (NatLT x y) where
  type WitnessC ØC (y ~ S y', Known Nat x, lt ~ True, eq ~ False, gt ~ False) (NatLT x y) = (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y), y' ~ Pred y)
  (\\) r = \case
    LTZ   -> r
    LTS l -> r \\ l

instance (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y)) => Witness ØC (Known Nat x, Known Nat y, lt ~ False, eq ~ True, gt ~ False) (NatEQ x y) where
  type WitnessC ØC (Known Nat x, Known Nat y, lt ~ False, eq ~ True, gt ~ False) (NatEQ x y) = (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y))
  (\\) r = \case
    EQZ   -> r
    EQS l -> r \\ l

instance (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y), x' ~ Pred x) => Witness ØC (x ~ S x', Known Nat y, lt ~ False, eq ~ False, gt ~ True) (NatGT x y) where
  type WitnessC ØC (x ~ S x', Known Nat y, lt ~ False, eq ~ False, gt ~ True) (NatGT x y) = (lt ~ (x < y), eq ~ (x == y), gt ~ (x > y), x' ~ Pred x)
  (\\) r = \case
    GTZ   -> r
    GTS l -> r \\ l

natCompare :: Nat x -> Nat y -> Either (NatLT x y) (Either (NatEQ x y) (NatGT x y))
natCompare = \case
  Z_   -> \case
    Z_   -> Right $ Left EQZ
    S_ y -> Left LTZ
  S_ x -> \case
    Z_   -> Right $ Right GTZ
    S_ y -> case natCompare x y of
      Left         lt  -> Left          $ LTS lt
      Right (Left  eq) -> Right $ Left  $ EQS eq
      Right (Right gt) -> Right $ Right $ GTS gt

-- }}}

