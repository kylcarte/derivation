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

import Data.Type.Nat
import Data.Type.Nat.Quote
import Data.Type.Product
-- import Type.Class.Witness (Dec(..))
import Type.Family.List
import Type.Family.Nat
import Type.Family.Tuple
import Data.Void

data Snt a
  = At a
  | Not (Snt a)
  | Conj (Snt a) (Snt a)
  | Disj (Snt a) (Snt a)
  | Cond (Snt a) (Snt a)
  deriving (Eq,Ord,Show)

type (&&) = Conj
type (||) = Disj
type (~>) = Cond
infixr 3 &&
infixr 2 ||
infixr 1 ~>

data Sent (at :: k -> *) :: Snt k -> * where
  Atom  :: !(at a)
        -> Sent at (At a)
  Neg   :: !(Sent at p)
        -> Sent at (Not p)
  (:&)  :: !(Sent at p)
        -> !(Sent at q)
        -> Sent at (Conj p q)
  (:|)  :: !(Sent at p)
        -> !(Sent at q)
        -> Sent at (Disj p q)
  (:->) :: !(Sent at p)
        -> !(Sent at q)
        -> Sent at (Cond p q)
infixr 3 :&
infixr 2 :|
infixr 1 :->

data VProd (f :: k -> *) :: N -> [k] -> * where
  Nil  :: VProd f Z Ø
  (:%) :: !(f a)
       -> !(VProd f n as)
       -> VProd f (S n) (a :< as)
infixr 5 :%

toProd :: VProd f n as -> Prod f as
toProd = \case
  Nil     -> Ø
  a :% as -> a :< toProd as

data Atomic (p :: pred -> N -> *) (t :: k -> *) :: (pred,[k]) -> * where
  A :: !(p r n)
    -> !(VProd t n as)
    -> Atomic p t (r#as)

data Form (p :: pred -> N -> *) (t :: k -> *) :: Snt (pred,[k]) -> * where
  Form :: !(Sent (Atomic p t) a)
       -> Form p t a

type family DecideA (t :: k -> *) (p :: pred) (as :: [k]) :: *

type family DecideS (t :: k -> *) (s :: Snt (pred,[k])) :: * where
  DecideS t (At a)     = DecideA t (Fst a) (Snd a)
  DecideS t (Not p)    = DecideS t p -> Void
  DecideS t (Conj p q) = (DecideS t p,DecideS t q)
  DecideS t (Disj p q) = Either (DecideS t p) (DecideS t q)
  -- DecideS t (Cond p q) = DecideS t p -> DecideS t q
  DecideS t (Cond p q) = DecideS t (Disj (Not p) q)

class DecideAtom (t :: k -> *) (p :: pred -> N -> *) where
  decideAtom :: p r n -> VProd t n as -> Dec (DecideA t r as)

decideSent :: DecideAtom t p => Sent (Atomic p t) a -> Dec (DecideS t a)
decideSent = \case
  Atom (A p as) -> decideAtom p as
  Neg p         -> case decideSent p of
    Proven  a -> Refuted "negation" $ \k -> k a
    Refuted _ j -> Proven j
  p :& q        -> case (decideSent p, decideSent q) of
    (Proven  a  ,Proven  b  ) -> Proven (a,b)
    (Refuted e j,_          ) -> Refuted e $ \(a,_) -> j a
    (_          ,Refuted e k) -> Refuted e $ \(_,b) -> k b
  p :| q        -> case (decideSent p, decideSent q) of
    (Refuted e1 j,Refuted e2 k) -> Refuted (e1 ++ "\n" ++ e2) $ \case
      Left  a -> j a
      Right b -> k b
    (Proven  a,_        ) -> Proven $ Left  a
    (_        ,Proven  b) -> Proven $ Right b
  p :-> q       -> case (decideSent p, decideSent q) of
    (Proven  a,Refuted e k) -> Refuted ("conditional: " ++ e) $ \case
      Left  j -> j a
      Right b -> k b
    (_        ,Proven  b) -> Proven  $ Right b
    (Refuted _ j,_        ) -> Proven  $ Left  j
  -- p :-> q       -> case (decideSent p, decideSent q) of
  --   (Proven  a,Refuted k) -> Refuted $ \l -> k $ l a
  --   (_        ,Proven  b) -> Proven  $ \_ -> b
  --   (Refuted j,_        ) -> Proven  $ absurd . j

type instance DecideA Nat (o :: Ordering) '[x,y] = NatIneq o x y

decideLess :: Nat x -> Nat y -> Dec (NatIneq LT x y)
decideLess = \case
  Z_ -> \case
    Z_   -> Refuted "!(Z < Z)" $ \case
    S_ y -> Proven  $ LTZero $ S_ y
  S_ x -> \case
    Z_   -> Refuted "!(S x < Z)" $ \case
    S_ y -> case decideLess x y of
      Proven  l -> Proven  $ LTSucc l
      Refuted e k -> Refuted e $ \(LTSucc l) -> k l

decideEqual :: Nat x -> Nat y -> Dec (NatIneq EQ x y)
decideEqual = \case
  Z_   -> \case
    Z_   -> Proven  EQZero
    S_ _ -> Refuted "!(Z = S y)" $ \case
  S_ x -> \case
    Z_   -> Refuted "!(S x = Z)" $ \case
    S_ y -> case decideEqual x y of
      Proven  l -> Proven  $ EQSucc l
      Refuted e k -> Refuted e $ \(EQSucc l) -> k l

decideMore :: Nat x -> Nat y -> Dec (NatIneq GT x y)
decideMore = \case
  Z_   -> \_ -> Refuted "!(Z > y)" $ \case
  S_ x -> \case
    Z_   -> Proven $ GTZero $ S_ x
    S_ y -> case decideMore x y of
      Proven  l -> Proven  $ GTSucc l
      Refuted e k -> Refuted e $ \(GTSucc l) -> k l

data family NatIneq (o :: Ordering) :: N -> N -> *

data instance NatIneq LT x y where
  LTZero :: !(Nat (S y))
         -> NatIneq LT Z (S y)
  LTSucc :: !(NatIneq LT x y)
         -> NatIneq LT (S x) (S y)

data instance NatIneq EQ x y where
  EQZero :: NatIneq EQ Z Z
  EQSucc :: !(NatIneq EQ x y)
         -> NatIneq EQ (S x) (S y)

data instance NatIneq GT x y where
  GTZero :: !(Nat (S x))
         -> NatIneq GT (S x) Z
  GTSucc :: !(NatIneq GT x y)
         -> NatIneq GT (S x) (S y)

deriving instance Show (NatIneq LT x y) 
deriving instance Show (NatIneq EQ x y) 
deriving instance Show (NatIneq GT x y) 

instance DecideAtom Nat Inequality where
  decideAtom = \case
    Less  -> \(x :% y :% Nil) -> decideLess  x y
    Equal -> \(x :% y :% Nil) -> decideEqual x y
    More  -> \(x :% y :% Nil) -> decideMore  x y

data Inequality :: Ordering -> N -> * where
  Less  :: Inequality LT [qN|2|]
  Equal :: Inequality EQ [qN|2|]
  More  :: Inequality GT [qN|2|]

{-
-- Arith {{{

data Ar
  = Val N
  | Add Ar Ar
  | Mul Ar Ar
  deriving (Eq,Ord,Show)

data Arith :: Ar -> * where
  Nat   :: !(Nat n) -> Arith (Val n)
  Plus  :: !(Arith x)
        -> !(Arith y)
        -> Arith (Add x y)
  Times :: !(Arith x)
        -> !(Arith y)
        -> Arith (Mul x y)

type family Eval (e :: Ar) :: N where
  Eval (Val x)   = x
  Eval (Add x y) = Eval x + Eval y
  Eval (Mul x y) = Eval x * Eval y

eval :: Arith e -> Nat (Eval e)
eval = \case
  Nat   x   -> x
  Plus  x y -> eval x .+ eval y
  Times x y -> eval x .* eval y

-- }}}
-}

type x .<. y = At (LT # '[x,y])
type x .=. y = At (EQ # '[x,y])
type x .>. y = At (GT # '[x,y])

(.<.) :: n x -> n y -> Form Inequality n (x .<. y)
x .<. y = atom Less $ x :% y :% Nil
(.=.) :: n x -> n y -> Form Inequality n (x .=. y)
x .=. y = atom Equal $ x :% y :% Nil
(.>.) :: n x -> n y -> Form Inequality n (x .>. y)
x .>. y = atom More $ x :% y :% Nil
infix 4 .<., .=., .>.

atom :: p r n -> VProd t n as -> Form p t (At (r # as))
atom p as = Form $ Atom $ A p as
neg :: Form p t a -> Form p t (Not a)
neg (Form a) = Form $ Neg a
(.&.) :: Form p t a -> Form p t b -> Form p t (Conj a b)
Form a .&. Form b = Form $ a :& b
(.|.) :: Form p t a -> Form p t b -> Form p t (Disj a b)
Form a .|. Form b = Form $ a :| b
(.->) :: Form p t a -> Form p t b -> Form p t (Cond a b)
Form a .-> Form b = Form $ a :-> b
infixr 3 .&.
infixr 2 .|.
infixr 1 .->

type Exp = Form Inequality Nat

-- e0 :: Nat x -> Nat y -> Exp (x .<. y || y .<. x)
exp0 x y = x .<. y .|. y .<. x

-- e1 :: Nat x -> Nat y -> Nat z -> Exp (x .<. y ~> y .<. z ~> x .<. z)
exp1 x y z = x .<. y .-> y .<. z .-> x .<. z

data Dec a
  = Proven a
  | Refuted String (a -> Void)

display :: Show a => Dec a -> IO ()
display = \case
  Proven a    -> putStrLn $ "success: " ++ show a
  Refuted e _ -> putStrLn $ "failure: " ++ e

decide :: DecideAtom t p => Form p t a -> Dec (DecideS t a)
decide (Form s) = decideSent s

decide_ :: (DecideAtom t p, Show (DecideS t a)) => Form p t a -> IO ()
decide_ = display . decide

