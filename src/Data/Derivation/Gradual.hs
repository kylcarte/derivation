{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
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

module Data.Derivation.Gradual where

import Data.Derivation
-- import Data.Type.Nat
-- import Type.Family.Nat
import Type.Family.Constraint
import Type.Family.Maybe

data Ty  g
  = G g
  | Ty g :-> Ty g
  | D
  deriving (Eq,Ord,Show)
infixr 4 :->

data Lit :: * -> * where
  Bool :: Bool
       -> Lit Bool
  Int  :: Int
       -> Lit Int

data Type (ground :: g -> *) :: Ty g -> * where
  Ground :: !(ground t)
         -> Type ground (G t)
  Arr    :: !(Type ground a)
         -> !(Type ground b)
         -> Type ground (a :-> b)
  Dyn    :: Type ground D

type GType = Type Lit

data Gradual (c :: g -> *) :: [([Maybe (Ty g)],Ty g)] -> [Maybe (Ty g)] -> Ty g -> * where
  Const :: !(c a)
        -> Gradual c '[] gam (G a)
  Var   :: !(Index gam (Just a))
        -> Gradual c '[] gam a
  Lam   :: Gradual c '[ (Just a & gam) # b ] gam (a :-> b)
  App1  :: Gradual c '[ gam # D , gam # a ] gam D
  App2  :: !(Consistent a a')
        -> Gradual c '[ gam # (a :-> b) , gam # a' ] gam b

type family App (a :: Ty g) :: Ty g where
  App D         = D
  App (a :-> b) = b

data Consistent :: Ty g -> Ty g -> * where
  CRefl :: Consistent t t
  CFun  :: !(Consistent s s')
        -> !(Consistent t t')
        -> Consistent (s :-> t) (s' :-> t')
  CUnL  :: Consistent D t
  CUnR  :: Consistent t D

type (|-) = Derivation (Gradual Lit)
infix 1 |-

type (~~) = Consistent
infix 2 ~~

lit :: Lit a -> (gam |- G a)
lit l = base $ Const l

var :: Index gam (Just a) -> (gam |- a)
var x = base $ Var x

lam :: (Just a & gam |- b) -> (gam |- a :-> b)
lam e = only e ==> Lam

{-
app :: 
-}

