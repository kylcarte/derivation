{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
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

module Data.Derivation
  ( module Data.Derivation
  , module Exports
  ) where

import Data.Type.Combinator as Exports (Uncur(..))
import Data.Type.Product    as Exports
import Data.Type.Index      as Exports
import Type.Class.HFunctor  as Exports (HFunctor(..))
import Type.Family.List     as Exports
import Type.Family.Tuple    as Exports hiding
  ( type (<$>)
  , type (<*>)
  , type (<&>)
  )

newtype Derivation rule gam a = Derivation
  { viewDeriv :: Deriv rule (Derivation rule) gam a
  }

data Deriv (rule :: [(k,l)] -> k -> l -> *) (deriv :: k -> l -> *) :: k -> l -> * where
  (:$) :: !(rule subs gam a)
       -> !(Args deriv subs)
       -> Deriv rule deriv gam a
infix 1 :$

type Args d = Prod (Uncur d)

mapRules ::
  (forall s g x. r1 s g x -> r2 s g x)
  -> Derivation r1 gam a
  -> Derivation r2 gam a
mapRules f (Derivation (r :$ args)) = Derivation $ f r :$ mapArgs (mapRules f) args

induction ::
  (forall s g x. r1 s g x -> Args (Derivation r2) s -> Derivation r2 g x)
  -> Derivation r1 gam a
  -> Derivation r2 gam a
induction f (Derivation (r :$ subs)) = f r $ mapArgs (induction f) subs

base :: rule Ø gam a -> Derivation rule gam a
base = ($$ Ø)

($$) :: rule subs gam a -> Args (Derivation rule) subs -> Derivation rule gam a
r $$ subs = Derivation $ r :$ subs
infix 1 $$

(==>) :: Args (Derivation rule) subs -> rule subs gam a -> Derivation rule gam a
subs ==> rule = Derivation $ rule :$ subs
infixl 1 ==>

mapArgs :: (forall a b. r a b -> s a b) -> Args r ps -> Args s ps
mapArgs f = map' $ \(Uncur a) -> Uncur $ f a

class WeakenAdmissible r where
  weakenRule :: Derivation r gam a -> Derivation r (b :< gam) a

class CutAdmissible r where
  cutRule :: Derivation r gam a -> Derivation r (a :< gam) b -> Derivation r gam b

class ContractionAdmissible r where
  contractRule :: Derivation r (a :< a :< gam) b -> Derivation r (a :< gam) b

class ExchangeAdmissible r where
  exchangeRule :: Derivation r (a :< b :< gam) c -> Derivation r (b :< a :< gam) c

