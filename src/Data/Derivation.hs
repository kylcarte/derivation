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
import Type.Class.Higher    as Exports (Functor1(..))
import Type.Family.List     as Exports
import Type.Family.Tuple    as Exports hiding
  ( type (<$>)
  , type (<*>)
  , type (<&>)
  )

newtype Deriv rule gam a = Deriv
  { viewStep :: Step rule (Deriv rule) gam a
  }

data Step (rule :: [(k,l)] -> k -> l -> *) (deriv :: k -> l -> *) :: k -> l -> * where
  (:$) :: !(rule subs gam a)
       -> !(Args deriv subs)
       -> Step rule deriv gam a
infix 1 :$

type Args d = Prod (Uncur d)

mapRules ::
  (forall s g x. r1 s g x -> r2 s g x)
  -> Deriv r1 gam a
  -> Deriv r2 gam a
mapRules f (Deriv (r :$ args)) = Deriv $ f r :$ mapArgs (mapRules f) args

induction ::
  (forall s g x. r1 s g x -> Args (Deriv r2) s -> Deriv r2 g x)
  -> Deriv r1 gam a
  -> Deriv r2 gam a
induction f (Deriv (r :$ subs)) = f r $ mapArgs (induction f) subs

base :: rule Ø gam a -> Deriv rule gam a
base = ($$ Ø)

($$) :: rule subs gam a -> Args (Deriv rule) subs -> Deriv rule gam a
r $$ subs = Deriv $ r :$ subs
infix 1 $$

(==>) :: Args (Deriv rule) subs -> rule subs gam a -> Deriv rule gam a
subs ==> rule = Deriv $ rule :$ subs
infixl 1 ==>

mapArgs :: (forall a b. r a b -> s a b) -> Args r ps -> Args s ps
mapArgs f = map1 $ \(Uncur a) -> Uncur $ f a

class WeakenAdmissible r where
  weakenRule :: Deriv r gam a -> Deriv r (b :< gam) a

class CutAdmissible r where
  cutRule :: Deriv r gam a -> Deriv r (a :< gam) b -> Deriv r gam b

class ContractionAdmissible r where
  contractRule :: Deriv r (a :< a :< gam) b -> Deriv r (a :< gam) b

class ExchangeAdmissible r where
  exchangeRule :: Deriv r (a :< b :< gam) c -> Deriv r (b :< a :< gam) c

