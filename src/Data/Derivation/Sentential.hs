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

module Data.Derivation.Sentential where

import Data.Type.Bool
import Data.Type.Combinator
import Data.Type.Conjunction
import Data.Type.Product
import Data.Type.Sum
import Data.Type.Quantifier
import Type.Family.List

data Sent a
  = At a
  | Neg (Sent a)
  | Disj (Sent a) (Sent a)
  | Conj (Sent a) (Sent a)
  | Cond (Sent a) (Sent a)
  deriving (Eq,Ord,Show)

type (/\) = Conj
type (\/) = Disj
type (~>) = Cond
infixr 3 /\
infixr 2 \/
infixr 1 ~>

data Sentence (at :: k -> *) :: Sent k -> * where
  At_   :: !(at a)
        -> Sentence at (At a)
  Neg_  :: !(Sentence at a)
        -> Sentence at (Neg a)
  Conj_ :: !(Sentence at a)
        -> !(Sentence at b)
        -> Sentence at (Conj a b)
  Disj_ :: !(Sentence at a)
        -> !(Sentence at b)
        -> Sentence at (Disj a b)
  Cond_ :: !(Sentence at a)
        -> !(Sentence at b)
        -> Sentence at (Cond a b)

type family Cross (as :: [[k]]) (bs :: [[k]]) :: [[k]] where
  Cross  Ø              bs  = Ø
  Cross (a :< as)  Ø        = Ø
  Cross (a :< as) (b :< bs) = (a ++ b) :< Cross as (b :< bs)

type family DecideSent (a :: Sent k) (r :: Bool) :: [[(k,Bool)]] where
  DecideSent (At a)     r     = '[ '[ '(a,r) ] ]
  DecideSent (Neg a)    r     = DecideSent a (Not r)
  DecideSent (Conj a b) True  = Cross (DecideSent a True) (DecideSent b True)
  DecideSent (Conj a b) False = DecideSent a False ++ DecideSent b False
  DecideSent (Disj a b) True  = DecideSent a True ++ DecideSent b True
  DecideSent (Disj a b) False = Cross (DecideSent a False) (DecideSent b False)
  DecideSent (Cond a b) True  = DecideSent a False ++ DecideSent b True
  DecideSent (Cond a b) False = Cross (DecideSent a True) (DecideSent b False)

type Dec (d :: k -> Bool -> *) = Sum (Prod (Uncur d))

data B :: Bool -> * where
  True_  :: B True
  False_ :: B False

cross :: Sum (Prod f) as -> Sum (Prod f) bs -> Sum (Prod f) (Cross as bs)
cross = \case
  InL x -> undefined
  InR x -> undefined

{-
decide :: (forall x. at x -> Some (B :&: d x)) -> Sentence at a -> Either (Dec d (DecideSent a True)) (Dec d (DecideSent a False))
decide dec = \case
  At_   a   -> dec a >>- \(r :&: d) -> case r of
    True_  -> Left  $ InL $ Uncur d :< Ø
    False_ -> Right $ InL $ Uncur d :< Ø
  Neg_  a   -> case decide dec a of
    Left  d -> Right d
    Right d -> Left  d
  Conj_ a b -> case (decide dec a,decide dec b) of
    (Left d1,Left d2) -> Left _
  Disj_ a b -> undefined
  Cond_ a b -> undefined
-}

