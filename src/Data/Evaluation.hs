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

module Data.Evaluation where

import Data.Derivation

import Prelude hiding (init)

class Eval (rule :: [([k],k)] -> [k] -> k -> *) (val :: k -> *) | rule -> val, val -> rule where
  eval :: Deriv rule gam a -> Prod val gam -> val a

eval_ :: Eval rule val => Deriv rule Ø a -> val a
eval_ = flip eval Ø

data Steps :: (k -> k -> *) -> k -> k -> * where
  Done :: Steps step a a
  (:>) :: step a b -> Steps step b c -> Steps step a c
infixr 5 :>

data FST a
data SND a

{-
data Small :: [(*,*)] -> * -> * -> * where
  FST  :: Small '[] (FST (a,b)) a
  SND  :: Small '[] (SND (a,b)) b
  PAIR :: Small '[a#a',b#b'] (a,b) (a',b')
-}

-- data Evaluation step 

