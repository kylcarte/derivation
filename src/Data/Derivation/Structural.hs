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

module Data.Derivation.Structural where

import Data.Derivation

data Weaken (rule :: [([k],l)] -> [k] -> l -> *) :: [([k],l)] -> [k] -> l -> * where
  Weaken :: (forall x. Index del x -> Index gam x)
         -> Weaken rule '[ del # a ] gam a
  Unweak :: !(rule args gam a)
         -> Weaken rule args gam a

weaken :: (forall x. Index del x -> Index gam x)
       -> Derivation (Weaken rule) del a
       -> Derivation (Weaken rule) gam a
weaken sub d = only d ==> Weaken sub

unweak :: Derivation rule gam a
       -> Derivation (Weaken rule) gam a
unweak = mapDeriv Unweak

data Exchange (rule :: [([k],l)] -> [k] -> l -> *) :: [([k],l)] -> [k] -> l -> * where
  Exchange :: Exchange rule '[ (b & a & gam) # c ] (a & b & gam) c
  Unexc    :: !(rule args gam a)
           -> Exchange rule args gam a

data Contraction (rule :: [([k],l)] -> [k] -> l -> *) :: [([k],l)] -> [k] -> l -> * where
  Contraction :: Contraction rule '[ (a & gam) # b ] (a & a & gam) b
  Uncon       :: !(rule args gam a)
              -> Contraction rule args gam a

