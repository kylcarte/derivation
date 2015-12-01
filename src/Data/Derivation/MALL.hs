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

module Data.Derivation.MALL where

import Data.Derivation

import Prelude hiding (init)
import Data.Void

data Modal a
  = Atom a
  | Not     (Modal a)
  | And     (Modal a) (Modal a)
  | Or      (Modal a) (Modal a)
  | Cond    (Modal a) (Modal a)
  | Square  (Modal a)
  | Diamond (Modal a)

data Model (acc :: k -> k -> *) (val :: k -> l -> *) :: k -> Modal l -> * where
  At     :: !(val x a)
         -> Model acc val x (Atom a)
  Neg    :: (Model acc val x a -> Void)
         -> Model acc val x (Not a)
  Conj   :: !(Model acc val x a)
         -> !(Model acc val x b)
         -> Model acc val x (And a b)
  Disj1  :: !(Model acc val x a)
         -> Model acc val x (Or a b)
  Disj2  :: !(Model acc val x b)
         -> Model acc val x (Or a b)
  Impl1  :: (Model acc val x a -> Void)
         -> Model acc val x (Cond a b)
  Impl2  :: !(Model acc val x b)
         -> Model acc val x (Cond a b)
  -- Strong :: (

-- MALL {{{

data Prop
  = Zero
  | One
  | Top
  | Bottom
  | Dual Prop
  | Times Prop Prop
  | Plus  Prop Prop
  | Par   Prop Prop
  | With  Prop Prop
  deriving (Eq,Ord,Show)

data MALL :: [([Prop],[Prop])] -> [Prop] -> [Prop] -> * where
  INIT    :: MALL '[]
                  --------
                  '[a] '[a]
  ----------------------------------------
  CUT     :: MALL '[ del # (a & gam) , (a & del') # gam' ]
                  --------
                   (del ++ del') (gam ++ gam')
  ----------------------------------------
  LDUAL   :: MALL '[ del # (a & gam) ]
                  --------
                   (Dual a & del) gam
  ----------------------------------------
  RDUAL   :: MALL '[ (a & del) # gam ]
                  --------
                   del (Dual a & gam)
  ----------------------------------------
  LONE    :: MALL '[ del # gam ]
                  --------
                   (One & del) gam
  ----------------------------------------
  RONE    :: MALL '[]
                  --------
                  '[] '[One]
  ----------------------------------------
  LTIMES  :: MALL '[ (a & b & del) # gam ]
                  --------
                   (Times a b & del) gam
  ----------------------------------------
  RTIMES  :: MALL '[ del # (a & gam) , del' # (b & gam') ]
                  --------
                   (del ++ del') (Times a b & gam ++ gam')
  ----------------------------------------
  LBOTTOM :: MALL '[]
                  --------
                   '[Bottom] '[]
  ----------------------------------------
  RBOTTOM :: MALL '[ del # gam ]
                  --------
                   del (Bottom & gam)
  ----------------------------------------
  LPAR    :: MALL '[ (a & del) # gam , (b & del') # gam' ]
                  --------
                   (Par a b & del ++ del') (gam ++ gam')
  ----------------------------------------
  RPAR    :: MALL '[ del # (a & b & gam) ]
                  --------
                   del (Par a b & gam)
  ----------------------------------------
  LZERO   :: MALL '[]
                  --------
                   (Zero & del) gam
  ----------------------------------------
  RTOP    :: MALL '[]
                  --------
                   del (Top & gam)
  ----------------------------------------
  LWITH1  :: MALL '[ (a & del) # gam ]
                  --------
                   (With a b & del) gam
  ----------------------------------------
  LWITH2  :: MALL '[ (b & del) # gam ]
                  --------
                   (With a b & del) gam
  ----------------------------------------
  RWITH   :: MALL '[ del # (a & gam) , del # (b & gam) ]
                  --------
                   del (With a b & gam)
  ----------------------------------------
  LPLUS   :: MALL '[ (a & del) # gam , (b & del) # gam ]
                  --------
                   (Plus a b & del) gam
  ----------------------------------------
  RPLUS1  :: MALL '[ del # (a & gam) ]
                  --------
                   del (Plus a b & gam)
  ----------------------------------------
  RPLUS2  :: MALL '[ del # (b & gam) ]
                  --------
                   del (Plus a b & gam)

type (|~) = Derivation MALL
infix 1 |~

init    ::  ('[a] |~ '[a])
init = base INIT

cut     ::  (del |~ a & gam) -> (a & del' |~ gam') -> (del ++ del' |~ gam ++ gam')
cut a b = a *: b ==> CUT

lDual   ::  (del |~ a & gam) -> (Dual a & del |~ gam)
lDual a = only a ==> LDUAL

rDual   ::  (a & del |~ gam) -> (del |~ Dual a & gam)
rDual a = only a ==> RDUAL

lOne    ::  (del |~ gam) -> (One & del |~ gam)
lOne a = only a ==> LONE

rOne    ::  ('[] |~ '[One])
rOne = base RONE

lTimes  ::  (a & b & del |~ gam) -> (Times a b & del |~ gam)
lTimes a = only a ==> LTIMES

rTimes  ::  (del |~ a & gam) -> (del' |~ b & gam') -> (del ++ del' |~ Times a b & gam ++ gam')
rTimes a b = a *: b ==> RTIMES

lBottom ::  ('[Bottom] |~ '[])
lBottom = base LBOTTOM

rBottom ::  (del |~ gam) -> (del |~ Bottom & gam)
rBottom a = only a ==> RBOTTOM

lPar    ::  (a & del |~ gam) -> (b & del' |~ gam') -> (Par a b & del ++ del' |~ gam ++ gam')
lPar a b = a *: b ==> LPAR

rPar    ::  (del |~ a & b & gam) -> (del |~ Par a b & gam)
rPar a = only a ==> RPAR

lZero   ::  (Zero & del |~ gam)
lZero = base LZERO

rTop    ::  (del |~ Top & gam)
rTop = base RTOP

lWith1  ::  (a & del |~ gam) -> (With a b & del |~ gam)
lWith1 a = only a ==> LWITH1

lWith2  ::  (b & del |~ gam) -> (With a b & del |~ gam)
lWith2 a = only a ==> LWITH2

rWith   ::  (del |~ a & gam) -> (del |~ b & gam) -> (del |~ With a b & gam)
rWith a b = a *: b ==> RWITH

lPlus   ::  (a & del |~ gam) -> (b & del |~ gam) -> (Plus a b & del |~ gam)
lPlus a b = a *: b ==> LPLUS

rPlus1  ::  (del |~ a & gam) -> (del |~ Plus a b & gam)
rPlus1 a = only a ==> RPLUS1

rPlus2  ::  (del |~ b & gam) -> (del |~ Plus a b & gam)
rPlus2 a = only a ==> RPLUS2

-- }}}

