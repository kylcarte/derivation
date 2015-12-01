{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

module Data.Derivation.Natural where

import Data.Derivation hiding (cut)
import Data.Type.Index.Quote

data Prop a
  = Atom a
  | Bottom
  | Prop a :-> Prop a
  deriving (Eq,Ord,Show)
infixr 3 :->

type Not a = a :-> Bottom

data Natural :: [([Prop k],Prop k)] -> [Prop k] -> Prop k -> * where
  Premise :: !(Index as a)
          -> Natural '[] as a
  BtmE    :: Natural '[as # Bottom] as a
  ArrI    :: Natural '[(a & as) # b] as (a :-> b)
  ArrE    :: Natural '[as # (a :-> b),as # a] as b

type (|-) = Derivation Natural
infix 1 |-

hyp :: Index as a -> as |- a
hyp = base . Premise

btmE :: as |- Bottom -> as |- a
btmE a = only a ==> BtmE

arrI :: (a & as) |- b -> as |- (a :-> b)
arrI a = only a ==> ArrI

arrE :: as |- (a :-> b) -> as |- a -> as |- b
arrE a b = a *: b ==> ArrE

btmI :: as |- a -> as |- Not a -> as |- b
btmI a a' = btmE $ arrE a' a

instance WeakenAdmissible Natural where
  weakenRule = weakenNat IS

instance ContractionAdmissible Natural where
  contractRule = weakenNat $ \case
    [ix|0|]   -> [ix|0|]
    [ix|1|]   -> [ix|0|]
    IS (IS x) -> IS x

instance ExchangeAdmissible Natural where
  exchangeRule = weakenNat $ \case
    [ix|0|]   -> [ix|1|]
    [ix|1|]   -> [ix|0|]
    IS (IS x) -> IS $ IS x

instance CutAdmissible Natural where
  cutRule a b = arrE (arrI b) a

weakenNat :: (forall x. Index as x -> Index bs x) -> as |- a -> bs |- a
weakenNat f (Derivation (r :$ subs)) = case (r,subs) of
  (Premise x,_           ) -> hyp $ f x
  (BtmE     ,     a :* ØA) -> btmE $ weakenNat f a
  (ArrI     ,     a :* ØA) -> arrI $ weakenNat (extend f) a
  (ArrE     ,a :* b :* ØA) -> arrE (weakenNat f a) (weakenNat f b)
  _                        -> error "impossible"

extend :: (forall x. Index as x -> Index bs x) -> Index (b :< as) a -> Index (b :< bs) a
extend f = \case
  IZ   -> IZ
  IS x -> IS $ f x

{-
type p :|: q = Not (Not p :&: Not q)
infixr 3 :|:
type p :-> q = Not (p :&: Not q)
infixr 2 :->

data Natural :: [([Prop k],Prop k)] -> [Prop k] -> Prop k -> * where
  Premise :: !(Index gam a)
          -> Natural '[]
             --------
             gam a
  --------------------
  NegI    :: Natural '[ (a & gam) # b , (a & gam) # Not b ]
             --------
             gam (Not a)
  --------------------
  NegE    :: Natural '[ (Not a & gam) # b , (Not a & gam) # Not b ]
             --------
             gam a
  --------------------
  ConjI   :: Natural '[ gam # a , gam # b ]
             --------
             gam (a :&: b)
  --------------------
  ConjE1  :: Natural '[ gam # (a :&: b) ]
             --------
             gam a
  --------------------
  ConjE2  :: Natural '[ gam # (a :&: b) ]
             --------
             gam b

weakenNat :: (forall x. Index as x -> Index bs x) -> Derivation Natural as a -> Derivation Natural bs a
weakenNat f (Derivation (r :$ subs)) = case (r,subs) of
  (Premise x,          ØA) -> Premise (f x) $$ ØA
  (NegI     ,a :* b :* ØA) -> negI (weakenNat (extend f) a) (weakenNat (extend f) b)
  (NegE     ,a :* b :* ØA) -> NegE   $$ weakenNat (extend f) a :* weakenNat (extend f) b :* ØA
  (ConjI    ,a :* b :* ØA) -> ConjI  $$ weakenNat f a :* weakenNat f b :* ØA
  (ConjE1   ,     a :* ØA) -> ConjE1 $$ weakenNat f a :* ØA
  (ConjE2   ,     a :* ØA) -> ConjE2 $$ weakenNat f a :* ØA
  _                        -> error "impossible"

instance Rule Natural Natural

instance WeakenAdmissible Natural where
  weakenRule = weakenNat IS

instance ExchangeAdmissible Natural where
  exchangeRule = weakenNat $ \case
    IZ         -> IS IZ
    IS IZ      -> IZ
    IS (IS x)  -> IS $ IS x

instance ContractionAdmissible Natural where
  contractRule = weakenNat $ \case
    IZ        -> IZ
    IS IZ     -> IZ
    IS (IS x) -> IS x
-}

{-
instance CutAdmissible Natural where
  cutRule a b = 
-}

{-
premise :: Index gam a
        -> (gam |- a)
premise = base . Premise

negI   :: (a & gam |- b)
       -> (a & gam |- Not b)
       -> (gam     |- Not a)
negI a b = a *: b ==> NegI

negE   :: (Not a & gam |- b)
       -> (Not a & gam |- Not b)
       -> (gam         |- a)
negE a b = a *: b ==> NegE

conjI  :: (gam |- a)
       -> (gam |- b)
       -> (gam |- a :&: b)
conjI a b = a *: b ==> ConjI

conjE1 :: (gam |- a :&: b)
       -> (gam |- a)
conjE1 a = only a ==> ConjE1

conjE2 :: (gam |- a :&: b)
       -> (gam |- b)
conjE2 a = only a ==> ConjE2
-}

{-
condI :: (a :< gam |- b)
      -> (gam |- a :-> b)
condI b = negI _ (conjE2 $ premise [ix|0|])
-}

{-
disjI1 :: (gam |- a)
       -> (gam |- a :|: b)
disjI1 a = negI
  ( weaken1 a )
  ( conjE1 (premise [ix|0|]) )
-}

{-
disjI2 :: (gam |- b)
       -> (gam |- a :|: b)
disjI2 b = negI
  ( weaken1 b )
  ( conjE2 (premise [ix|0|]) )
-}

{-
bottomE :: (gam |- a)
        -> (gam |- Not a)
        -> (gam |- b)
bottomE a b = negE
  ( weaken1 a )
  ( weaken1 b )
-}

{-
dblNeg :: (gam |- Not (Not a))
       -> (gam |- a)
dblNeg a = negE
  ( premise [ix|0|] )
  ( weaken1 a )
-}

{-
condI :: (a & gam |- b)
      -> (gam |- a :-> b)
condI b = negI
  ( cut
    ( conjE1 (premise [ix|0|]) )
    ( weaken w b )
  ) $ conjE2 (premise [ix|0|])
  where
  w :: Index (a & gam) x -> Index (a & (a :&: Not b) & gam) x
  w = \case
    IZ   -> IZ
    IS i -> IS (IS i)
-}

{-
condE :: (gam |- a :-> b)
   -> (a & gam |- b)
condE f = negE
  ( conjI
    (premise [ix|1|])
    (premise [ix|0|])
  )
  ( weaken (IS . IS) f )
-}

{-
mPonens :: (gam |- a :-> b)
        -> (gam |- a)
        -> (gam |- b)
mPonens f a = cut a $ condE f

kAxiom :: gam |- b :-> a :-> b
kAxiom = condI $ condI $ premise [ix|1|]

sAxiom :: gam |- (a :-> b :-> c) :-> (a :-> b) :-> (a :-> c)
sAxiom = condI $ condI $ condI
  $ mPonens
    ( mPonens
      (premise [ix|2|])
      (premise [ix|0|])
    )
  $ mPonens
    (premise [ix|1|])
    (premise [ix|0|])

contAxiom :: gam |- (Not b :-> Not a) :-> (a :-> b)
contAxiom = condI $ condI $ negE
  (premise [ix|1|])
  $ mPonens
    (premise [ix|2|])
    (premise [ix|0|])

contra :: gam |- (a :-> b) :-> (b :-> c) :-> (a :-> c)
contra = condI $ condI $ condI $ mPonens
  (premise [ix|1|])
  $ mPonens
    (premise [ix|2|])
    (premise [ix|0|])
-}

