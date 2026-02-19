{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module BooleanRing.BooleanRingQuotients.QuotientConclusions  where 
{- We show that the quotient of a Boolean Ring agrees with that of the underlying commutative Ring -}


import Cubical.Data.Sum as ⊎

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing.Univalence
open import Cubical.Relation.Nullary

open import QuotientBool as QB
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.CommRing.Quotient.Base
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty as UP
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import BasicDefinitions
open import CommRingQuotients.EmptyQuotient
open import CountablyPresentedBooleanRings.PresentedBoole
open import Cubical.Algebra.CommRing.Univalence 

open import CountablyPresentedBooleanRings.Examples.FreeCase 
open import CommRingQuotients.EquivHelper
open import CommRingQuotients.RepeatedQuotient
open import BooleanRing.BoolRingUnivalence

private opaque
  unfolding QB._/Im_
  quotientCheck : {ℓ : Level} (A : BooleanRing ℓ) → {X : Type ℓ} → (f : X → ⟨ A ⟩ ) → 
    (BooleanRing→CommRing A) IQ./Im f ≡ BooleanRing→CommRing (A QB./Im f)
  quotientCheck A f = refl 

  sameUnderlyingSet : (A : BooleanRing ℓ-zero) → (fst A) ≡ fst (BooleanRing→CommRing A)
  sameUnderlyingSet A = refl

private opaque
  unfolding QB.quotientImageHom
  unfolding QB._/Im_
  sumWhenRestricted : {ℓ : Level} (A : BooleanRing ℓ) {X : Type ℓ} (f g : X → ⟨ A ⟩) → 
    BooleanRing→CommRing (A QB./Im (⊎.rec f g)) ≡
    BooleanRing→CommRing ((A QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
  sumWhenRestricted A f g =  
    BooleanRing→CommRing (A QB./Im (⊎.rec f g)) 
      ≡⟨ quotientCheck A (⊎.rec f g) ⟩ 
    (BooleanRing→CommRing A) IQ./Im (⊎.rec f g)
      ≡⟨ (uaCommRing $ quotientConclusion (BooleanRing→CommRing A) f g) ⟩ 
    ((BooleanRing→CommRing A) IQ./Im f) IQ./Im ((fst $ IQ.quotientImageHom (BooleanRing→CommRing A) f)∘ g)
      ≡⟨ quotientCheck (A QB./Im f) ((fst (IQ.quotientImageHom (BooleanRing→CommRing A) f)) ∘ g)⟩ 
    BooleanRing→CommRing ((A QB./Im f) QB./Im ( (fst $ QB.quotientImageHom {B = A} {f = f}) ∘ g)) ∎ 

quotientEquivBool : {ℓ : Level} {X : Type ℓ} (A : BooleanRing ℓ) (f g : X → ⟨ A ⟩ ) →
  A QB./Im (⊎.rec f g) ≡
  (A QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g)
quotientEquivBool A f g = uaBoolRing
  (invEq (CommRingPath _ _) (sumWhenRestricted A f g))
