{-# OPTIONS --cubical --guardedness #-}
module Boole.Shouldhave where 

open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import FreeBool
import FreeBool as FB

open import QuotientBool as QB
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base
import Cubical.Algebra.CommRing.Quotient.Base as Quot
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty as UP
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import WLPO
open import CommRingQuotients.EmptyQuotient
module _ {ℓ : Level}  (R : CommRing ℓ) {X : Type ℓ} {f : X → ⟨ R ⟩}
         {S : CommRing ℓ} {g : CommRingHom R S} 
         {gfx=0 : ∀ (x : X) → g $cr (f x) ≡ CommRingStr.0r (snd S)} where
{-
    IQEvalInduce : IQ.inducedHom R f g gfx=0 ∘cr IQ.quotientImageHom R f ≡ g
    IQEvalInduce = IQ.evalInduce {ℓ} R {X} {f} {S}
-}
    IQquotientImageHomSurjective : isSurjection (fst (IQ.quotientImageHom R f) )
    IQquotientImageHomSurjective = quotientHomSurjective R (IQ.genIdeal R f) 
   
    IQquotientImageHomEpi : {ℓ' : Level} → (S : hSet ℓ') → (f' g' : ⟨ R IQ./Im f ⟩ → ⟨ S ⟩) → 
                            f' ∘ (IQ.quotientImageHom R f) .fst ≡ g' ∘ (IQ.quotientImageHom R f).fst → f' ≡ g'
    IQquotientImageHomEpi = quotientHomEpi R (IQ.genIdeal R f)
  

opaque
  unfolding QB.quotientImageHom
  unfolding QB.inducedHom 
  QBEvalInduce : 
     {ℓ : Level} (B : BooleanRing ℓ) {X : Type ℓ} {f : X → ⟨ B ⟩}
     {S : BooleanRing ℓ} {g : BoolHom B S}
     {gfx=0 : ∀ (x : X) → g $cr (f x) ≡ BooleanRingStr.𝟘 (snd S)} → 
     QB.inducedHom {B = B} {f = f} S g gfx=0 ∘cr QB.quotientImageHom {B = B} ≡ g
  QBEvalInduce {ℓ} B {S = S} = IQ.evalInduce {ℓ = ℓ} (BooleanRing→CommRing B) {S = BooleanRing→CommRing S}
   
