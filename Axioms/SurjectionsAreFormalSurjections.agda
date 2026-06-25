module Axioms.SurjectionsAreFormalSurjections where

open import BasicDefinitions
open import BooleanRing.FreeBooleanRing.FreeBool

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Functions.Surjection

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import StoneSpaces.Spectrum

-- RENAMING FLAG

module _ {ℓ ℓ' : Level} (B : BooleanRing ℓ) (C : BooleanRing ℓ') (f : BoolHom B C) where
  open BooleanRingStr ⦃...⦄
  instance
    _ = snd B
    _ = snd C
  open RingHomTheory
  isInjectiveBoolHom : Type _
  isInjectiveBoolHom = (x y : ⟨ B ⟩) → (f $cr x) ≡ (f $cr y) → x ≡ y

  ker≡0→injBoolHom :
    ((b : ⟨ B ⟩) → f $cr b ≡ 𝟘 → b ≡ 𝟘) →
    isInjectiveBoolHom
  ker≡0→injBoolHom fb=0→b=0 x y = ker≡0→inj (CommRingHom→RingHom f) (λ {b} → fb=0→b=0 b) {x} {y}

  SpGeneralAction : SpGeneralBooleanRing C → SpGeneralBooleanRing B
  SpGeneralAction = _∘cr f

SpAction : (B C : Booleω) → BoolHom (fst B) (fst C) → Sp C → Sp B
SpAction B C = SpGeneralAction  (fst B) (fst C)

isSurjectiveSpHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isSurjectiveSpHom B C f = isSurjection (SpAction B C f)

formalSurjectionsAreSurjectionsAxiom : Type (ℓ-suc ℓ-zero)
formalSurjectionsAreSurjectionsAxiom =
  (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isInjectiveBoolHom (fst B) (fst C) g → isSurjectiveSpHom B C g
