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

isInjectiveBoolHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isInjectiveBoolHom B C g = (x y : ⟨ fst B ⟩) → g $cr x ≡ g $cr y → x ≡ y
-- Fact : it's sufficient to show that f x = 0 → x = 0. 

module _ (B C : Booleω) where
  open BooleanRingStr ⦃...⦄
  instance 
    _ = snd $ fst B
    _ = snd $ fst C
  open RingHomTheory
  ker≡0→injBoolHom : 
    (f : BoolHom (fst B) (fst C) ) → 
    ((b : ⟨ fst B ⟩) → f $cr b ≡ 𝟘 → b ≡ 𝟘) → 
    isInjectiveBoolHom B C f
  ker≡0→injBoolHom f fb=0→b=0 x y = ker≡0→inj (CommRingHom→RingHom f) (λ {b} → fb=0→b=0 b) {x} {y}


SpAction : (B C : Booleω) → BoolHom (fst B) (fst C) → Sp C → Sp B
SpAction B C f γ = γ ∘cr f 

isSurjectiveSpHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isSurjectiveSpHom B C f = isSurjection (SpAction B C f) 

formalSurjectionsAreSurjectionsAxiom : Type (ℓ-suc ℓ-zero)
formalSurjectionsAreSurjectionsAxiom = 
  (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isInjectiveBoolHom B C g → isSurjectiveSpHom B C g

--surjectionsAreFormallySurjecive : (B C : Booleω) (g : BoolHom (fst B) (fst C)) → isSurjectiveSpHom B C g → isInjectiveBoolHom B C g 
--surjectionsAreFormallySurjecive B C g ∘gSurj b c gb=gc = {! ∘gSurj   !} where
--  pick : ⟨ fst B ⟩ → BoolHom (freeBA Unit) (fst B)
--  pick x = inducedBAHom Unit (fst B) λ _ → x 
--  gpickx=gpicky : g ∘cr pick b ≡ g ∘cr pick c
--  gpickx=gpicky = {! gb=gc !} 


-- This should be a standard categorical fact if we replace surjective by epi and injective by mono. But we should be able to see it via the free BA on 1 generator, and the morphisms sending that one generator to x and to y. 


