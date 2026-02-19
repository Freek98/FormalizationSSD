{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.Examples.BoolQuotient where 

open import CountablyPresentedBooleanRings.CountableQuotient
open import CountablyPresentedBooleanRings.PresentedBoole
open import CountablyPresentedBooleanRings.Examples.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Base
open import Cubical.Algebra.CommRing
open IsCommRingHom

open import BooleanRing.FreeBooleanRing.FreeBool
open import Cubical.Data.Nat
open import QuotientBool as QB
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool

open BooleanRingStr (snd $ freeBA ℕ) 
private
  f₀ = fst is-cp-2
  e = snd is-cp-2
  eFwd = fst (fst e)
  π : BoolHom (freeBA ℕ) (freeBA ℕ QB./Im f₀)
  π = QB.quotientImageHom

boolLift : Bool → ⟨ freeBA ℕ ⟩
boolLift true  = 𝟙
boolLift false = 𝟘

liftCondition : (α : ℕ → Bool) →
  fst π ∘ (boolLift ∘ α) ≡ eFwd ∘ α
liftCondition α = funExt pointwise where
  pointwise : (n : ℕ) → fst π (boolLift (α n)) ≡ eFwd (α n)
  pointwise n with α n
  ... | true  = pres1 (snd π) ∙ sym (pres1 (snd e))
  ... | false = pres0 (snd π) ∙ sym (pres0 (snd e))

boolQuotientPresented : (α : ℕ → Bool) → has-Boole-ω' (BoolBR QB./Im α)
boolQuotientPresented α =
  countablyPresentedQuotient BoolBR is-cp-2 α (boolLift ∘ α) (liftCondition α)

