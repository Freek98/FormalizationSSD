{-# OPTIONS --cubical --guardedness #-}
module AntiEquivalence where
open import Axioms.StoneDuality
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
import Cubical.Induction.WellFounded as WF
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties using (isProp⊎)

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

module SpectrumEmptyImpliesTrivial (SD : StoneDualityAxiom) (B : Booleω) (spEmpty : Sp B → ⊥) where
  emptyFunContr : isContr (Sp B → Bool)
  emptyFunContr = (λ sp → ex-falso (spEmpty sp)) , λ f → funExt (λ sp → ex-falso (spEmpty sp))

  B-contr : isContr ⟨ fst B ⟩
  B-contr = isOfHLevelRespectEquiv 0 (invEquiv (evaluationMap B , SD B)) emptyFunContr

  0≡1-in-B : BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B))
  0≡1-in-B = isContr→isProp B-contr _ _

