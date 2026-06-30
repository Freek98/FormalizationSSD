module Countability.Instances.Canonical where

open import Countability.Base
open import BinarySequences.Definitions

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

countabilityStructureΣℕ1 : (α : binarySequence) → has-Countability-structure (Σℕ1 α)
countabilityStructureΣℕ1 α = α , idIso

is-countable-Σℕ1 : (α : binarySequence) → is-countable (Σℕ1 α)
is-countable-Σℕ1 α = ∣ countabilityStructureΣℕ1 α ∣₁

countabilityStructureIso : has-Countability-structure A → Iso A B →
  has-Countability-structure B
countabilityStructureIso (α , A≅Σα) A≅B = α , compIso (invIso A≅B) A≅Σα

is-countable-Iso : is-countable A → Iso A B → is-countable B
is-countable-Iso cA A≅B = PT.map (λ s → countabilityStructureIso s A≅B) cA
