{-# OPTIONS --cubical --guardedness #-}

module BasicDefinitions where 

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_)
open import Cubical.Data.Nat

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Isomorphism

_↔_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A ↔ B = (A → B) × (B → A)

binarySequence : Type 
binarySequence = ℕ → Bool

has-Countability-structure : {ℓ : Level} → (A : Type ℓ) → Type ℓ
has-Countability-structure A = Σ[ α ∈ binarySequence ] Iso A (Σ[ n ∈ ℕ ] α n ≡ true)

-- Definition 1.2.
is-countable : {ℓ : Level} → (A : Type ℓ) → Type ℓ
is-countable A = ∥ has-Countability-structure A ∥₁ 
