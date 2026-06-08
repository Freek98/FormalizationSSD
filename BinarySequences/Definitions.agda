module BinarySequences.Definitions where 

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_)
open import Cubical.Data.Nat

open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary

binarySequence : Type 
binarySequence = ℕ → Bool

bitFlip : binarySequence → binarySequence
bitFlip = not ∘_ 

δSequence : ℕ → binarySequence
δSequence = _≡ᵇ_

Σℕ1 : binarySequence → Type 
Σℕ1 α = Σ[ n ∈ ℕ ] α n ≡ true

∃ℕ1 : binarySequence → Type
∃ℕ1 α = ∥ Σℕ1 α ∥₁

∀ℕ0 : binarySequence → Type 
∀ℕ0 α = (n : ℕ) → α n ≡ false

hits1AtMostOnce : binarySequence → Type 
hits1AtMostOnce α = ∀ (n m : ℕ) → α n ≡ true → α m ≡ true → n ≡ m 

hits1NotTwice : binarySequence → Type 
hits1NotTwice α = ∀ (n m : ℕ) → ¬ (m ≡ n) → α m and α n ≡ false
