module Countability.Instances.BinarySum where

open import Countability.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
open import BinarySequences.Definitions
open import Cubical.HITs.PropositionalTruncation as PT
open Iso

module ΣℕSumBinarySequence (α β : binarySequence) where
  γ : binarySequence
  γ n = ⊎.rec α β (inv ℕ⊎ℕ≅ℕ n)

  flattenSum : Iso (Σℕ1 α ⊎ Σℕ1 β) (Σ[ s ∈ ℕ ⊎ ℕ ] ⊎.rec α β s ≡ true)
  fun flattenSum (inl (n , p)) = inl n , p
  fun flattenSum (inr (m , q)) = inr m , q
  inv flattenSum (inl n , p) = inl (n , p)
  inv flattenSum (inr m , q) = inr (m , q)
  sec flattenSum (inl n , p) = refl
  sec flattenSum (inr m , q) = refl
  ret flattenSum (inl (n , p)) = refl
  ret flattenSum (inr (m , q)) = refl

  Σℕα⊎Σℕβ=Σℕγ : Iso (Σℕ1 α ⊎ Σℕ1 β) (Σℕ1 γ)
  Σℕα⊎Σℕβ=Σℕγ = compIso flattenSum (invIso (Σ-cong-iso-fst (invIso ℕ⊎ℕ≅ℕ)))

countabilityStructureBinarySum : {ℓ : Level} → (A B : Type ℓ) →
  has-Countability-structure A → has-Countability-structure B →
  has-Countability-structure (A ⊎ B)
countabilityStructureBinarySum A B (α , A=Σα) (β , B=Σβ) = γ , compIso (⊎Iso A=Σα B=Σβ) Σℕα⊎Σℕβ=Σℕγ where
  open ΣℕSumBinarySequence α β

is-countable-BinarySum : {ℓ : Level} → (A B : Type ℓ) →
  is-countable A → is-countable B → is-countable (A ⊎ B)
is-countable-BinarySum A B = rec2 squash₁ λ a b → ∣ countabilityStructureBinarySum A B a b ∣₁
