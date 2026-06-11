module PropositionalTopology.Definitions where

open import BasicDefinitions
open import BinarySequences
open import QuickFixes
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat.Bijections.Sum
open import Cubical.Data.Nat.Bijections.Product
open import Cubical.Functions.Logic
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing

import BooleanRing.BooleanRingQuotients.QuotientBool as QB
import Cubical.Data.Sum as ⊎

private 
  variable 
    ℓ : Level

isOpenWitness : hProp ℓ → Type _
isOpenWitness P = Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ (Σ[ n ∈ ℕ ] α n ≡ true)

isOpenProp : hProp ℓ → Type _ 
isOpenProp P = ∥ isOpenWitness P ∥₁

hasOpenStr : (P : Type ℓ) → Type _ 
hasOpenStr P = Σ[ Pprop ∈ isProp P ] isOpenWitness (P , Pprop)

isOpen : (P : Type ℓ) → Type _ 
isOpen P = ∥ hasOpenStr P ∥₁ 

isClosedWitness : hProp ℓ → Type _ 
isClosedWitness P = Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) →  α n ≡ false)

isClosedProp : hProp ℓ → Type _ 
isClosedProp P = ∥ isClosedWitness P ∥₁ 

hasClosedStr : (P : Type ℓ) → Type _ 
hasClosedStr P = Σ[ Pprop ∈ isProp P ] isClosedWitness (P , Pprop)

isClosed : (P : Type ℓ) → Type _ 
isClosed P = ∥ hasClosedStr P ∥₁ 

Open : Type₁
Open = Σ[ P ∈ hProp ℓ-zero ] isOpenProp P

Closed : Type₁
Closed = Σ[ P ∈ hProp ℓ-zero ] isClosedProp P


