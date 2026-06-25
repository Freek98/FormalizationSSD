module BinarySequences where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Bool renaming ( _≤_ to _≤B_ ; _≥_ to _≥B_ ; _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open <-Reasoning

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT


open import BasicDefinitions


or-≥-left : (a b : Bool) → (a or b) ≥B a
or-≥-left false false = tt
or-≥-left false true = tt
or-≥-left true _ = tt

or-≥-right : (a b : Bool) → (a or b) ≥B b
or-≥-right false false = tt
or-≥-right false true = tt
or-≥-right true _ = tt

or-true→⊎-default-right : (a b : Bool) → a or b ≡ true → (a ≡ true) ⊎ (b ≡ true)
or-true→⊎-default-right false false x = ex-falso (false≢true x)
or-true→⊎-default-right true  false _ = ⊎.inl refl
or-true→⊎-default-right false true  _ = ⊎.inr refl
or-true→⊎-default-right true  true  _ = ⊎.inr refl

or-true→⊎-default-left : (a b : Bool) → a or b ≡ true → (a ≡ true) ⊎ (b ≡ true)
or-true→⊎-default-left false false x = ex-falso (false≢true x)
or-true→⊎-default-left true  false _ = ⊎.inl refl
or-true→⊎-default-left false true  _ = ⊎.inr refl
or-true→⊎-default-left true  true  _ = ⊎.inl refl

and-true→× : (a b : Bool) → (a and b) ≡ true → (a ≡ true) × (b ≡ true)
and-true→× false _    x = ex-falso (false≢true x)
and-true→× true false x = ex-falso (false≢true x)
and-true→× true true  x = refl , refl

or-true→⊎ : (a b : Bool) → a or b ≡ true → (a ≡ true) ⊎ (b ≡ true)
or-true→⊎ = or-true→⊎-default-left

false-or-x-true→x-true : (a : Bool) → false or a ≡ true → a ≡ true
false-or-x-true→x-true false x = ex-falso (false≢true x)
false-or-x-true→x-true true _ = refl

x-or-false-true→x-true : (a : Bool) → a or false ≡ true → a ≡ true
x-or-false-true→x-true false x = ex-falso (false≢true x)
x-or-false-true→x-true true _ = refl

module MakeIncreasing where
  makeIncreasing : binarySequence → binarySequence
  makeIncreasing α zero = α 0
  makeIncreasing α (suc n) = α (suc n) or makeIncreasing α n

  isIncreasingSeq : binarySequence → Type
  isIncreasingSeq α = (n : ℕ) → α (suc n) ≥B α n

  makeIncreasingIsIncreasing : (α : binarySequence) → isIncreasingSeq (makeIncreasing α)
  makeIncreasingIsIncreasing α n = or-≥-right (α (suc n)) (makeIncreasing α n)

  hit→makeIncreasingHit : (α : binarySequence) → (n : ℕ) → α n ≡ true → makeIncreasing α n ≡ true
  hit→makeIncreasingHit α zero αn=1 = αn=1
  hit→makeIncreasingHit α (suc n) αn=1 = cong (λ b → b or makeIncreasing α n) αn=1

  extractFromMakeIncreasing : (α : binarySequence) → (n : ℕ) → makeIncreasing α n ≡ true → Σ[ n ∈ ℕ ] α n ≡ true
  extractFromMakeIncreasing α zero αInc=1 = zero , αInc=1
  extractFromMakeIncreasing α (suc n) αInc=1 = case ((makeIncreasing α n) =B true) of λ
   { (no ¬p) → suc n , x-or-false-true→x-true (α $ suc n)
     ( α (suc n) or false
         ≡⟨ cong (λ b → α (suc n) or b) (sym (¬true→false (makeIncreasing α n) ¬p)) ⟩
       α (suc n) or (makeIncreasing α n)
         ≡⟨ αInc=1 ⟩
       true ∎ ) ;
     (yes p) → extractFromMakeIncreasing α n p }

