module Countability.Instances.DecidableSubsets where

open import Countability.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)

open import BinarySequences.Definitions
open import Cubical.HITs.PropositionalTruncation as PT
open Iso

private
  dependentBool : (b : Bool) → (b ≡ true → Bool) → Bool
  dependentBool true  f = f refl
  dependentBool false _ = false

  dependentBool-intro : (b : Bool) (f : b ≡ true → Bool) (q : b ≡ true)
    → f q ≡ true → dependentBool b f ≡ true
  dependentBool-intro true  f q fq = subst (λ r → f r ≡ true) (isSetBool _ _ q refl) fq
  dependentBool-intro false f q _  = ex-falso (false≢true q)

  dependentBool-elim : (b : Bool) (f : b ≡ true → Bool)
    → dependentBool b f ≡ true → Σ[ q ∈ b ≡ true ] f q ≡ true
  dependentBool-elim true  f p = refl , p
  dependentBool-elim false _ p = ex-falso (false≢true p)

module ΣℕSubBinarySequence (α : binarySequence) (P : Σℕ1 α → Bool) where
  ΣαPSequence : binarySequence
  ΣαPSequence n = dependentBool (α n) (λ q → P (n , q))

  ΣαPSequence-intro : (n : ℕ) (q : α n ≡ true) → P (n , q) ≡ true → ΣαPSequence n ≡ true
  ΣαPSequence-intro n = dependentBool-intro (α n) (λ q → P (n , q))

  ΣαPSequence-elim : (n : ℕ) → ΣαPSequence n ≡ true → Σ[ q ∈ α n ≡ true ] P (n , q) ≡ true
  ΣαPSequence-elim n = dependentBool-elim (α n) (λ q → P (n , q))

  ΣℕαP=ΣℕΣαPSequence : Iso (Σ[ x ∈ Σℕ1 α ] P x ≡ true) (Σℕ1 ΣαPSequence)
  fun ΣℕαP=ΣℕΣαPSequence ((n , q) , r) = n , ΣαPSequence-intro n q r
  inv ΣℕαP=ΣℕΣαPSequence (n , r) = (n , fst e) , snd e
    where e = ΣαPSequence-elim n r
  sec ΣℕαP=ΣℕΣαPSequence (n , r) = ΣPathP (refl , (isSetBool _ _ _ _))
  ret ΣℕαP=ΣℕΣαPSequence ((n , q) , r) =
    ΣPathP (ΣPathP (refl , (isSetBool _ _ _ _)) ,
            toPathP (isSetBool _ _ _ _))

countabilityStructureDecidableSubset : {ℓ : Level} → (A : Type ℓ) (P : A → Bool) →
  has-Countability-structure A →
  has-Countability-structure (Σ[ a ∈ A ] P a ≡ true)
countabilityStructureDecidableSubset A P (α , A=Σα) =
  ΣαPSequence , compIso (invIso (Σ-cong-iso-fst (invIso A=Σα))) ΣℕαP=ΣℕΣαPSequence
  where
    P' : Σℕ1 α → Bool
    P' x = P (inv A=Σα x)
    open ΣℕSubBinarySequence α P'

is-countable-decidable-subset : {ℓ : Level} → (A : Type ℓ) (P : A → Bool) →
  is-countable A → is-countable (Σ[ a ∈ A ] P a ≡ true)
is-countable-decidable-subset A P = PT.map (countabilityStructureDecidableSubset A P)
