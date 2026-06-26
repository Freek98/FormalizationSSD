module Countability.Instances.DecidableSubsets where

open import Countability.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Bool.Properties using (isSetBool ; false≢true)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)

open import BinarySequences.Definitions
open import Cubical.HITs.PropositionalTruncation as PT
open Iso

private
  boolGuard : (b : Bool) → (b ≡ true → Bool) → Bool
  boolGuard true  f = f refl
  boolGuard false _ = false

  boolGuard-intro : (b : Bool) (f : b ≡ true → Bool) (q : b ≡ true)
    → f q ≡ true → boolGuard b f ≡ true
  boolGuard-intro true  f q fq = subst (λ r → f r ≡ true) (isSetBool _ _ q refl) fq
  boolGuard-intro false f q _  = ex-falso (false≢true q)

  boolGuard-elim : (b : Bool) (f : b ≡ true → Bool)
    → boolGuard b f ≡ true → Σ[ q ∈ b ≡ true ] f q ≡ true
  boolGuard-elim true  f p = refl , p
  boolGuard-elim false _ p = ex-falso (false≢true p)

module ΣℕSubBinarySequence (α : binarySequence) (P : Σℕ1 α → Bool) where
  ΣαP : binarySequence
  ΣαP n = boolGuard (α n) (λ q → P (n , q))

  ΣαP-intro : (n : ℕ) (q : α n ≡ true) → P (n , q) ≡ true → ΣαP n ≡ true
  ΣαP-intro n = boolGuard-intro (α n) (λ q → P (n , q))

  ΣαP-elim : (n : ℕ) → ΣαP n ≡ true → Σ[ q ∈ α n ≡ true ] P (n , q) ≡ true
  ΣαP-elim n = boolGuard-elim (α n) (λ q → P (n , q))

  ΣℕαP=ΣℕΣαP : Iso (Σ[ x ∈ Σℕ1 α ] P x ≡ true) (Σℕ1 ΣαP)
  fun ΣℕαP=ΣℕΣαP ((n , q) , r) = n , ΣαP-intro n q r
  inv ΣℕαP=ΣℕΣαP (n , r) = (n , fst e) , snd e
    where e = ΣαP-elim n r
  sec ΣℕαP=ΣℕΣαP (n , r) = ΣPathP (refl , (isSetBool _ _ _ _))
  ret ΣℕαP=ΣℕΣαP ((n , q) , r) =
    ΣPathP (ΣPathP (refl , (isSetBool _ _ _ _)) ,
            toPathP (isSetBool _ _ _ _))

countabilityStructureDecidableSubset : {ℓ : Level} → (A : Type ℓ) (P : A → Bool) →
  has-Countability-structure A →
  has-Countability-structure (Σ[ a ∈ A ] P a ≡ true)
countabilityStructureDecidableSubset A P (α , A=Σα) =
  ΣαP , compIso (invIso (Σ-cong-iso-fst (invIso A=Σα))) ΣℕαP=ΣℕΣαP
  where
    P' : Σℕ1 α → Bool
    P' x = P (inv A=Σα x)
    open ΣℕSubBinarySequence α P'

is-countable-decidable-subset : {ℓ : Level} → (A : Type ℓ) (P : A → Bool) →
  is-countable A → is-countable (Σ[ a ∈ A ] P a ≡ true)
is-countable-decidable-subset A P = PT.map (countabilityStructureDecidableSubset A P)
