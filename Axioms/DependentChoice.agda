module Axioms.DependentChoice where

open import Cubical.Functions.Surjection
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁ ; ∥_∥₁)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat 
open import Cubical.Data.Nat.Order 
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude

-- dual to Sequence as SequentialColimit
record Tower (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor tower
  field
    obj : ℕ → Type ℓ
    map : {n : ℕ} → obj (suc n) → obj n

open Tower 

private
  variable 
    ℓ : Level

record SequentialLimit (T : Tower ℓ) : Type ℓ where 
  constructor limitPoint 
  field 
    branch : (n : ℕ) → obj T n
    commutes : (n : ℕ) → map T (branch (suc n)) ≡ branch n

projection : (T : Tower ℓ) → (n : ℕ) →  SequentialLimit T → Tower.obj T n
projection T n (limitPoint branch _) = branch n

allMapsSurjective : (Tower ℓ) → Type ℓ 
allMapsSurjective (tower _ map) = (n : ℕ) → isSurjection (map {n})

projectionSurjective : (T : Tower ℓ) → Type ℓ
projectionSurjective T = isSurjection (projection T 0)

DependentChoiceAxiom : {ℓ : Level} → Type (ℓ-suc ℓ) 
DependentChoiceAxiom {ℓ} = (T : Tower ℓ) → allMapsSurjective T → projectionSurjective T

countableChoiceFor : (P : ℕ → Type ℓ) → Type _
countableChoiceFor P = ((n : ℕ) → P n → ∥ P (suc n) ∥₁) → ∥ P 0 ∥₁  → ∥ ((n : ℕ) → P n) ∥₁ 

countableChoice : {ℓ : Level} → Type _ 
countableChoice {ℓ} = (P : ℕ → Type ℓ) → countableChoiceFor P 

module countableChoiceTower {ℓ : Level} (dc : DependentChoiceAxiom {ℓ}) 
  (P : ℕ → Type ℓ) (pSuc : (n : ℕ) → P n → ∥ P (suc n) ∥₁) (p0 : ∥ P 0 ∥₁ )   where
  PupTo : ℕ → Type ℓ
  PupTo zero = P 0 
  PupTo (suc n) = PupTo n × P (suc n) 

  |Pn| : (n : ℕ) → ∥ P n ∥₁ 
  |Pn| zero = p0 
  |Pn| (suc n) = PT.rec PT.squash₁ (pSuc n) (|Pn| n) 
  
  forgetLastChoice : (n : ℕ) → PupTo (suc n) → PupTo n
  forgetLastChoice n = fst 

  fstSurjective : (n : ℕ) → isSurjection $ forgetLastChoice n
  fstSurjective n nPchoices = {! !}

  partialChoiceTower : Tower ℓ
  partialChoiceTower .obj = PupTo 
  partialChoiceTower .map = fst 



