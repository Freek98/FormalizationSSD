module Axioms.DependentChoice where

open import Cubical.Functions.Surjection
open import Cubical.Foundations.Function
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat 
open import Cubical.Data.Nat.Order 
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
