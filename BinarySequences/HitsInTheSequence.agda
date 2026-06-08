module BinarySequences.HitsInTheSequence where

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

noHitBefore : binarySequence → ℕ → Bool
noHitBefore α zero    = true
noHitBefore α (suc n) = noHitBefore α n and not (α n)

firstHitOnly : binarySequence → binarySequence
firstHitOnly α n = α n and noHitBefore α n

shift : binarySequence → binarySequence
shift α k = α (suc k)

atMostOneFirstHit : (α : binarySequence) → (n m : ℕ) → firstHitOnly α n ≡ true → firstHitOnly α m ≡ true → n ≡ m 
atMostOneFirstHit α zero zero fHαn fHαm = refl
atMostOneFirstHit α zero (suc m) fHαn fHαm = {! !}
atMostOneFirstHit α (suc n) zero fHαn fHαm = {! !}
atMostOneFirstHit α (suc n) (suc m) fHαn fHαm = atMostOneFirstHit (shift α) {! n !} {! !} {! !} {! !} 

isPropFirstHitOnly : (α : binarySequence) → isProp (Σℕ $ firstHitOnly α) 
isPropFirstHitOnly α (n , fHαn) (m , fHαm) = Σ≡Prop (λ n → isSetBool (fHα n) true) 
  {! !} where
  fHα = firstHitOnly α
