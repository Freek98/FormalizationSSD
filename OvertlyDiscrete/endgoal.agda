{-# OPTIONS --lossy-unification #-}
module OvertlyDiscrete.endgoal where
-- This file contains the equivalence between ODisc types and open quotients of countable sets. 
open import Cubical.Foundations.Prelude
open import PropositionalTopology.Definitions
open import Cubical.Foundations.Univalence 
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Functions.Surjection
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit
open import Cubical.Relation.Nullary
open import Cubical.Data.FinSet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat.Order.Recursive using (Decidable→Collapsible)
open import BasicDefinitions
open import LLMGeneratedFixes.EqualityOpenLLMFinished

open Sequence 
private  
  variable 
    ℓ : Level

isSequenceOfFiniteSets : Sequence ℓ → Type _
isSequenceOfFiniteSets An = (n : ℕ) → isFinSet (obj An n)

sequenceOfFiniteSets : Type (ℓ-suc ℓ) 
sequenceOfFiniteSets {ℓ} = Σ[ An ∈ Sequence ℓ ] (isSequenceOfFiniteSets An) 

hasODiscStr : Type ℓ → Type (ℓ-suc ℓ) 
hasODiscStr A = Σ[ An ∈ sequenceOfFiniteSets ] A ≡ SeqColim (fst An)

hasCountableCover : Type ℓ → Type (ℓ-suc ℓ) 
hasCountableCover {ℓ} A = Σ[ B ∈ Type ℓ ] has-Countability-structure B × B ↠ A

hasOpenEqualityStr : Type ℓ → Type _
hasOpenEqualityStr A = (x y : A) → hasOpenStr (x ≡ y)

hasOpenEquality : Type ℓ → Type _ 
hasOpenEquality A = (x y : A) → isOpen (x ≡ y) 

ODiscHasOpenEquality : (A : Type ℓ) → hasODiscStr A → hasOpenEquality A
ODiscHasOpenEquality A ((sequence objA mapA , AnFinite) , A=ColimAn) = 
  subst hasOpenEquality (sym A=ColimAn) equalityIsOpen where
  open FiniteSeqColim objA mapA AnFinite




  

ODiscHasCountableCover : (A : Type ℓ) → hasODiscStr A → hasCountableCover A
ODiscHasCountableCover = {! !} 

CountableCoverAndOpenEqualityImpliesODisc : (A : Type ℓ) → hasCountableCover A → hasOpenEqualityStr A → hasODiscStr A
CountableCoverAndOpenEqualityImpliesODisc = {! !} 
