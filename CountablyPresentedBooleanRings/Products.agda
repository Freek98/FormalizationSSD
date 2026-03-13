{-# OPTIONS --lossy-unification #-}
module CountablyPresentedBooleanRings.Products where 
open import CountablyPresentedBooleanRings.Definitions

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso ; rec* to empty-func)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning
open import Cubical.Data.Nat.Bijections.Sum

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.BooleanRing

open import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.FreeBool
import BooleanRing.FreeBooleanRing.FreeBool as FB

open  import BooleanRing.FreeBooleanRing.SurjectiveTerms
open  import BooleanRing.FreeBooleanRing.freeBATerms

open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.QuotientConclusions 
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing
import Cubical.Algebra.CommRing.Quotient.Base as Quot
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty as UP
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import BasicDefinitions
open import CommRingQuotients.EmptyQuotient
open import Countability.Properties
open import BooleanRing.BooleanRingMaps
open import BooleanRing.ProductBA

module freeBASum (A B : Type) where
  -- the following should make use of the universal property of free Boolean algebras
  sumFreeEqu : BooleanRingEquiv (freeBA A ×BR freeBA B) (freeBA (A ⊎ B))
  sumFreeEqu = {! !} 
  -- Sketch using universal properties of freeBA and ⊎ 
  --          (freeBA A ⊎ B , D) ≃ (A ⊎ B , D) ≃ (A , ⟨ D ⟩) × (B , ⟨ D ⟩) ≃ 
  --          (freeBA A , D) x (freeBA B , D)
  --          And then use some yoneda-trick of A , D = B , D for all D, then A = B
  module quotient {X Y : Type} (f : X → ⟨ freeBA A ⟩) (g : Y → ⟨ freeBA B ⟩) where
    open BooleanRingStr ⦃...⦄
    instance 
      _ = snd (freeBA A)
      _ = snd (freeBA B) 
      _ = snd (freeBA A ×BR freeBA B)
    combMap : (X ⊎ Y) → ⟨ freeBA A ×BR freeBA B ⟩
    combMap (inl x) = f x , 𝟘
    combMap (inr y) = 𝟘 , g y 

    quotientEqu : BooleanRingEquiv 
      ((freeBA A /Im f) ×BR (freeBA B /Im g)) 
      ((freeBA (A ⊎ B)) /Im (fst (fst sumFreeEqu) ∘ combMap)) 
    quotientEqu = {! !} 



Equ×Map : (B C D E : BooleanRing ℓ-zero) → BooleanRingEquiv B D → BooleanRingEquiv C E → BooleanRingEquiv (B ×BR C) (D ×BR E)
Equ×Map = {! !} 

module ProductPresentation (B C : BooleanRing ℓ-zero) where
  predProd : (presB : has-countable-presentation B) 
             (presC : has-countable-presentation C) → 
             has-countable-presentation (B ×BR C)
  predProd (BGens , BGensCount , X , XCount , f , B=FreeG/f) 
           (CGens , CGensCount , Y , YCount , g , C=FreeG/g) = 
           (BGens ⊎ CGens) , has-Countability-structure-⊎ BGensCount CGensCount , 
           (X ⊎ Y) , has-Countability-structure-⊎ XCount YCount , 
           fst (fst sumFreeEqu) ∘ combMap , 
           (EquivQuotBR sumFreeEqu combMap) ∘cre {! quotientEqu !} ∘cre Equ×Map 
             B C (freeBA BGens /Im f) (freeBA CGens /Im g) B=FreeG/f C=FreeG/g where
           -- Sketch:
           -- B ×BR C ≃ (freeBA BGens / f) (freeBA CGens / g) ≃
           --           ((freeBA (A ⊎ B)) /Im (fst (fst sumFreeEqu) ∘ combMap))
           --           
           --           
           open freeBASum BGens CGens
           open quotient f g 

