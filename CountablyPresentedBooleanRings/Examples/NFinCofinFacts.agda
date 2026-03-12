{-# OPTIONS --guardedness --lossy-unification #-}
module CountablyPresentedBooleanRings.Examples.NFinCofinFacts where
open import CountablyPresentedBooleanRings.Examples.NFinCofin

open import BooleanRing.SubBooleanRing
open import Cubical.Data.Bool renaming (_≟_ to _=B_) hiding (_≤_ ; _≥_)
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import QuickFixes

open import BooleanRing.BooleanRingMaps
open import BooleanRing.FreeBooleanRing.FreeBool
import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.UniversalProperty
open import BooleanRing.BoolAlgMorphism

open import BasicDefinitions

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism using (Iso)

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕ_)
open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
open import Cubical.Data.List
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import CountablyPresentedBooleanRings.Definitions
open BooleanAlgebraStr ⦃...⦄
open BooleanRingStr ⦃...⦄

module UniversalPropertyCountablyPresented 
  {ℓ : Level} (B : BooleanRing ℓ) where
  instance _ = snd B
  instance _ = snd (freeBA ℕ)
--  niceType = Σ[ f ∈ (ℕ → ⟨ B ⟩) ] ((n m : ℕ) → (n ≡ m → ⊥) → (f n) ∧ (f m) ≡ 𝟘)
--  extension : BoolHom presentation B
--  extension = {! !} 
--  goalIso : Iso niceType (BoolHom ℕfinCofinBA B)
--  goalIso = {! !} 
  
  smallerConditionThenRelationsOnFunctions : 
    (f : BoolHom (freeBA ℕ) B) → 
    (∀ (n : ℕ) → f $cr (relationsℕ n) ≡ 𝟘) → 
    (∀ (n m : ℕ) → ((n ≡ m ) → ⊥) → f $cr ((generator n) ∧ (generator m)) ≡ 𝟘)
  smallerConditionThenRelationsOnFunctions f frespRelations n m n≢m = 
    f $cr ((generator n) ∧ (generator m)) 
      ≡⟨ cong (fst f) (sym $ NFinCofinPresentation.relations-neq n m n≢m) ⟩ 
    f $cr (relations (n , m) )
      ≡⟨ cong (fst f ∘ relations) (sym $ ℕ×ℕ≅ℕ .Iso.ret (n , m)) ⟩ 
    f $cr (relationsℕ (ℕ×ℕ≅ℕ .Iso.fun (n , m) ) )
      ≡⟨ frespRelations (ℕ×ℕ≅ℕ .Iso.fun (n , m)) ⟩ 
    𝟘 ∎
  
  open IsCommRingHom
  otherDirection : 
    (f : BoolHom (freeBA ℕ) B) → 
    (∀ (n m : ℕ) → ((n ≡ m ) → ⊥) → f $cr ((generator n) ∧ (generator m)) ≡ 𝟘) → 
    (∀ (n : ℕ) → f $cr (relationsℕ n) ≡ 𝟘)
  otherDirection f fzeroOnDiffGenerators n with (uncurry discreteℕ) (ℕ×ℕ≅ℕ . Iso.inv n)
  ... | yes p = pres0 (snd f)
  ... | no ¬p = fzeroOnDiffGenerators _ _ ¬p 

