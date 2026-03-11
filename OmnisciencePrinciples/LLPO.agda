{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module OmnisciencePrinciples.LLPO where
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
open import BooleanRing.ProductBA
open import Axioms.SurjectionsAreFormalSurjections
open import Axioms.StoneDuality
open import StoneSpaces.Spectrum

module LLPOProof (sd : StoneDualityAxiom) (fs : formalSurjectionsAreSurjectionsAxiom) where
  module B∞Dfn (B∞ : BooleanRing ℓ-zero) (singletons : ℕ → ⟨ B∞ ⟩) where
    module UniversalPropertyB∞Dfn (C : BooleanRing ℓ-zero) where
      open BooleanAlgebraStr (snd C)
      open BooleanRingStr (snd C)
      B∞UP : Type
      B∞UP = Iso (BoolHom B∞ C) 
        (Σ[ α ∈ (ℕ → ⟨ C ⟩) ] ((n m : ℕ) → (n ≡ m → ⊥) → (α n) ∧ (α m) ≡ 𝟘 ))
      B∞UPFunctions : B∞UP → Type 
      B∞UPFunctions B∞C≃Σ = (n : ℕ) → (α : ℕ → ⟨ C ⟩) (αworks : ((n m : ℕ) → (n ≡ m → ⊥) → (α n) ∧ (α m) ≡ 𝟘 )) 
        → α n ≡ (Iso.inv B∞C≃Σ (α , αworks) $cr singletons n) 
    module UniversalPropertyB∞ (universal : ( C : (BooleanRing ℓ-zero)) → 
      Σ[ up ∈ (UniversalPropertyB∞Dfn.B∞UP C) ] UniversalPropertyB∞Dfn.B∞UPFunctions C up ) where
      ℕ∞ : Type
      ℕ∞ = Σ[ α ∈ binarySequence ] ((n m : ℕ) → (n ≡ m → ⊥) → (α n) and (α m) ≡ false )
      ℕ∞=SpB∞ : Iso (SpGeneralBooleanRing B∞) ℕ∞ 
      ℕ∞=SpB∞ = fst $ universal BoolBR 
      module countablyPresentedB∞ (presented : is-countably-presented-alt B∞) where




