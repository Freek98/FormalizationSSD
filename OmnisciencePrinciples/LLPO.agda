module OmnisciencePrinciples.LLPO where
open import CountablyPresentedBooleanRings.Examples.NFinCofin

open import BooleanRing.SubBooleanRing
open import Parity
open import CategoryTheory.StuffFromStoneAboutBAs
open import Cubical.Categories.Functor
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
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum as ⊎ 
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Nat.IsEven
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

module EquivalenceRequirements (B : BooleanRing ℓ-zero) (C : BooleanRing ℓ-zero) where
  Booleω-has-prods : Type _
  Booleω-has-prods = is-countably-presented-alt B → is-countably-presented-alt C → is-countably-presented-alt (B ×BR C)
  AntiEquivalenceOnMaps : Type
  AntiEquivalenceOnMaps = is-countably-presented-alt B → is-countably-presented-alt C → 
    isIso {A = BoolHom B C} {B = SpGeneralBooleanRing C → SpGeneralBooleanRing B } λ f g → g ∘cr f 
  ProdsUP : Type _
  ProdsUP = (D : BooleanRing ℓ-zero) → 
    Iso (BoolHom (B ×BR C) D) (BoolHom B D ⊎ BoolHom C D)
  SpAntiEquivalenceOnProd : ProdsUP → Iso (SpGeneralBooleanRing (B ×BR C)) (SpGeneralBooleanRing B ⊎ SpGeneralBooleanRing C) 
  SpAntiEquivalenceOnProd up = up BoolBR 
  

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
    module UniversalPropertyB∞ (universal : (C : (BooleanRing ℓ-zero)) → 
      Σ[ up ∈ (UniversalPropertyB∞Dfn.B∞UP C) ] UniversalPropertyB∞Dfn.B∞UPFunctions C up ) where
      ℕ∞ : Type
      ℕ∞ = Σ[ α ∈ binarySequence ] ((n m : ℕ) → (n ≡ m → ⊥) → (α n) and (α m) ≡ false)

      LLPOExplicitAt : ℕ∞ → Type
      LLPOExplicitAt (α , _) = 
        (∀ (n : ℕ) → α (double n) ≡ false) ⊎ (∀ (n : ℕ) → α (suc $ double n) ≡ false)
      LLPO : Type 
      LLPO = (x : ℕ∞) →  ∥ LLPOExplicitAt x ∥₁

      module HowWeDoIt where
        splitIntoEvens : binarySequence → binarySequence 
        splitIntoEvens α = evenOddElim (λ n ((k , n=2k)) → α k) (λ n oddn → false)

        splitIntoEvensℕ∞ : ℕ∞ → ℕ∞
        splitIntoEvensℕ∞ (α , αkl=1) .fst = splitIntoEvens α
        splitIntoEvensℕ∞ (α , αkl=1) .snd m n m≠n with (even-or-odd m) | (even-or-odd n) 
        ... | inl (k , m=2k) | inl (l , n=2l) = αkl=1 k l λ k=l → m≠n $
          m ≡⟨ m=2k ⟩ double k ≡⟨ cong double k=l ⟩ double l ≡⟨ sym n=2l ⟩ n ∎
        ... | inl (k , _) | inr _ = and-zeroʳ (α k)
        ... | inr modd  | _ = refl

        splitIntoOdds : binarySequence → binarySequence 
        splitIntoOdds α = evenOddElim (λ n evenn → false) (λ n ((k , n=2k+1)) → α k)

        splitIntoOddsℕ∞ : ℕ∞ → ℕ∞
        splitIntoOddsℕ∞ (α , αkl=1) .fst = splitIntoOdds α
        splitIntoOddsℕ∞ (α , αkl=1) .snd m n m≠n with (even-or-odd m) | (even-or-odd n) 
        ... | inr (k , m=2k+1) | inr (l , n=2l+1) = αkl=1 k l λ k=l → m≠n $
          m              ≡⟨ m=2k+1 ⟩ 
          suc (double k) ≡⟨ cong (suc ∘ double) k=l ⟩ 
          suc (double l) ≡⟨ sym n=2l+1 ⟩ 
          n              ∎
        ... | inr (k , _) | inl _ = and-zeroʳ (α k)
        ... | inl modd  | _ = refl
        
        e : ℕ∞ ⊎ ℕ∞ → ℕ∞
        e = ⊎.rec splitIntoEvensℕ∞ splitIntoOddsℕ∞ 

        e-fibers→LLPO-explicit : ∀ (x : ℕ∞) → fiber e x → LLPOExplicitAt x
        e-fibers→LLPO-explicit x (inl β , eβ=α) = inr λ k → 
         (sym $ cong (λ x' → fst x' (suc (double k))) eβ=α) ∙ evenOddElim-odd k
        e-fibers→LLPO-explicit x (inr β , eβ=α) = inl λ k → 
         (sym $ cong (λ x' → fst x' (double k)) eβ=α) ∙ evenOddElim-even k

        e-surj→LLPO : isSurjection e → LLPO
        e-surj→LLPO esurj x = PT.map (e-fibers→LLPO-explicit x) (esurj x) 
      
      open HowWeDoIt

      ℕ∞=SpB∞ : Iso (SpGeneralBooleanRing B∞) ℕ∞ 
      ℕ∞=SpB∞ = fst $ universal BoolBR 
      module countablyPresentedB∞ 
        (presented : is-countably-presented-alt B∞) 
        (eqOnMaps : (B C : BooleanRing ℓ-zero) → EquivalenceRequirements.AntiEquivalenceOnMaps B C)
        where
        open EquivalenceRequirements B∞ B∞ 
        module prodProps (prodPresented : Booleω-has-prods) (prodUP : ProdsUP) where
          ℕ∞+ℕ∞=SpProd : Iso (SpGeneralBooleanRing (B∞ ×BR B∞)) (ℕ∞ ⊎ ℕ∞)
          ℕ∞+ℕ∞=SpProd = compIso (SpAntiEquivalenceOnProd prodUP) (⊎Iso ℕ∞=SpB∞ ℕ∞=SpB∞)
          open Functor
          module fProps 
            (prodIso : Iso (BoolHom B∞ (B∞ ×BR B∞)) (ℕ∞ ⊎ ℕ∞ → ℕ∞))
            (f : BoolHom B∞ (B∞ ×BR B∞)) 
            (fInj : isInjectiveBoolHom (B∞ , presented) ((B∞ ×BR B∞) , prodPresented presented presented) f) 
            (fcorrespondsToe : prodIso .Iso.fun f ≡ e ) where


        




