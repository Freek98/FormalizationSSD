module BinarySequences.deMorganLLPO where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; doubleℕ)
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as PT

open import BasicDefinitions
open import BinarySequences.Definitions
open import BinarySequences.Properties

open import OmnisciencePrinciples.LLPO
open import LLMGeneratedFixes.Parity
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Foundations.Function

module deMorganOpen
  (α β : binarySequence)
  (αAtMostOnce : hits1AtMostOnce α) (βAtMostOnce : hits1AtMostOnce β)
  (notBoth : ¬ (Σℕ1 α × Σℕ1 β)) where
  open Interleave α β

  γ : binarySequence
  γ = interleave α β

  γAtMostOnce : hits1AtMostOnce γ
  γAtMostOnce n m γn γm = case (even-or-odd n , even-or-odd m) return (λ _ → n ≡ m) of λ
    { (inl (k , n=2k)   , inl (l , m=2l)  ) →
      n=2k ∙ cong doubleℕ
      (αAtMostOnce k l (evenHit n k n=2k γn) (evenHit m l m=2l γm))
      ∙ sym m=2l
    ; (inl (k , n=2k)   , inr (l , m=2l+1)) → ex-falso (notBoth $
      (k , evenHit n k n=2k   γn ) ,
      (l , oddHit  m l m=2l+1 γm))
    ; (inr (k , n=2k+1) , inl (l , m=2l)  ) → ex-falso (notBoth $
      (l , evenHit m l m=2l   γm ) ,
      (k , oddHit  n k n=2k+1 γn))
    ; (inr (k , n=2k+1) , inr (l , m=2l+1)) → n=2k+1 ∙ cong (suc ∘ doubleℕ)
      (βAtMostOnce k l (oddHit n k n=2k+1 γn) (oddHit m l m=2l+1 γm))
      ∙ sym m=2l+1 } where
      evenHit : (n k : ℕ) → n ≡ doubleℕ k → γ n ≡ true → α k ≡ true
      evenHit n k n≡2k   hit = sym (fstOnEvens k) ∙ cong γ (sym n≡2k)   ∙ hit
      oddHit  : (m l : ℕ) → m ≡ suc (doubleℕ l) → γ m ≡ true → β l ≡ true
      oddHit  m l m≡2l+1 hit = sym (sndOnOdds l) ∙ cong γ (sym m≡2l+1) ∙ hit

  deMorganConcl : LLPOExplicitAt (γ , γAtMostOnce) → ( (¬ Σℕ1 α) ⊎ (¬ Σℕ1 β))
  deMorganConcl (inl γ2n=false) = inl λ ((n , αn)) → false≢true $
    sym (γ2n=false n) ∙ fstOnEvens n ∙ αn
  deMorganConcl (inr γ2n+1=false) = inr λ ((m , βm)) → false≢true $
    sym (γ2n+1=false m) ∙ sndOnOdds m ∙ βm

  LLPO→deMorganOpen : LLPO → ∥(¬ Σℕ1 α) ⊎ (¬ Σℕ1 β) ∥₁
  LLPO→deMorganOpen llpo = PT.map deMorganConcl $ llpo (γ , γAtMostOnce)

LLPO→deMorganOpen : LLPO → (α β : binarySequence) →
  (hits1AtMostOnce α) → hits1AtMostOnce β →
  ¬ (Σℕ1 α × Σℕ1 β) → ∥(¬ Σℕ1 α) ⊎ (¬ Σℕ1 β) ∥₁
LLPO→deMorganOpen llpo α β α1 β1 nb = deMorganOpen.LLPO→deMorganOpen α β α1 β1 nb llpo

