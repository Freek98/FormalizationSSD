{-# OPTIONS --guardedness #-}

module CountablyPresentedBooleanRings.Examples.Bool where 
{- The goal of this module is to show that the standard Booleans form a countably presented Boolean algebra-}


open import BooleanRing.BooleanRingMaps
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty as ⊥ renaming (rec to ex-falso ; rec* to empty-func)
{- I got a unification problem for using rec* in EmptyQuotient, 
-- which is needed as that's what the image quotient uses, which maybe was a design mistake
-}

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.FreeBool
import BooleanRing.FreeBooleanRing.FreeBool as FB

open  import BooleanRing.FreeBooleanRing.SurjectiveTerms
open  import BooleanRing.FreeBooleanRing.freeBATerms

open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
--open import NaturalNumbersProperties.NBijection
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty as UP
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import BasicDefinitions
open import CommRingQuotients.EmptyQuotient
open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import BooleanRing.BoolRingUnivalence

open import Cubical.Algebra.CommRing.Univalence 

free⊥ : BooleanRing ℓ-zero
free⊥ = freeBA ⊥

module _ {ℓ : Level} (B : BooleanRing ℓ) where
  open BooleanRingStr (snd B) 
  max2 : Type ℓ
  max2 = (x : ⟨ B ⟩) → ((x ≡ 𝟘) ⊎ (x ≡ 𝟙))

  nontriv : Type ℓ
  nontriv = ¬ 𝟘 ≡ 𝟙 

  BoolBRCharacterisationHelper : nontriv → max2 → isEquiv (fst (BoolBR→ B))
  equiv-proof (BoolBRCharacterisationHelper 0≠1 0∨1) b with (0∨1 b)
  ... | inl b=0 = (false , sym b=0) , λ { (false , p) → Σ≡Prop (λ _ → is-set _ _) refl
                                        ; (true  , p) → ex-falso (0≠1 (sym (p ∙ b=0))) }
  ... | inr b=1 = (true  , sym b=1) , λ { (false , p) → ex-falso (0≠1      (p ∙ b=1))
                                        ; (true  , p) → Σ≡Prop (λ _ → is-set _ _) refl } 
  
  BoolBRCharacterisation : nontriv → max2 → BooleanRingEquiv BoolBR B
  BoolBRCharacterisation _ _ .fst .fst = fst $ BoolBR→ B
  BoolBRCharacterisation n m .fst .snd = BoolBRCharacterisationHelper n m
  BoolBRCharacterisation _ _ .snd      = snd $ BoolBR→ B

  open IsCommRingHom
  map→2→nontriv : (BoolHom B BoolBR) → nontriv
  map→2→nontriv (f , fHom) p = false≢true $ 
    false ≡⟨ (sym $ pres0 fHom) ⟩ 
    f 𝟘   ≡⟨ cong f p ⟩ f 𝟙 ≡⟨ pres1 fHom ⟩ 
    true  ∎

free→2 : {A : Type} → BoolHom (freeBA A)  BoolBR
free→2 {A} = (Iso.fun $ freeBA-universal-property A BoolBR) λ _ → false 

freeNonTriv : {A : Type} → nontriv (freeBA A) 
freeNonTriv {A} = map→2→nontriv (freeBA A) free→2

private module _ {ℓ : Level} {B : BooleanRing ℓ} where
  open BooleanRingStr (snd B) 
  open BooleanAlgebraStr (snd B)
  01+closed : (a b : ⟨ B ⟩) → (a ≡ 𝟘) ⊎ (a ≡ 𝟙) → (b ≡ 𝟘) ⊎ (b ≡ 𝟙) → (a + b ≡ 𝟘) ⊎ (a + b ≡ 𝟙)
  01+closed a b (inl a=0) (inl b=0) = inl $ 
    a + b ≡⟨ cong₂ (λ a b → a + b) a=0 b=0 ⟩ 
    𝟘 + 𝟘 ≡⟨ +IdL 𝟘 ⟩  
    𝟘     ∎
  01+closed a b (inl a=0) (inr b=1) = inr $ 
    a + b ≡⟨ cong₂ (λ a b → a + b) a=0 b=1 ⟩ 
    𝟘 + 𝟙 ≡⟨ +IdL 𝟙 ⟩  
    𝟙     ∎
  01+closed a b (inr a=1) (inl b=0) = inr $ 
    a + b ≡⟨ cong₂ (λ a b → a + b) a=1 b=0 ⟩ 
    𝟙 + 𝟘 ≡⟨ +IdR 𝟙 ⟩  
    𝟙     ∎
  01+closed a b (inr a=1) (inr b=1) = inl $ 
    a + b ≡⟨ cong₂ (λ a b → a + b) a=1 b=1 ⟩ 
    𝟙 + 𝟙 ≡⟨ characteristic2 ⟩  
    𝟘     ∎

  01·closed : (a b : ⟨ B ⟩) → (a ≡ 𝟘) ⊎ (a ≡ 𝟙) → (b ≡ 𝟘) ⊎ (b ≡ 𝟙) → (a · b ≡ 𝟘) ⊎ (a · b ≡ 𝟙)
  01·closed a b (inl a=0) (inl b=0) = inl $ 
    a · b ≡⟨ cong₂ (λ a b → a · b) a=0 b=0 ⟩ 
    𝟘 · 𝟘 ≡⟨ ·Idem 𝟘 ⟩  
    𝟘     ∎
  01·closed a b (inl a=0) (inr b=1) = inl $ 
    a · b ≡⟨ cong₂ (λ a b → a · b) a=0 b=1 ⟩ 
    𝟘 · 𝟙 ≡⟨ ∧IdR ⟩  
    𝟘     ∎
  01·closed a b (inr a=1) (inl b=0) = inl $ 
    a · b ≡⟨ cong₂ (λ a b → a · b) a=1 b=0 ⟩ 
    𝟙 · 𝟘 ≡⟨ ∧IdL ⟩  
    𝟘     ∎
  01·closed a b (inr a=1) (inr b=1) = inr $ 
    a · b ≡⟨ cong₂ (λ a b → a · b) a=1 b=1 ⟩ 
    𝟙 · 𝟙 ≡⟨ ·Idem 𝟙 ⟩  
    𝟙     ∎
  
  01-closed : (a : ⟨ B ⟩) → (a ≡ 𝟘) ⊎ (a ≡ 𝟙) → (- a ≡ 𝟘) ⊎ (- a ≡ 𝟙)
  01-closed _ (inl p) = inl (cong -_ p ∙ sym -IsId)
  01-closed _ (inr p) = inr (cong -_ p ∙ sym -IsId)
  

module _ where
  open BooleanRingStr (snd free⊥)
  private 
    π : freeBATerms ⊥ → ⟨ free⊥ ⟩
    π = fst includeBATermsSurj 
  private opaque
    unfolding includeBATermsSurj
    max2free⊥Helper : (x : freeBATerms ⊥) → (π x ≡ 𝟘) ⊎ (π x ≡ 𝟙)
    max2free⊥Helper (Tconst false) = inl refl
    max2free⊥Helper (Tconst true)  = inr refl
    max2free⊥Helper (-T x)    = 01-closed {B = free⊥} (π x)       (max2free⊥Helper x) 
    max2free⊥Helper (x +T y)  = 01+closed {B = free⊥} (π x) (π y) (max2free⊥Helper x) (max2free⊥Helper y)
    max2free⊥Helper (x ·T y)  = 01·closed {B = free⊥} (π x) (π y) (max2free⊥Helper x) (max2free⊥Helper y) 

  max2free⊥ : max2 free⊥
  max2free⊥ b = PT.rec 
    (λ { (inl b=0) (inl b=0') → cong inl $ is-set b 𝟘 b=0 b=0'
       ; (inl b=0) (inr b=1 ) → ex-falso (freeNonTriv (sym b=0 ∙ b=1))
       ; (inr b=1) (inl b=0 ) → ex-falso (freeNonTriv (sym b=0 ∙ b=1))
       ; (inr b=1) (inr b=1') → cong inr $ is-set b 𝟙 b=1 b=1' }) 
    (λ (t , πt=b) → subst (λ a → (a ≡ 𝟘) ⊎ (a ≡ 𝟙)) πt=b (max2free⊥Helper t)) 
    (snd includeBATermsSurj b)

  2≃free⊥ : BooleanRingEquiv BoolBR free⊥ 
  2≃free⊥ = (BoolBRCharacterisation free⊥ freeNonTriv max2free⊥)
  
  free⊥=2 : free⊥ ≡ BoolBR
  free⊥=2 = sym (uaBoolRing 2≃free⊥)

⊥ind : {A : Type} → {b : ⊥} →  (a : A) → ex-falso b ≡ a
⊥ind {b = ()} 

count⊥ : has-Countability-structure ⊥
count⊥ = ((λ n → false) , iso ex-falso (λ (n , f=t) → false≢true f=t) (λ b → ⊥ind b) ⊥.elim)  

is-cp-free⊥ : has-Boole-ω' free⊥
is-cp-free⊥ = free-on-countable-has-freeℕ-presentation ⊥ count⊥

is-cp-2 : has-Boole-ω' BoolBR
is-cp-2 = subst has-Boole-ω' free⊥=2 is-cp-free⊥ 

BoolCP : countablyPresentedBooleanRing
BoolCP = BoolBR , ∣ is-cp-2 ∣₁
