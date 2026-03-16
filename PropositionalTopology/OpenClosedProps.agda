module PropositionalTopology.OpenClosedProps where
open import QuickFixes
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Logic
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary hiding (¬_)
open import QuickFixes
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import BasicDefinitions

import BooleanRing.BooleanRingQuotients.QuotientBool as QB
import Cubical.Data.Sum as ⊎

isOpenWitness : hProp ℓ-zero → Type₀
isOpenWitness P = Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ (∃[ n ∈ ℕ ] α n ≡ true)

isOpenProp : hProp ℓ-zero → Type₀
isOpenProp P = ∥ isOpenWitness P ∥₁

isOpenPropHelperConstructor : (P : hProp ℓ-zero) → 
  (α : binarySequence) → (Σℕ α → ⟨ P ⟩) → (⟨ P ⟩ → ∥ Σℕ α ∥₁) → isOpenProp P 
isOpenPropHelperConstructor P α Σα→P P→∃α = ∣ (α , P→∃α , PT.rec (snd P) Σα→P) ∣₁ 

isPropIsOpenProp : {P : hProp ℓ-zero} → isProp (isOpenProp P)
isPropIsOpenProp = squash₁

or-true→⊎ : (a b : Bool) → a or b ≡ true → (a ≡ true) ⊎ (b ≡ true)
or-true→⊎ false false x = ex-falso (false≢true x)
or-true→⊎ false true _ = ⊎.inr refl
or-true→⊎ true false _ = ⊎.inl refl
or-true→⊎ true true  _ = ⊎.inl refl 

Open⊔ : (P Q : hProp ℓ-zero) → isOpenWitness P → isOpenWitness Q → isOpenProp (P ⊔ Q)
Open⊔ P Q (α , P→α , α→P) (β , Q→β , β→Q) = {! !} where
  γ : binarySequence 
  γ k = α k or β k 
  P⊎Q→γ : ⟨ P ⟩ ⊎ ⟨ Q ⟩  → Σ[ n ∈ ℕ ] γ n ≡ true
  P⊎Q→γ (⊎.inl p) = case P→α p return (λ _ → Σ-syntax ℕ λ n → γ n ≡ true) of {! !}
 -- PT.rec (λ 
 --   (n , αn=1) → n , cong (λ a → a or (β n)) αn=1) ? 
--  P⊎Q→γ (⊎.inr q) = case Q→β q return (λ _ → Σ-syntax ℕ λ n → γ n ≡ true) of λ 
--    (n , βn=1) → n , cong (λ b → (α n) or b) βn=1 ∙ or-zeroʳ (α n) 
--  γ→P⊎Q : Σ[ n ∈ ℕ ] γ n ≡ true → ⟨ P ⟩ ⊎ ⟨ Q ⟩
--  γ→P⊎Q (n , γn=1) = case or-true→⊎ (α n) (β n) γn=1 of λ 
--    { (⊎.inl αn=1) → ⊎.inl (α→P (n , αn=1))
--    ; (⊎.inr βn=1) → ⊎.inr (β→Q (n , βn=1)) } 
--  γ→P∨Q : Σℕ γ → ⟨ P ⊔ Q ⟩ 
--  γ→P∨Q = ∣_∣₁ ∘ γ→P⊎Q 
--
--Open⊓ : (P Q : hProp ℓ-zero) → isOpenWitness P → isOpenWitness Q → isOpenWitness (P ⊓ Q)
--Open⊓ P Q (α , P→α , α→P) (β , Q→β , β→Q) = {! !} 

isClosedWitness : hProp ℓ-zero → Type₀
isClosedWitness P = Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) →  α n ≡ false)

isClosedProp : hProp ℓ-zero → Type₀
isClosedProp P = ∥ isClosedWitness P ∥₁ 

isPropIsClosedProp : {P : hProp ℓ-zero} → isProp (isClosedProp P)
isPropIsClosedProp = squash₁

Open : Type₁
Open = Σ[ P ∈ hProp ℓ-zero ] isOpenProp P

Closed : Type₁
Closed = Σ[ P ∈ hProp ℓ-zero ] isClosedProp P

negOpenWitnessIsClosedWitness : (P : hProp ℓ-zero) → isOpenWitness P → isClosedWitness (¬ P) 
negOpenWitnessIsClosedWitness P (α , P→∃α , ∃α→P) = 
  α , ¬P→∀α , ∀α→¬P where
  ¬P→∀α : ⟨ ¬ P ⟩ → (n : ℕ) → α n ≡ false 
  ¬P→∀α ¬p n = ¬true→false (α n) λ αn=t → 
    ¬p (∃α→P ∣ (n , αn=t) ∣₁ )
  ∀α→¬P : ((n : ℕ) → α n ≡ false) → ⟨ ¬ P ⟩ 
  ∀α→¬P ∀n¬αn p = case (P→∃α p) of 
    λ f → {! !} --((n , αn=t)) → true≢false $ 
--    true ≡⟨ sym αn=t ⟩ α n ≡⟨ ∀n¬αn n ⟩ false ∎


negOpenIsClosed : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp (¬ P)
negOpenIsClosed P = PT.map (negOpenWitnessIsClosedWitness P)

decIsOpen : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isOpenProp P
decIsOpen P (yes p) = ∣ (λ _ → true) , (λ p → ∣ 0 , refl ∣₁) , (λ _ → p) ∣₁
decIsOpen P (no ¬p) = ∣ (λ _ → false) , (λ p₁ → ex-falso (¬p p₁)) , 
  PT.rec (snd P) (λ ((_ , f=t)) → ex-falso (false≢true f=t)) ∣₁

decIsClosed : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isClosedProp P
decIsClosed P (yes p) = ∣ (λ _ → false) , (λ _ _ → refl) , (λ _ → p) ∣₁
decIsClosed P (no ¬p) = ∣ (λ _ → true) , (λ p₁ → ex-falso (¬p p₁)) , 
  (λ f → ex-falso (true≢false (f 0))) ∣₁



