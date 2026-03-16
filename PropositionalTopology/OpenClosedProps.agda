module PropositionalTopology.OpenClosedProps where
open import QuickFixes
open import BinarySequences
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat.Bijections.Sum
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
isOpenWitness P = Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ (Σ[ n ∈ ℕ ] α n ≡ true)

isOpenProp : hProp ℓ-zero → Type₀
isOpenProp P = ∥ isOpenWitness P ∥₁

isOpenPropHelperConstructor : (P : hProp ℓ-zero) → 
  (α : binarySequence) → (Σℕ α → ⟨ P ⟩) → (⟨ P ⟩ → ∥ Σℕ α ∥₁) → isOpenProp P 
isOpenPropHelperConstructor P α Σα→P P→∃α = ∣ α , P→Σα , Σα→P ∣₁ where
  P→Σα : ⟨ P ⟩ → Σℕ α
  P→Σα p = extractFirstHitInBinarySequence.extract α (P→∃α p)

isPropIsOpenProp : {P : hProp ℓ-zero} → isProp (isOpenProp P)
isPropIsOpenProp = squash₁

Open⊔ : (P Q : hProp ℓ-zero) → isOpenWitness P → isOpenWitness Q → isOpenProp (P ⊔ Q)
Open⊔ P Q (α , P→α , α→P) (β , Q→β , β→Q) = isOpenPropHelperConstructor 
  (P ⊔ Q) γ γ→P∨Q (PT.map P⊎Q→γ) where
  γ : binarySequence 
  γ k = α k or β k 
  P⊎Q→γ : ⟨ P ⟩ ⊎ ⟨ Q ⟩  → Σ[ n ∈ ℕ ] γ n ≡ true
  P⊎Q→γ (⊎.inl p) = case P→α p return (λ _ → Σ-syntax ℕ λ n → γ n ≡ true) of λ 
    (n , αn=1) → n , cong (λ a → a or (β n)) αn=1
  P⊎Q→γ (⊎.inr q) = case Q→β q return (λ _ → Σ-syntax ℕ λ n → γ n ≡ true) of λ 
    (n , βn=1) → n , cong (λ b → (α n) or b) βn=1 ∙ or-zeroʳ (α n) 
  γ→P⊎Q : Σ[ n ∈ ℕ ] γ n ≡ true → ⟨ P ⟩ ⊎ ⟨ Q ⟩
  γ→P⊎Q (n , γn=1) = case or-true→⊎ (α n) (β n) γn=1 of λ 
    { (⊎.inl αn=1) → ⊎.inl (α→P (n , αn=1))
    ; (⊎.inr βn=1) → ⊎.inr (β→Q (n , βn=1)) } 
  γ→P∨Q : Σℕ γ → ⟨ P ⊔ Q ⟩ 
  γ→P∨Q = ∣_∣₁ ∘ γ→P⊎Q 

Open⊓ : (P Q : hProp ℓ-zero) → isOpenWitness P → isOpenWitness Q → isOpenWitness (P ⊓ Q)
Open⊓ P Q (α , P→α , α→P) (β , Q→β , β→Q) = {! !} where
  open MakeIncreasing
  γ : binarySequence 
  γ k = makeIncreasing α k and makeIncreasing β k 
  γ→P×Q : Σ[ n ∈ ℕ ] γ n ≡ true → ⟨ P ⊓ Q ⟩
  γ→P×Q (n , γn=1) .fst = α→P (extractFromMakeIncreasing α n (fst $ and-true→× _ _ γn=1))
  γ→P×Q (n , γn=1) .snd = β→Q (extractFromMakeIncreasing β n (snd $ and-true→× _ _ γn=1)) 
  P×Q→γ : ⟨ P ⊓ Q ⟩ → Σ[ n ∈ ℕ ] γ n ≡ true
  P×Q→γ (p , q) = {!  !} 

isClosedWitness : hProp ℓ-zero → Type₀
isClosedWitness P = Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) →  α n ≡ false)

Closed⊓ : (P Q : hProp ℓ-zero) → isClosedWitness P → isClosedWitness Q → isClosedWitness (P ⊓ Q)
Closed⊓ P Q (α , P→α , α→P) (β , Q→β , β→Q) = γ , P∧Q→γ , γ→P∧Q where
  γSplit : ℕ ⊎ ℕ → Bool
  γSplit = ⊎.rec α β
  γSplit0→P∧Q : ((p : ℕ ⊎ ℕ) → γSplit p ≡ false) → ⟨ P ⊓ Q ⟩ 
  γSplit0→P∧Q γSplit0 .fst = α→P λ n → γSplit0 (⊎.inl n)
  γSplit0→P∧Q γSplit0 .snd = β→Q λ n → γSplit0 (⊎.inr n) 
  γ : binarySequence 
  γ = γSplit ∘ ℕ⊎ℕ≅ℕ .Iso.inv 
  γ→P∧Q : ((n : ℕ) → γ n ≡ false) → ⟨ P ⊓ Q ⟩
  γ→P∧Q γ=0 = γSplit0→P∧Q λ p → 
    γSplit p 
      ≡⟨ cong γSplit (sym $ ℕ⊎ℕ≅ℕ .Iso.ret p) ⟩ 
    γ (ℕ⊎ℕ≅ℕ .Iso.fun p) 
      ≡⟨ γ=0 (ℕ⊎ℕ≅ℕ .Iso.fun p) ⟩  
    false ∎  

  P∧Q→γ : ⟨ P ⊓ Q ⟩ → (n : ℕ) → γ n ≡ false
  P∧Q→γ P∧Q n with (ℕ⊎ℕ≅ℕ .Iso.inv n) 
  ... | _⊎_.inl m = P→α (fst P∧Q) m
  ... | _⊎_.inr m = Q→β (snd P∧Q) m 

isClosedProp : hProp ℓ-zero → Type₀
isClosedProp P = ∥ isClosedWitness P ∥₁ 

isPropIsClosedProp : {P : hProp ℓ-zero} → isProp (isClosedProp P)
isPropIsClosedProp = squash₁

Open : Type₁
Open = Σ[ P ∈ hProp ℓ-zero ] isOpenProp P

Closed : Type₁
Closed = Σ[ P ∈ hProp ℓ-zero ] isClosedProp P

negOpenWitnessIsClosedWitness : (P : hProp ℓ-zero) → isOpenWitness P → isClosedWitness (¬ P) 
negOpenWitnessIsClosedWitness P (α , P→Σα , Σα→P) = 
  α , ¬P→∀α , ∀α→¬P where
  ¬P→∀α : ⟨ ¬ P ⟩ → (n : ℕ) → α n ≡ false 
  ¬P→∀α ¬p n = ¬true→false (α n) λ αn=t → 
    ¬p (Σα→P (n , αn=t))
  ∀α→¬P : ((n : ℕ) → α n ≡ false) → ⟨ ¬ P ⟩ 
  ∀α→¬P ∀n¬αn p = case (P→Σα p) of 
    λ ((n , αn=t)) → true≢false $ 
    true ≡⟨ sym αn=t ⟩ α n ≡⟨ ∀n¬αn n ⟩ false ∎


negOpenIsClosed : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp (¬ P)
negOpenIsClosed P = PT.map (negOpenWitnessIsClosedWitness P)

decIsOpen : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isOpenProp P
decIsOpen P (yes p) = ∣ (λ _ → true) , (λ _ → 0 , refl) , (λ _ → p) ∣₁
decIsOpen P (no ¬p) = ∣ (λ _ → false) , (λ p₁ → ex-falso (¬p p₁)) , (λ x → ex-falso (false≢true (snd x))) ∣₁

decIsClosed : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isClosedProp P
decIsClosed P (yes p) = ∣ (λ _ → false) , (λ _ _ → refl) , (λ _ → p) ∣₁
decIsClosed P (no ¬p) = ∣ (λ _ → true) , (λ p₁ → ex-falso (¬p p₁)) , (λ f → ex-falso (true≢false (f 0))) ∣₁



