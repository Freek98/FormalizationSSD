module PropositionalTopology.Properties where
open import PropositionalTopology.Definitions

open import BinarySequences
open import Cubical.Foundations.Isomorphism
open Iso
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat.Bijections.Sum
open import Cubical.Data.Nat.Bijections.Product
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

isOpenPropHelperConstructor : (P : hProp ℓ-zero) → 
  (α : binarySequence) → (Σℕ α → ⟨ P ⟩) → (⟨ P ⟩ → ∥ Σℕ α ∥₁) → isOpenProp P 
isOpenPropHelperConstructor P α Σα→P P→∃α = ∣ α , P→Σα , Σα→P ∣₁ where
  P→Σα : ⟨ P ⟩ → Σℕ α
  P→Σα p = extractFirstHitInBinarySequence.extract α (P→∃α p)


OpenWitnessBinary⊔ : (P Q : hProp ℓ-zero) → isOpenWitness P → isOpenWitness Q → isOpenProp (P ⊔ Q)
OpenWitnessBinary⊔ P Q (α , P→α , α→P) (β , Q→β , β→Q) = isOpenPropHelperConstructor 
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

private
  and-true-left : (a b : Bool) → a and b ≡ true → a ≡ true
  and-true-left true  _ _ = refl
  and-true-left false _ p = ex-falso (false≢true p)

  and-true-right : (a b : Bool) → a and b ≡ true → b ≡ true
  and-true-right true  b p = p
  and-true-right false _ p = ex-falso (false≢true p)

OpenWitness⊓ : (P Q : hProp ℓ-zero) → isOpenWitness P → isOpenWitness Q → isOpenWitness (P ⊓ Q)
OpenWitness⊓ P Q (α , P→α , α→P) (β , Q→β , β→Q) = γ , P×Q→γ , γ→P×Q where
  γSplit : ℕ → ℕ → Bool
  γSplit n m = α n and β m 

  γ : binarySequence
  γ n = uncurry γSplit (Iso.inv ℕ×ℕ≅ℕ n)

  γ→P×Q : Σℕ γ → ⟨ P ⊓ Q ⟩
  γ→P×Q (k , r) = α→P (m , αm) , β→Q (n , βn) where
    mn = Iso.inv ℕ×ℕ≅ℕ k
    m = fst mn 
    n = snd mn
    αm : α m ≡ true
    αm = and-true-left (α m) (β n) r
    βn : β n ≡ true
    βn = and-true-right (α m) (β n) r
  P×Q→γ : ⟨ P ⊓ Q ⟩ → Σℕ γ
  P×Q→γ (p , q) = k , γk where
    mαm = P→α p
    m = fst mαm
    αm = snd mαm
    nβn = Q→β q
    n = fst nβn 
    αn = snd nβn
    k = Iso.fun ℕ×ℕ≅ℕ (m , n)
    γSplitmn : γSplit m n ≡ true 
    γSplitmn = cong₂ _and_ αm αn 
    γk : γ k ≡ true 
    γk = γ k 
           ≡⟨⟩ 
         uncurry γSplit (Iso.inv ℕ×ℕ≅ℕ k) 
           ≡⟨ cong (uncurry γSplit) (Iso.ret ℕ×ℕ≅ℕ (m , n)) ⟩  
         uncurry γSplit (m , n) 
           ≡⟨ γSplitmn ⟩ 
         true ∎

Open⊓ : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q → isOpenProp (P ⊓ Q)
Open⊓ P Q = PT.map2 (OpenWitness⊓ P Q)

ClosedWitnessBinary⊓ : (P Q : hProp ℓ-zero) → isClosedWitness P → isClosedWitness Q → isClosedWitness (P ⊓ Q)
ClosedWitnessBinary⊓ P Q (α , P→α , α→P) (β , Q→β , β→Q) = γ , P∧Q→γ , γ→P∧Q where
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



isPropIsClosedProp : {P : hProp ℓ-zero} → isProp (isClosedProp P)
isPropIsClosedProp = squash₁

isPropIsOpenProp : {P : hProp ℓ-zero} → isProp (isOpenProp P)
isPropIsOpenProp = squash₁
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

ℕ⊓ : {ℓ : Level} → (P : ℕ → hProp ℓ) → hProp ℓ
ℕ⊓ P = (∀ n → ⟨ P n ⟩) , isPropΠ λ n → snd (P n) 

ℕ⊔ : {ℓ : Level} → (P : ℕ → hProp ℓ) → hProp ℓ
ℕ⊔ P = ( ∃[ n ∈ ℕ ] ⟨ P n ⟩) , squash₁ 

ClosedWitnessℕ⊓ : 
  (P : ℕ → hProp ℓ-zero)
  → ((n : ℕ) → isClosedWitness (P n))
  → isClosedWitness (ℕ⊓ P)

ClosedWitnessℕ⊓ P w = β , ∀P→β , β→∀P where
  βSplit : ℕ → ℕ → Bool 
  βSplit n = fst (w n)

  β : binarySequence
  β = uncurry βSplit ∘ inv ℕ×ℕ≅ℕ 

  ∀P→β : ((n : ℕ) → ⟨ P n ⟩) → (k : ℕ) → β k ≡ false
  ∀P→β allP k = fst (snd (w n)) (allP n) m where
    n = fst (inv ℕ×ℕ≅ℕ k)
    m = snd (inv ℕ×ℕ≅ℕ k)

  β→∀P : ((k : ℕ) → β k ≡ false) → (n : ℕ) → ⟨ P n ⟩
  β→∀P allβ n = snd (snd (w n)) βSplitnm=0 where
    βSplitnm=0 : (m : ℕ) → βSplit n m ≡ false
    βSplitnm=0 m =
      βSplit n m
        ≡⟨ sym (cong (uncurry βSplit) (ret ℕ×ℕ≅ℕ (n , m))) ⟩
      β (fun ℕ×ℕ≅ℕ (n , m))
        ≡⟨ allβ (fun ℕ×ℕ≅ℕ (n , m)) ⟩
      false ∎

OpenWitnessℕ⊔ : (P : ℕ → hProp ℓ-zero)
  → (w : (n : ℕ) → isOpenWitness (P n))
  → isOpenWitness (ℕ⊔ P)
OpenWitnessℕ⊔ P w = β , ∃P→Σβ , ∣_∣₁ ∘ Σβ→ΣP  where
  βSplit : ℕ → ℕ → Bool 
  βSplit n = fst (w n)

  β : binarySequence
  β k = uncurry βSplit (inv ℕ×ℕ≅ℕ k) 

  Σβ→ΣP : Σℕ β → Σ[ n ∈ ℕ ] ⟨ P n ⟩
  Σβ→ΣP (k , βk=t) = n , snd (snd (w n)) (m , βSplitnm=t) where
    n = fst (inv ℕ×ℕ≅ℕ k)
    m = snd (inv ℕ×ℕ≅ℕ k)
    βSplitnm=t : βSplit n m ≡ true
    βSplitnm=t = βk=t

  ΣP→Σβ : Σ[ n ∈ ℕ ] ⟨ P n ⟩ → Σℕ β 
  ΣP→Σβ (n , pn) = let 
    (m , βSplitnm=t) = fst (snd (w n)) pn
    k = fun ℕ×ℕ≅ℕ (n , m)
    eq : inv ℕ×ℕ≅ℕ k ≡ (n , m)
    eq = ret ℕ×ℕ≅ℕ (n , m)
    βk=t : β k ≡ true
    βk=t = cong (λ p → βSplit (fst p) (snd p)) eq ∙ βSplitnm=t
    in  (k , βk=t) 

  ∃P→∃β : ∃[ n ∈ ℕ ] ⟨ P n ⟩ → ∥ Σℕ β ∥₁
  ∃P→∃β = PT.map ΣP→Σβ
  ∃P→Σβ :  ∃[ n ∈ ℕ ] ⟨ P n ⟩ → Σℕ β
  ∃P→Σβ = extract ∘ ∃P→∃β where
    open extractFirstHitInBinarySequence β
