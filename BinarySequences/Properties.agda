module BinarySequences.Properties where 

open import BinarySequences.Definitions

open import Cubical.Data.Sigma
open import Cubical.Data.Bool renaming ( _≤_ to _≤B_ ; _≥_ to _≥B_ ; _≟_ to _=B_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Bijections.Sum

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕTrich_)
open <-Reasoning

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

module _ (α : binarySequence) where
  isProp∀ℕ0 : isProp (∀ℕ0 α) 
  isProp∀ℕ0 = isPropΠ λ n → isSetBool (α n) false

  isProp∃ℕ1 : isProp (∃ℕ1 α)
  isProp∃ℕ1 = squash₁ 

  ¬Σℕ1→∀ℕ0 : ¬ Σℕ1 α → ∀ℕ0 α
  ¬Σℕ1→∀ℕ0 ¬Σℕ n = ¬true→false (α n) λ αn=1 → ¬Σℕ (n , αn=1)

  ∀ℕ0→¬Σℕ1 : ∀ℕ0 α → ¬ Σℕ1 α
  ∀ℕ0→¬Σℕ1 all0 (n , αn=1) = true≢false $ sym αn=1 ∙ all0 n
  
  ¬∃ℕ→¬Σℕ : ¬ ∃ℕ1 α → ¬ Σℕ1 α 
  ¬∃ℕ→¬Σℕ = _∘ ∣_∣₁ 

  ¬∃ℕ1→∀ℕ0 : ¬ ∃ℕ1 α → ∀ℕ0 α
  ¬∃ℕ1→∀ℕ0 = ¬Σℕ1→∀ℕ0 ∘ ¬∃ℕ→¬Σℕ 

  ∀ℕ0→¬∃ℕ1 : ∀ℕ0 α → ¬ ∃ℕ1 α
  ∀ℕ0→¬∃ℕ1 all0 exists1 = PT.rec isProp⊥ (∀ℕ0→¬Σℕ1 all0) exists1 

  isPropHits1AtMostOnce : isProp (hits1AtMostOnce α)
  isPropHits1AtMostOnce = isPropΠ4 λ n m _ _ → isSetℕ n m 
  
  module ℕ∞SequenceProperties (atMostOnce : hits1AtMostOnce α) where 
    isPropΣℕ1 : isProp (Σℕ1 α)
    isPropΣℕ1 (n , αn) (m , αm) = Σ≡Prop (λ n → isSetBool (α n) true) (atMostOnce n m αn αm) 

    splitSupportΣℕ1 : SplitSupport $ Σℕ1 α
    splitSupportΣℕ1 = PT.rec isPropΣℕ1 λ x → x 

atMostOnce→NotTwice : (α : binarySequence) → hits1AtMostOnce α → hits1NotTwice α 
atMostOnce→NotTwice α atMostOnce n m n≢m = case (α m =B false , α n =B false) 
  return (λ _ → α m and α n ≡ false) of λ 
    { (yes p , yes p₁) → cong₂ _and_ p p₁
    ; (yes p , no ¬p) → cong (λ b → b and α n) p
    ; (no ¬p , yes p) → cong (_and_ (α m)) p ∙ and-zeroʳ (α m)
    ; (no ¬p , no ¬p₁) → ex-falso (n≢m (atMostOnce m n (¬false→true (α m) ¬p) (¬false→true (α n) ¬p₁))) } 

notTwice→AtMostOnce : (α : binarySequence) → hits1NotTwice α → hits1AtMostOnce α 
notTwice→AtMostOnce α notTwice m n αm=1 αn=1 = case discreteℕ m n return (λ _ → m ≡ n) of 
  λ { (yes p) → p
    ; (no ¬p) → ex-falso (true≢false $ 
      true 
        ≡⟨ sym $ cong₂ _and_ αm=1 αn=1 ⟩ 
      α m and α n 
        ≡⟨ notTwice n m ¬p ⟩ 
      false ∎ ) } 

private 
  and-elim-left : (a b : Bool) → a and b ≡ true → a ≡ true 
  and-elim-left false b p = ex-falso (false≢true p)
  and-elim-left true _  _ = refl 

  and-elim-right : (a b : Bool) → a and b ≡ true → b ≡ true 
  and-elim-right a false p = ex-falso (true≢false (sym p ∙ and-comm a false))
  and-elim-right _ true  _ = refl

  deMorganBool : (a b : Bool) → a and b ≡ false → (a ≡ false) ⊎ (b ≡ false)
  deMorganBool false _ _ = inl refl
  deMorganBool true  b p = inr p

  not≡true→≡false : (b : Bool) → not b ≡ true → b ≡ false
  not≡true→≡false false _ = refl
  not≡true→≡false true  p = ex-falso (false≢true p)

  not≡false→≡true : (b : Bool) → not b ≡ false → b ≡ true
  not≡false→≡true false p = ex-falso (true≢false p)  
  not≡false→≡true true  _ = refl
  
  ¬true→not≡true : (b : Bool) → ¬ b ≡ true → not b ≡ true
  ¬true→not≡true b p = cong not $ ¬true→false b p
  
module AtMostOneHit (α : binarySequence) where
  noHitBefore : binarySequence
  noHitBefore zero = true
  noHitBefore (suc n) = (noHitBefore n) and (not $ α n)
  
  onlyFirstHit : binarySequence
  onlyFirstHit n = (α n) and (noHitBefore n)
    
  getEarlierHit : (n : ℕ) → noHitBefore n ≡ false → Σ[ k ∈ ℕ ] (k < n) × (α k ≡ true)
  getEarlierHit zero    p = ex-falso (true≢false p)         
  getEarlierHit (suc n) p = case deMorganBool (noHitBefore n) (not (α n)) p of λ
    { (inl nHBn)  → let (k , k<n , αk) = getEarlierHit n nHBn in k , ≤-suc k<n , αk
    ; (inr notαn) → n , ≤-refl , not≡false→≡true (α n) notαn }
  
  boundedαToFirstHit : (bound n : ℕ) → n < bound → α n ≡ true → Σℕ1 onlyFirstHit
  boundedαToFirstHit zero    n n<0  _  = ex-falso (¬-<-zero n<0)
  boundedαToFirstHit (suc b) n n<sb αn = case noHitBefore n =B true of λ
    { (yes nHBn) → n , cong₂ _and_ αn nHBn
    ; (no ¬nHBn) → let (k , k<n , αk) = getEarlierHit n (¬true→false (noHitBefore n) ¬nHBn)
                   in boundedαToFirstHit b k (≤-trans k<n (pred-≤-pred n<sb)) αk }
                   -- Note that in this final call, the bound is smaller!
  
  αToOnlyFirstHit : Σℕ1 α → Σℕ1 onlyFirstHit
  αToOnlyFirstHit (n , αn) = boundedαToFirstHit (suc n) n ≤-refl αn
  
  onlyFirstHitToα : (n : ℕ) → onlyFirstHit n ≡ true → α n ≡ true
  onlyFirstHitToα n = and-elim-left (α n) (noHitBefore n) 
 
  allFalseBefore→noHitBefore : (n : ℕ) → ((k : ℕ) → k < n → α k ≡ false) → noHitBefore n ≡ true
  allFalseBefore→noHitBefore zero    _    = refl
  allFalseBefore→noHitBefore (suc n) all0 =
    cong₂ _and_
      (allFalseBefore→noHitBefore n (λ k k<n → all0 k (≤-suc k<n)))
      (cong not (all0 n ≤-refl))

  noHitBeforePred : (n : ℕ) → noHitBefore (suc n) ≡ true → noHitBefore n ≡ true
  noHitBeforePred n = and-elim-left (noHitBefore n) (not $ α n)

  noHitBeforeToNoTα : (n : ℕ) → noHitBefore (suc n) ≡ true → α n ≡ false
  noHitBeforeToNoTα n noHitBeforeSn = not≡true→≡false (α n) (and-elim-right (noHitBefore n) (not $ α n) noHitBeforeSn)

  noHitBefore→SoFarAll0 : (n : ℕ) → noHitBefore n ≡ true → (k : ℕ) → k < n → α k ≡ false 
  noHitBefore→SoFarAll0 zero _ k k<n = ex-falso (¬-<-zero k<n)
  noHitBefore→SoFarAll0 (suc n) noHitBeforeSn=1 k k<sucn = case ≤-split k<sucn of 
    λ { (inl Sk<Sn) → 
      noHitBefore→SoFarAll0 n (noHitBeforePred n noHitBeforeSn=1) k (pred-≤-pred Sk<Sn)
      ; (inr Sk=Sn) → 
      noHitBeforeToNoTα k (cong noHitBefore Sk=Sn ∙ noHitBeforeSn=1) } 

  onlyFirstHitToNoEarlierHit : (n : ℕ) → onlyFirstHit n ≡ true → (k : ℕ) → k < n → α k ≡ false 
  onlyFirstHitToNoEarlierHit n = noHitBefore→SoFarAll0 n ∘ and-elim-right (α n) (noHitBefore n) 
  atMostOneHitInOnlyFirstHit : hits1AtMostOnce onlyFirstHit
  atMostOneHitInOnlyFirstHit m n fHm fHn = case (m =ℕTrich n) return (λ _ → m ≡ n) of 
    λ { (lt m<n) → ex-falso $ <case m n fHm fHn m<n
      ; (eq m=n) → m=n
      ; (gt n<m) → ex-falso $ <case n m fHn fHm n<m } where
        <case : (k l : ℕ) → onlyFirstHit k ≡ true → onlyFirstHit l ≡ true → ¬ k < l
        <case k l fHk fHl k<l = true≢false $ 
          true ≡⟨ sym $ onlyFirstHitToα k fHk ⟩ 
          α k  ≡⟨ onlyFirstHitToNoEarlierHit l fHl k k<l ⟩ 
          false ∎ 
  
  extract : ∃ℕ1 α → Σℕ1 α
  extract = (λ ((n , p)) → n , onlyFirstHitToα n p) ∘ 
            splitSupportΣℕ1 ∘ 
            PT.map αToOnlyFirstHit where
    open ℕ∞SequenceProperties onlyFirstHit atMostOneHitInOnlyFirstHit 

splitSupportΣℕ1 : (α : binarySequence) → SplitSupport (Σℕ1 α)
splitSupportΣℕ1 = AtMostOneHit.extract 

module Interleave (α β : binarySequence) where 
  fstOnEvens : (n : ℕ) → interleave α β (doubleℕ n) ≡ α n 
  fstOnEvens n = 
    interleave α β (doubleℕ n) ≡⟨⟩ 
    ⊎.rec α β (Iso.inv ℕ⊎ℕ≅ℕ (doubleℕ n)) ≡⟨ cong (⊎.rec α β) (Iso.ret ℕ⊎ℕ≅ℕ (inl n)) ⟩ 
    ⊎.rec α β (inl n) ≡⟨⟩ 
    α n ∎  
  sndOnOdds : (n : ℕ) → interleave α β (suc (doubleℕ n)) ≡ β n
  sndOnOdds n = cong (⊎.rec α β) (Iso.ret ℕ⊎ℕ≅ℕ (inr n)) 

