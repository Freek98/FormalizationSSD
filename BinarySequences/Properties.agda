module BinarySequences.Properties where 

open import BinarySequences.Definitions

open import Cubical.Data.Sigma
open import Cubical.Data.Bool renaming ( _≤_ to _≤B_ ; _≥_ to _≥B_ ; _≟_ to _=B_)
open import Cubical.Data.Nat

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
open import Cubical.Data.Nat.Order 
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

isPropHits1AtMostOnce : (α : binarySequence) → isProp (hits1AtMostOnce α)
isPropHits1AtMostOnce α = isPropΠ4 λ n m _ _ → isSetℕ n m 

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

-- let's see what exactly we want here, some refactoring must happen
-- 
-- firstHitAt is actually a binary sequence, one that is constructed from conjunction of the binary sequence witnessing that there have only been zeros before n and alpha itself. (the LLM formalization called this "noHitBefore" and "firstHitOnly"). I think it's better to define those sequences and derive the noHitBefore property on itself. 
-- 
module extractFirstHitInBinarySequence (α : binarySequence) where
  firstHitAt : (n : ℕ) → Type
  firstHitAt m = (α m ≡ true) × ((k : ℕ) → k < m → α k ≡ false)
    
  first-hit : Type
  first-hit = Σ[ m ∈ ℕ ] firstHitAt m

  firstSeenBefore : ℕ → Type
  firstSeenBefore n = (Σ[ m ∈ ℕ ] (m < n) × firstHitAt m)
  
  pred¬firstSeenBefore : (n : ℕ) → (¬ firstSeenBefore (suc n) ) → ¬ firstSeenBefore n
  pred¬firstSeenBefore n nothingBeforeSn (m , m<n , αm , notbeforem) = nothingBeforeSn (m , ≤-suc m<n , αm , notbeforem) 

  isPropFirstHitAt : (n : ℕ) → isProp (firstHitAt n)
  isPropFirstHitAt n (p , nF) (p' , nF') = Σ≡Prop 
    (λ αn → isPropΠ2 λ n _ → isSetBool (α n) false) 
    (isSetBool (α n) true p p') 

  isPropFirstHit : isProp first-hit
  isPropFirstHit (m , αm , mFirst) (n , αn , nFirst ) with (m ≟ n ) 
  ... | lt m<n = ex-falso (true≢false (sym αm ∙ nFirst m m<n))
  ... | eq m=n = Σ≡Prop (λ n → isPropFirstHitAt n) m=n
  ... | gt n<m = ex-falso (true≢false (sym αn ∙ mFirst n n<m )) 

  notSeenAtToNoHitBefore : (n : ℕ) → ¬ firstSeenBefore n → (k : ℕ) → k < n → α k ≡ false 
  notSeenAtToNoHitBefore zero _ _ k<0            = ex-falso $ ¬-<-zero k<0
  notSeenAtToNoHitBefore (suc n) noBefore k k<Sn = ¬true→false (α k) λ { αk → noBefore 
    (k , k<Sn , αk , λ { l l<k → notSeenAtToNoHitBefore n (pred¬firstSeenBefore n noBefore) l (<help l<k k<Sn) }) }  where
      <help : {m n k : ℕ} → (m < n) → n < suc k → m < k 
      <help {m} {n} {k} m<n n<Sk = pred-≤-pred (suc (suc m) ≤⟨ suc-≤-suc m<n ⟩ suc n ≤≡⟨ n<Sk ⟩ suc k ∎) 

  decidableFirst : (n : ℕ ) → Dec (firstSeenBefore n)
  decidableFirst zero    = no λ { ( _ , m<0 , _) → ¬-<-zero m<0 }
  decidableFirst (suc n) with (decidableFirst n)
  ... | yes (m , m<n , first) = yes (m , (m <⟨ m<n ⟩ n <≡⟨ 0 , refl ⟩ suc n ∎) , first)
  ... | no noEarlierFirst with (α n =B true) 
  ...     | yes αn = yes 
               (n , (0 , refl) , αn , notSeenAtToNoHitBefore n noEarlierFirst )
  ...     | no ¬αn = no caseSplit where
             caseSplit : firstSeenBefore (suc n)  → ⊥ 
             caseSplit (m , m<Sn , αm , x) with <-split m<Sn 
             ... | inl m<n = noEarlierFirst (m , m<n , αm , x)
             ... | inr m=n = ¬αn (cong α (sym m=n) ∙ αm)  

  findFirst : (n : ℕ) → α n ≡ true → firstSeenBefore (suc n)
  findFirst n αn with decidableFirst (suc n) 
  ... | yes p = p
  ... | no ¬p = ex-falso (¬p (n , (0 , refl) , αn , (notSeenAtToNoHitBefore n $ pred¬firstSeenBefore n ¬p)))
  
  extractFirst : ∃[ n ∈ ℕ ] α n ≡ true → first-hit
  extractFirst = PT.rec isPropFirstHit (uncurry goback) where
   
    spot : (n : ℕ) → firstSeenBefore n → first-hit
    spot n (m , _ , αm , mfirst) = m , αm , mfirst 

    goback : (n : ℕ) → α n ≡ true → first-hit
    goback n αn = spot (suc n) (findFirst n αn) 
  
  firstHit→Witness : first-hit → Σ[ n ∈ ℕ ] α n ≡ true
  firstHit→Witness (n , αn , _ ) = n , αn 

  extract : ∃[ n ∈ ℕ ] (α n ≡ true)  → Σ[ n ∈ ℕ ] (α n ≡ true) 
  extract = firstHit→Witness ∘ extractFirst

hasSplitSupportΣℕ1 : (α : binarySequence) → SplitSupport (Σℕ1 α)
hasSplitSupportΣℕ1 = extractFirstHitInBinarySequence.extract 
