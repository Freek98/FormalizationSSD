module BinarySequences where 

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Bool renaming ( _≤_ to _≤B_ ; _≥_ to _≥B_ ; _≟_ to _=B_)
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


open import BasicDefinitions 


or-≥-left : (a b : Bool) → (a or b) ≥B a
or-≥-left false false = tt
or-≥-left false true = tt
or-≥-left true _ = tt 

or-≥-right : (a b : Bool) → (a or b) ≥B b
or-≥-right false false = tt
or-≥-right false true = tt
or-≥-right true _ = tt 

or-true→⊎-default-right : (a b : Bool) → a or b ≡ true → (a ≡ true) ⊎ (b ≡ true)
or-true→⊎-default-right false false x = ex-falso (false≢true x)
or-true→⊎-default-right true  false _ = ⊎.inl refl
or-true→⊎-default-right false true  _ = ⊎.inr refl
or-true→⊎-default-right true  true  _ = ⊎.inr refl 

or-true→⊎-default-left : (a b : Bool) → a or b ≡ true → (a ≡ true) ⊎ (b ≡ true)
or-true→⊎-default-left false false x = ex-falso (false≢true x)
or-true→⊎-default-left true  false _ = ⊎.inl refl
or-true→⊎-default-left false true  _ = ⊎.inr refl
or-true→⊎-default-left true  true  _ = ⊎.inl refl 

and-true→× : (a b : Bool) → (a and b) ≡ true → (a ≡ true) × (b ≡ true) 
and-true→× false _    x = ex-falso (false≢true x)
and-true→× true false x = ex-falso (false≢true x)
and-true→× true true  x = refl , refl 

or-true→⊎ : (a b : Bool) → a or b ≡ true → (a ≡ true) ⊎ (b ≡ true)
or-true→⊎ = or-true→⊎-default-left

false-or-x-true→x-true : (a : Bool) → false or a ≡ true → a ≡ true
false-or-x-true→x-true false x = ex-falso (false≢true x)
false-or-x-true→x-true true _ = refl 

x-or-false-true→x-true : (a : Bool) → a or false ≡ true → a ≡ true
x-or-false-true→x-true false x = ex-falso (false≢true x)
x-or-false-true→x-true true _ = refl 

module MakeIncreasing where
  makeIncreasing : binarySequence → binarySequence
  makeIncreasing α zero = α 0
  makeIncreasing α (suc n) = α (suc n) or makeIncreasing α n 
  
  isIncreasingSeq : binarySequence → Type
  isIncreasingSeq α = (n : ℕ) → α (suc n) ≥B α n
  
  makeIncreasingIsIncreasing : (α : binarySequence) → isIncreasingSeq (makeIncreasing α)
  makeIncreasingIsIncreasing α n = or-≥-right (α (suc n)) (makeIncreasing α n) 

  hit→makeIncreasingHit : (α : binarySequence) → (n : ℕ) → α n ≡ true → makeIncreasing α n ≡ true
  hit→makeIncreasingHit α zero αn=1 = αn=1
  hit→makeIncreasingHit α (suc n) αn=1 = cong (λ b → b or makeIncreasing α n) αn=1 

  extractFromMakeIncreasing : (α : binarySequence) → (n : ℕ) → makeIncreasing α n ≡ true → Σ[ n ∈ ℕ ] α n ≡ true
  extractFromMakeIncreasing α zero αInc=1 = zero , αInc=1
  extractFromMakeIncreasing α (suc n) αInc=1 = case ((makeIncreasing α n) =B true) of λ 
   { (no ¬p) → suc n , x-or-false-true→x-true (α $ suc n) 
     ( α (suc n) or false 
         ≡⟨ cong (λ b → α (suc n) or b) (sym (¬true→false (makeIncreasing α n) ¬p)) ⟩ 
       α (suc n) or (makeIncreasing α n) 
         ≡⟨ αInc=1 ⟩ 
       true ∎ ) ;
     (yes p) → extractFromMakeIncreasing α n p }




module extractFirstHitInBinarySequence (α : binarySequence) where
  is-first-hit : (n : ℕ) → Type
  is-first-hit m = (α m ≡ true) × ((k : ℕ) → k < m → α k ≡ false)
    
  first-hit : Type
  first-hit = Σ[ m ∈ ℕ ] is-first-hit m

  firstSeenBefore : ℕ → Type
  firstSeenBefore n = (Σ[ m ∈ ℕ ] (m < n) × is-first-hit m)
  
  pred¬firstSeenBefore : (n : ℕ) → (¬ firstSeenBefore (suc n) ) → ¬ firstSeenBefore n
  pred¬firstSeenBefore n nothingBeforeSn (m , m<n , αm , notbeforem) = nothingBeforeSn (m , ≤-suc m<n , αm , notbeforem) 

  propHelp : (n : ℕ) → isProp (is-first-hit n)
  propHelp n (p , nF) (p' , nF') = Σ≡Prop 
    (λ αn → isPropΠ2 λ n _ → isSetBool (α n) false) 
    (isSetBool (α n) true p p') 

  firstProp : isProp first-hit
  firstProp (m , αm , mFirst) (n , αn , nFirst ) with (m ≟ n ) 
  ... | lt m<n = ex-falso (true≢false (sym αm ∙ nFirst m m<n))
  ... | eq m=n = Σ≡Prop (λ n → propHelp n) m=n
  ... | gt n<m = ex-falso (true≢false (sym αn ∙ mFirst n n<m )) 

  need : (n : ℕ) → ¬ firstSeenBefore n → (k : ℕ) → k < n → α k ≡ false 
  need zero _ _ k<0            = ex-falso $ ¬-<-zero k<0
  need (suc n) noBefore k k<Sn = ¬true→false (α k) λ { αk → noBefore 
    (k , k<Sn , αk , λ { l l<k → need n (pred¬firstSeenBefore n noBefore) l (<help l<k k<Sn) }) }  where
      <help : {m n k : ℕ} → (m < n) → n < suc k → m < k 
      <help {m} {n} {k} m<n n<Sk = pred-≤-pred (suc (suc m) ≤⟨ suc-≤-suc m<n ⟩ suc n ≤≡⟨ n<Sk ⟩ suc k ∎) 

  decidableFirst : (n : ℕ ) → Dec (firstSeenBefore n)
  decidableFirst zero    = no λ { ( _ , m<0 , _) → ¬-<-zero m<0 }
  decidableFirst (suc n) with (decidableFirst n)
  ... | yes (m , m<n , first) = yes (m , (m <⟨ m<n ⟩ n <≡⟨ 0 , refl ⟩ suc n ∎) , first)
  ... | no noEarlierFirst with (α n =B true) 
  ...     | yes αn = yes 
               (n , (0 , refl) , αn , need n noEarlierFirst )
  ...     | no ¬αn = no caseSplit where
             caseSplit : firstSeenBefore (suc n)  → ⊥ 
             caseSplit (m , m<Sn , αm , x) with <-split m<Sn 
             ... | inl m<n = noEarlierFirst (m , m<n , αm , x)
             ... | inr m=n = ¬αn (cong α (sym m=n) ∙ αm)  

  FindFirst : (n : ℕ) → α n ≡ true → firstSeenBefore (suc n)
  FindFirst n αn with decidableFirst (suc n) 
  ... | yes p = p
  ... | no ¬p = ex-falso (¬p (n , (0 , refl) , αn , (need n $ pred¬firstSeenBefore n ¬p)))
  
  extractFirst : ∃[ n ∈ ℕ ] α n ≡ true → first-hit
  extractFirst = PT.rec firstProp (uncurry goback) where
   
    spot : (n : ℕ) → firstSeenBefore n → first-hit
    spot n (m , _ , αm , mfirst) = m , αm , mfirst 

    goback : (n : ℕ) → α n ≡ true → first-hit
    goback n αn = spot (suc n) (FindFirst n αn) 
  
  first→Hit : first-hit → Σ[ n ∈ ℕ ] α n ≡ true
  first→Hit (n , αn , _ ) = n , αn 

  extract : ∃[ n ∈ ℕ ] (α n ≡ true)  → Σ[ n ∈ ℕ ] (α n ≡ true) 
  extract = first→Hit ∘ extractFirst
