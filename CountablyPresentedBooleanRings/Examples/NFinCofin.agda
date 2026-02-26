{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.Examples.NFinCofin where
open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.Examples.Bool
open import Cubical.Foundations.Equiv
open import Cubical.Data.Fin
open import Cubical.Foundations.Isomorphism
open import BooleanRing.BooleanRingMaps
open import BooleanRing.SubBooleanRing
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat hiding (_·_ ; _+_)
open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing.Base

open import Cubical.Data.Sum
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.QuotientConclusions
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import BasicDefinitions
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕ_)
open import Cubical.Algebra.CommRing.Instances.Unit
open import QuickFixes

--this approach suggested after conversation with AI
isFinite : binarySequence → Type
isFinite α = Σ[ n ∈ ℕ ] (∀ (m : ℕ) → m > n → α m ≡ false)

isCofinite : binarySequence → Type 
isCofinite α = Σ[ n ∈ ℕ ](∀ (m : ℕ) → m > n → α m ≡ true)
-- I will just replace this with isFinite (¬ α)

isFiniteProp : binarySequence → Type
isFiniteProp α = ( ∀ (n : ℕ) → α n ≡ false) ⊎ (Σ[ n ∈ ℕ ] (α n ≡ true) × 
                                              (∀ (m : ℕ) → m > n → α m ≡ false))

isPropisFiniteProp : (α : binarySequence) → isProp (isFiniteProp α)
isPropisFiniteProp α (inl α=0) (inl α=0') = cong inl (funExt λ n → isSetBool _ _ _ _)
isPropisFiniteProp α (inl α=0) (inr (n , αn=1 , _)) = ex-falso (true≢false (sym αn=1 ∙ α=0 n))
isPropisFiniteProp α (inr (n , αn=1 , _)) (inl α=0) = ex-falso (true≢false (sym αn=1 ∙ α=0 n))
isPropisFiniteProp α (inr (n , αn=1 , α>n=0)) (inr (m , αm=1 , α>m=0)) = cong inr $
  case_of_ {B = λ _ → (n , αn=1 , α>n=0) ≡ (m , αm=1 , α>m=0)} (n =ℕ m) 
  λ { (lt n<m) → ex-falso (false≢true (sym (α>n=0 m n<m) ∙ αm=1))
    ; (eq n=m) → Σ≡Prop (λ _ → isProp× (isSetBool _ _) (isPropΠ2 λ _ _ → isSetBool _ _)) n=m
    ; (gt m<n) → ex-falso (false≢true (sym (α>m=0 n m<n) ∙ αn=1)) } 

BooleanStructureOnBinarySequences : BooleanRingStr binarySequence
BooleanStructureOnBinarySequences = pointWiseStructure ℕ (λ _ → Bool) (λ _ → snd BoolBR)

open BooleanRingStr ⦃...⦄
instance
 _ = BooleanStructureOnBinarySequences 
 _ = BoolBR

open BooleanAlgebraStr (binarySequence , BooleanStructureOnBinarySequences)

isCofiniteProp : binarySequence → Type 
isCofiniteProp α = isFiniteProp (¬ α)

isFiniteOrCofinite : (α : binarySequence) → Type
isFiniteOrCofinite α = isFinite α ⊎ isCofinite α

FinCofinℕ : Type
FinCofinℕ = Σ[ α ∈ binarySequence ] ∥ isFiniteOrCofinite α ∥₁ 

open SubBoolRing


complementFiniteIsCofinite : (α : binarySequence) → isFinite α → 
                             isCofinite (¬ α)
complementFiniteIsCofinite α (n , α>n=0) = n , λ m m>n → cong not (α>n=0 m m>n) 

complementCofiniteIsFinite : (α : binarySequence) → isCofinite α → 
                             isFinite (¬ α)
complementCofiniteIsFinite α (n , α>n=1) = n , λ m m>n → cong not (α>n=1 m m>n) 

open <-Reasoning

--unionFiniteFinite : (α β : binarySequence) → 
--  isFinite α → isFinite β → isFinite (α ∨ β)
--unionFiniteFinite α β (n , α>n=0) (m , β>m=0) = max m n , λ r r>mn → 
--  (α ∨ β) r 
--    ≡⟨⟩ 
--  BooleanAlgebraStr._∨_ BoolBR (α r) (β r)
--    ≡⟨ cong₂ (BooleanAlgebraStr._∨_ BoolBR) 
--      (α>n=0 r $ n ≤<⟨ right-≤-max {m = m}⟩ max m n <≡⟨ r>mn ⟩ r ∎)
--      (β>m=0 r $ m ≤<⟨ left-≤-max         ⟩ max m n <≡⟨ r>mn ⟩ r ∎) 
--     ⟩ 
--  BooleanAlgebraStr._∨_ BoolBR false false
--    ≡⟨⟩ 
--  false ∎ 
--  I think it's sufficient to use deMorgan and negations to show the other combinations match up if you realize that intersection with Finite is Finite. If I've proven that, I'll delete this. 

intersectionWithFiniteIsFinite : (α β : binarySequence) → 
  isFinite α → isFinite (α ∧ β)
intersectionWithFiniteIsFinite α β (n , α>n=0) = n , λ r r>mn → 
  (α ∧ β) r 
    ≡⟨⟩ 
  BooleanAlgebraStr._∧_ BoolBR (α r) (β r)
    ≡⟨ cong (λ a' → BooleanAlgebraStr._∧_ BoolBR a' (β r)) 
      (α>n=0 r r>mn)
     ⟩ 
  BooleanAlgebraStr._∧_ BoolBR false (β r)
    ≡⟨⟩ 
  false ∎ 

UnionCofiniteIsCofinite : (α β : binarySequence) → 
  isCofinite α → isCofinite (α ∨ β)
UnionCofiniteIsCofinite α β αCofin = subst isCofinite 
  (¬ (¬ α ∧ ¬ β) 
    ≡⟨ DeMorgan¬∧ {x = ¬ α} {y = ¬ β} ⟩ 
  ¬ ¬ α ∨ ¬ ¬ β 
    ≡⟨ cong₂ _∨_ (¬Invol {x = α}) ¬Invol ⟩ 
  α ∨ β ∎)
  (complementFiniteIsCofinite (¬ α ∧ ¬ β) 
  (intersectionWithFiniteIsFinite (¬ α) (¬ β) (complementCofiniteIsFinite α αCofin))) 

-- I feel there should be some generalization to subalgebras here. 
-- Suppose I have some algebraic structure, say rings, I can show in general that if R is a ring, and P : ⟨ R ⟩ → hProp -- Note you didn't do hProp :(, but you can truncate I guess. 
--  then Σ[ r ∈ R ] P r is also a ring, with the inherited ring structure. 
--  Then you can do the same for commRings, BooleanRings and all the structures you need for that. Let's ask that to some AI program, feel it should be a good short task. 

{-
It might be nice to have the following definition work at some point
data FinCofinℕ : Type where
  Finite   : (α : binarySequence) → isFinite α   → FinCofinℕ
  Cofinite : (α : binarySequence) → isCofinite α → FinCofinℕ
-}
--FinCofinℕsubBR : IsSubBooleanRing 
--  (binarySequence , BooleanStructureOnBinarySequences) 
--  (∥_∥₁ ∘ isFiniteOrCofinite) 
--  λ _ → squash₁ 
--FinCofinℕsubBR .IsSubBooleanRing.0-closed = {! !}
--FinCofinℕsubBR .IsSubBooleanRing.1-closed = {! !}
--FinCofinℕsubBR .IsSubBooleanRing.+-closed = {! !}
--FinCofinℕsubBR .IsSubBooleanRing.·-closed = {! !}
--FinCofinℕsubBR .IsSubBooleanRing.neg-closed = {! !} 


