{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.Examples.NFinCofin where
open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.Examples.Bool
open import BooleanRing.AlgebraicFacts
open import Cubical.Foundations.Equiv
open import Cubical.Tactics.NatSolver
open import BooleanRing.BooleanRingMaps
open import BooleanRing.SubBooleanRing
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_) 
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
open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.Data.Bool renaming ( _≟_ to _=B_)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕ_)
open import Cubical.Algebra.CommRing.Instances.Unit
open import QuickFixes

booleanStructureOnBinarySequences : BooleanRingStr binarySequence
booleanStructureOnBinarySequences = pointWiseStructure ℕ (λ _ → Bool) (λ _ → snd BoolBR)

ℙℕ : BooleanRing ℓ-zero
ℙℕ = binarySequence , booleanStructureOnBinarySequences

open BooleanAlgebraStr ℙℕ

--skipSteps : ℕ → binarySequence → binarySequence
--skipSteps zero α = α ∘ suc
--skipSteps (suc n) α = skipSteps n α ∘ suc
--
--skipStepsByAdd : (n : ℕ) → (α : binarySequence) → skipSteps n α ≡ α ∘ (_+ℕ_ (suc n))
--skipStepsByAdd zero α = refl
--skipStepsByAdd (suc n) α = 
--  skipSteps n α ∘ suc ≡⟨ cong (λ β → β ∘ suc ) $ skipStepsByAdd n α ⟩
--  α ∘ (λ k → suc n +ℕ k) ∘ suc ≡⟨ cong (λ p → α ∘ p) (funExt λ k → solveℕ!) ⟩ 
--  α ∘ (λ k → (suc (suc n)) +ℕ k) ∎  
--
--skipStepSize : (n : ℕ) → (α : binarySequence) → skipSteps n α zero ≡ α (suc n)
--skipStepSize n α = funExt⁻ (skipStepsByAdd n α) 0 ∙ cong α solveℕ!
--
--isConst0 : binarySequence → Type
--isConst0 α = ∀ (n : ℕ) → α n ≡ false 
--
--data isFinite (α : binarySequence) : Type where
--  constant0 : isConst0 α → isFinite α
--  isConstantAfter : (n : ℕ) → (α n ≡ true) → isConst0 (skipSteps n α) → isFinite α
--
--bounded→Finite : (α : binarySequence) → (n : ℕ) → isConst0 (skipSteps n α) → isFinite α
--bounded→Finite α zero α>n=0 = case_of_ {B = λ _ → isFinite α} (α 0 =B false) λ 
--  { (yes p) → constant0 λ { zero → p
--                          ; (suc m) → α>n=0 m }
--  ; (no ¬p) → isConstantAfter 0 (¬false→true (α 0) ¬p) α>n=0 } 
--bounded→Finite α (suc n) α>Sn=0 = case_of_ {B = λ _ → isFinite α} (α (suc n) =B false) λ 
--  { (yes p) → bounded→Finite α n λ { zero → skipStepSize n α ∙ p
--                                   ; (suc m) → α>Sn=0 m } 
--  ; (no ¬p) → isConstantAfter (suc n) (¬false→true (α (suc n)) ¬p) α>Sn=0 } 
--
--intersectWithFiniteIsFinite : (α β : binarySequence) → isFinite α → isFinite (α ∧ β) 
--intersectWithFiniteIsFinite α β (constant0 x) = constant0 λ n → cong (λ a → a and β n) (x n)
--intersectWithFiniteIsFinite α β (isConstantAfter n αn=1 α>n=0) = bounded→Finite (α ∧ β) n λ m → 
--  skipSteps n (α ∧ β) m 
--    ≡⟨ (funExt⁻ $ skipStepsByAdd n (α ∧ β)) m ⟩ 
--  α ((suc n) +ℕ m) and β ((suc n) +ℕ m) 
--    ≡⟨ cong (λ x → x and β ((suc n) +ℕ m) ) (sym $ (funExt⁻ $ skipStepsByAdd n α) m) ⟩ 
--  (skipSteps n α m) and β ((suc n) +ℕ m) 
--    ≡⟨ cong (λ x → x and β (suc n +ℕ m)) (α>n=0 m) ⟩ 
--  false and β ((suc n) +ℕ m) 
--    ≡⟨⟩ 
--  false ∎
--
--isPropisFinite : (α : binarySequence) → isProp (isFinite α)
--isPropisFinite α (constant0 x) (constant0 x₁) = cong constant0 $ funExt λ _ → isSetBool _ _ _ _
--isPropisFinite α (constant0 α=0) (isConstantAfter n αn=1 _) = 
--  ex-falso (false≢true (sym (α=0 n) ∙ αn=1))
--isPropisFinite α (isConstantAfter n αn=1 _) (constant0 α=0) =
--  ex-falso (false≢true (sym (α=0 n) ∙ αn=1))
--isPropisFinite α (isConstantAfter n αn=1 α>n=0) (isConstantAfter m αm=1 α>m=0) = 
--  case_of_ {B = λ _ → (isConstantAfter n αn=1 α>n=0) ≡ (isConstantAfter m αm=1 α>m=0)} (n =ℕ m) λ { (lt n<m) → ex-falso (true≢false (sym αm=1 ∙ {! α>n=0 !}))
--                                                                                                  ; (eq x) → {! !}
--                                                                                                  ; (gt x) → {! !} }
--
{-

{-
isPropisFinite : (α : binarySequence) → isProp (isFinite α)
isPropisFinite α (inr (n , αn=1 , α>n=0)) (inr (m , αm=1 , α>m=0)) = cong inr $
  case_of_ {B = λ _ → (n , αn=1 , α>n=0) ≡ (m , αm=1 , α>m=0)} (n =ℕ m) 
  λ { (lt n<m) → ex-falso (false≢true (sym (α>n=0 m n<m) ∙ αm=1))
    ; (eq n=m) → Σ≡Prop (λ _ → isProp× (isSetBool _ _) (isPropΠ2 λ _ _ → isSetBool _ _)) n=m
    ; (gt m<n) → ex-falso (false≢true (sym (α>m=0 n m<n) ∙ αn=1)) } 

isCofinite : binarySequence → Type 
isCofinite α = isFinite (¬ α)

¬FiniteAndCofinite : (α : binarySequence) → isFinite α → isCofinite α → ⊥ 
¬FiniteAndCofinite α (inl α=0) (inl ¬α=0) = true≢false $ 
  true    ≡⟨ cong not (sym $ α=0 0) ⟩ 
  (¬ α) 0 ≡⟨ ¬α=0 0 ⟩ 
  false   ∎
¬FiniteAndCofinite α (inl α=0) (inr (n , ¬αn=1 , ¬α>m=0 )) = true≢false $
  true    ≡⟨ sym $ cong not (α=0 (suc n)) ⟩ 
  (¬ α) (suc n) ≡⟨ ¬α>m=0 (suc n) <-suc ⟩ 
  false   ∎
¬FiniteAndCofinite α (inr (n , αn=1 , ¬α>m=0 )) (inl ¬α=0) = true≢false $
  true    ≡⟨ (sym $ cong not $ ¬α>m=0 (suc n) <-suc) ⟩ 
  (¬ α) (suc n) ≡⟨ ¬α=0 (suc n) ⟩ 
  false   ∎
¬FiniteAndCofinite α (inr (n , αn=1 , α>n=0) ) (inr (m , ¬αm=1 , ¬α>m=0)) = true≢false $ 
  true ≡⟨ sym $ cong not (α>n=0 ((max (suc m) (suc n))) right-≤-max) ⟩ 
  (¬ α $ (max (suc m) (suc n))) 
       ≡⟨ ¬α>m=0 (max (suc m) (suc n)) (left-≤-max {m = suc m}{ n = suc n}) ⟩
  false ∎  

¬FinIsCofin : (α : binarySequence) → isFinite α → isCofinite (¬ α)
¬FinIsCofin α = subst isFinite (sym $ funExt (notnot ∘ α)) 

¬CofinIsFin : (α : binarySequence) → isCofinite α → isFinite (¬ α)
¬CofinIsFin α c = c 

isFiniteOrCofinite : (α : binarySequence) → Type
isFiniteOrCofinite α = isFinite α ⊎ isCofinite α

isPropisFiniteOrCofinite : (α : binarySequence) → isProp (isFiniteOrCofinite α)
isPropisFiniteOrCofinite α (inl f) (inl f') = cong inl $ isPropisFinite α f f'
isPropisFiniteOrCofinite α (inl f) (inr c)  = ex-falso $ ¬FiniteAndCofinite α f c
isPropisFiniteOrCofinite α (inr c) (inl f)  = ex-falso $ ¬FiniteAndCofinite α f c
isPropisFiniteOrCofinite α (inr c) (inr c') = cong inr $ isPropisFinite (¬ α) c c' 

0Finite : isFinite (λ n → false)
0Finite = inl λ n → refl 

1Cofinite : isCofinite (λ n → true)
1Cofinite = 0Finite

intersectionWithFiniteIsFinite : (α : binarySequence) → isFinite α → (β : binarySequence) → isFinite (α ∧ β)
intersectionWithFiniteIsFinite = {! !} 

open SubBooleanAlgebra
ℕfinCofinSubBA : IsSubBooleanAlgebra (binarySequence , BooleanStructureOnBinarySequences) isFiniteOrCofinite isPropisFiniteOrCofinite 
ℕfinCofinSubBA .IsSubBooleanAlgebra.𝟘-cl = inl 0Finite
ℕfinCofinSubBA .IsSubBooleanAlgebra.𝟙-cl = inr 1Cofinite
ℕfinCofinSubBA .IsSubBooleanAlgebra.∧-cl = {! !}
ℕfinCofinSubBA .IsSubBooleanAlgebra.∨-cl = {! !}
ℕfinCofinSubBA .IsSubBooleanAlgebra.¬-cl = {! !} 

--ℕfinCofinAlgebra : BooleanRing ℓ-zero
--ℕfinCofinAlgebra = SubBoolAlgConstr.mkSubBooleanAlgebra (binarySequence , BooleanStructureOnBinarySequences) isFiniteOrCofinite isPropisFiniteOrCofinite (inl 0Finite) (inr 1Cofinite) {! !} {! !} {! !} 



--open <-Reasoning
--
----unionFiniteFinite : (α β : binarySequence) → 
----  isFinite α → isFinite β → isFinite (α ∨ β)
----unionFiniteFinite α β (n , α>n=0) (m , β>m=0) = max m n , λ r r>mn → 
----  (α ∨ β) r 
----    ≡⟨⟩ 
----  BooleanAlgebraStr._∨_ BoolBR (α r) (β r)
----    ≡⟨ cong₂ (BooleanAlgebraStr._∨_ BoolBR) 
----      (α>n=0 r $ n ≤<⟨ right-≤-max {m = m}⟩ max m n <≡⟨ r>mn ⟩ r ∎)
----      (β>m=0 r $ m ≤<⟨ left-≤-max         ⟩ max m n <≡⟨ r>mn ⟩ r ∎) 
----     ⟩ 
----  BooleanAlgebraStr._∨_ BoolBR false false
----    ≡⟨⟩ 
----  false ∎ 
----  I think it's sufficient to use deMorgan and negations to show the other combinations match up if you realize that intersection with Finite is Finite. If I've proven that, I'll delete this. 
--
--intersectionWithFiniteIsFinite : (α β : binarySequence) → 
--  isFinite α → isFinite (α ∧ β)
--intersectionWithFiniteIsFinite α β (n , α>n=0) = n , λ r r>mn → 
--  (α ∧ β) r 
--    ≡⟨⟩ 
--  BooleanAlgebraStr._∧_ BoolBR (α r) (β r)
--    ≡⟨ cong (λ a' → BooleanAlgebraStr._∧_ BoolBR a' (β r)) 
--      (α>n=0 r r>mn)
--     ⟩ 
--  BooleanAlgebraStr._∧_ BoolBR false (β r)
--    ≡⟨⟩ 
--  false ∎ 
--
--UnionCofiniteIsCofinite : (α β : binarySequence) → 
--  isCofinite α → isCofinite (α ∨ β)
--UnionCofiniteIsCofinite α β αCofin = subst isCofinite 
--  (¬ (¬ α ∧ ¬ β) 
--    ≡⟨ DeMorgan¬∧ {x = ¬ α} {y = ¬ β} ⟩ 
--  ¬ ¬ α ∨ ¬ ¬ β 
--    ≡⟨ cong₂ _∨_ (¬Invol {x = α}) ¬Invol ⟩ 
--  α ∨ β ∎)
--  (complementFiniteIsCofinite (¬ α ∧ ¬ β) 
--  (intersectionWithFiniteIsFinite (¬ α) (¬ β) (complementCofiniteIsFinite α αCofin))) 

-}
-}
