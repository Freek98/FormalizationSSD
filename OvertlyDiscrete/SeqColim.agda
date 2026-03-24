module OvertlyDiscrete.SeqColim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Nat.Order
import Cubical.Data.Nat.Order.Recursive as Rec
open Rec.Minimal
open import Cubical.Relation.Nullary
open import Cubical.Data.FinSet
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit 
open import Cubical.HITs.PropositionalTruncation as PT

data _≤E_ : (n m : ℕ) → Type where
  ≤E-refl : {n : ℕ} → n ≤E n
  ≤E-suc : {n m : ℕ} → n ≤E m → n ≤E suc m

suc-≤E-suc : {n m : ℕ} → n ≤E m → suc n ≤E suc m 
suc-≤E-suc ≤E-refl = ≤E-refl
suc-≤E-suc (≤E-suc c) = ≤E-suc (suc-≤E-suc c) 

≤E→≤ : {n m : ℕ} → n ≤E m → n ≤ m 
≤E→≤ ≤E-refl = ≤-refl
≤E→≤ (≤E-suc x) = ≤-suc (≤E→≤ x) 

≤→≤E : {n m : ℕ} → (n ≤ m) → n ≤E m 
≤→≤E {n} {m} (k , p) = helper n m k p where
  helper : (n m k : ℕ) → (p : k + n ≡ m) → n ≤E m
  helper n m zero p = subst (λ m' → n ≤E m') p ≤E-refl
  helper n zero (suc k) p = ex-falso (¬-<-zero (n , +-comm n (suc k) ∙ p))
  helper n (suc m) (suc k) p = ≤E-suc (helper n m k (cong predℕ p)) 

≤Induction' : (k : ℕ) → (P : (n : ℕ) → k ≤ n → Type) → P k ≤-refl → 
  ((l : ℕ) → (k≤l : k ≤ l) → P l k≤l) → (m : ℕ) → (k≤m : k ≤ m) → P m k≤m
≤Induction' k P Pk Psuc (suc m) k≤m = case ≤-split k≤m of λ 
  { (inl k<m) → {! !}
  ; (inr k=m) → {! !} } 
≤Induction' k P Pk Psuc zero k≤m = {! !}

≤Induction : (P : ℕ → Type) → (k : ℕ) → P k → ((l : ℕ) → P l → P (suc l)) → (m : ℕ) → k ≤ m → P m 
≤Induction P k Pk Psuc (suc m) k≤m = case (≤-split k≤m)  of λ 
  { (inl (n , n+sk=sm)) → Psuc m (≤Induction P k Pk Psuc m (n , {! n+sk=sm !}))
  ; (inr k=sucm) → subst P k=sucm Pk }
≤Induction P zero Pk Psuc zero k≤m = Pk
≤Induction P (suc k) Pk Psuc zero k≤m = ex-falso (¬-<-zero k≤m)

decΣProp : {A : Type} {B : A → Type} → isProp A → (( a : A) → isProp (B a)) → Dec A → ((a : A) → Dec (B a)) → Dec (Σ[ a ∈ A ] (B a))
decΣProp {A = A} {B = B} Aprop Bprop (yes a) Bdec with Bdec a 
... | yes b = yes (a , b)
... | no ¬p = no λ ((a' , b)) → ¬p (subst B (Aprop a' a) b) 
decΣProp Aprop Bprop (no ¬p) Bdec = no (¬p ∘ fst) 

--decΣProp2 : {A : Type} {B : A → Type} {C : (a : A) → B a → Type} → 

module SequentialColimitOfFiniteTypes 
  (X : ℕ → Type) (Xmap : {n : ℕ} → X n → X (suc n))
  (isFin : (n : ℕ) → isFinSet (X n)) where

  open Sequence 

  Xseq : Sequence _
  Xseq .Sequence.obj = X
  Xseq .Sequence.map = Xmap 

  iterMap : (n m : ℕ) → X n  → X (m + n) 
  iterMap n zero x = x
  iterMap n (suc m) x = Xmap (iterMap n m x) 

  ιnm : {n m : ℕ} → (n ≤ m) → X n → X m 
  ιnm {n} {m} (d , d+n=m) x = subst X d+n=m (iterMap n d x) 

  ιnm' : {n m : ℕ} → n ≤E m → X n → X m 
  ιnm' ≤E-refl x = x
  ιnm' (≤E-suc k) x = Xmap (ιnm' k x) 

  ιnmUseProp : {n m : ℕ} → {p q : n ≤ m} → (x : X n) → ιnm p x ≡ ιnm q x
  ιnmUseProp {n}{m}{p}{q} x i = subst X 
    (snd (isProp≤ {m = n} {n = m} p q i)) 
    (iterMap n (fst (isProp≤ p q i)) x) 

  iterMapComp : (n m k : ℕ) (x : X n)
    → PathP (λ i → X (+-assoc k m n i)) (iterMap (m + n) k (iterMap n m x)) (iterMap n (k + m) x)
  iterMapComp n m zero x = refl
  iterMapComp n m (suc k) x = congP (λ _ → Xmap) (iterMapComp n m k x)

  ιnmcomp : {n m k : ℕ} → (n≤m : n ≤ m) → (m≤k : m ≤ k) → (n≤k : n ≤ k) → (x : X n) →
    ιnm m≤k (ιnm n≤m x) ≡ ιnm n≤k x
  ιnmcomp {n} {m} {k} n≤m m≤k n≤k x =
    inductionLemma n (n≤m .fst) (m≤k .fst) x m (n≤m .snd) k (m≤k .snd) n≤k
    where
    inductionLemma : (n d e : ℕ) (x : X n)
      (m : ℕ) (p : d + n ≡ m)
      (k : ℕ) (q : e + m ≡ k)
      (n≤k : n ≤ k)
      → ιnm (e , q) (ιnm (d , p) x) ≡ ιnm n≤k x
    inductionLemma n d e x =
      J> J> λ n≤k →
      transportRefl _
      ∙ cong (iterMap (d + n) e) (transportRefl _)
      ∙ sym (fromPathP (symP (iterMapComp n d e x)))
      ∙ cong (λ le → ιnm le x) (isProp≤ _ _)

  ιnmPres : {n m k l : ℕ} (n≤k : n ≤ k) (m≤k : m ≤ k) (k≤l : k ≤ l) (n≤l : n ≤ l) (m≤l : m ≤ l) (x : X n) (y : X m) → ιnm n≤k x ≡ ιnm m≤k y → ιnm n≤l x ≡ ιnm m≤l y
  ιnmPres n≤k m≤k k≤l n≤l m≤l x y p = 
    ιnm n≤l x ≡⟨ sym $ ιnmcomp n≤k k≤l n≤l x ⟩ 
    ιnm k≤l (ιnm n≤k x) ≡⟨ cong (ιnm k≤l) p ⟩ 
    ιnm k≤l (ιnm m≤k y) ≡⟨ ιnmcomp m≤k k≤l m≤l y ⟩ 
    ιnm m≤l y ∎
  
--  ιnm'Incl : {n m : ℕ} → (n≤m : n ≤E m) → (x : X n) → 
--    incl {n = n} x ≡ incl {n = m} (ιnm' n≤m x)
--  ιnm'Incl ≤E-refl x = refl
--  ιnm'Incl {n = n} {m = (suc m)} (≤E-suc c) x = 
--    incl {n = n} x ≡⟨ push {n = n} x ⟩ 
--    incl {n = suc n} (Xmap {n = n} x) 
--      ≡⟨ ιnm'Incl {n = suc n} {m = suc m} (suc-≤E-suc {n = n} {m = m} c) (Xmap x) ⟩ 
--    incl (ιnm' (suc-≤E-suc c) (Xmap x)) 
--      ≡⟨ sym {! push   !} ⟩ 
--    incl {n = suc m} (ιnm' {n = n} (≤E-suc c) x)  ∎
--
  ιnmIncl : {n m : ℕ} → (n≤m : n ≤ m) → (x : X n) → incl {n = n} x ≡ incl {n = m} (ιnm n≤m x)
  ιnmIncl {n} {m} n≤m x = ≤Induction' n (λ k n≤k → incl {n = n} x ≡ incl {n = k} (ιnm n≤k x)) 
    {! refl !} {! !} {! !} {! !} -- ≤Induction {! !} {! !} {! !} {! !} {! !} {! !} 

  X∞ : Type 
  X∞ = SeqColim Xseq

  EqualAt : {n m : ℕ} → (x : X n) → (y : X m) → (k : ℕ) → Type
  EqualAt {n = n} {m = m} x y k = 
    Σ[ n≤k ∈ (n ≤ k)] Σ[ m≤k ∈ (m ≤ k)] ιnm n≤k x ≡ ιnm m≤k y 

  isPropEqualAt : {n m : ℕ} → {x : X n} → {y : X m} → (k : ℕ) → isProp (EqualAt x y k)
  isPropEqualAt k = isPropΣ isProp≤ λ _ → isPropΣ isProp≤ λ _ → isFinSet→isSet (isFin k) _ _ 

  isDecEqualAt : {n m : ℕ} → {x : X n} → {y : X m} → (k : ℕ) → Dec (EqualAt x y k)
  isDecEqualAt k = 
    decΣProp isProp≤ 
    (λ _ → isPropΣ isProp≤ λ _ → isFinSet→isSet (isFin k) _ _) (≤Dec _ _) λ _ → 
    decΣProp isProp≤ 
    (λ _ → isFinSet→isSet (isFin k) _ _) (≤Dec _ _) λ _ → isFinSet→Discrete (isFin k) _ _  

  

  EqWitness : {n m : ℕ} → (x : X n) → (y : X m) → Type
  EqWitness x y = Σ[ k ∈ ℕ ] EqualAt x y k

  EqWitnessSplitSupport : {n m : ℕ} → (x : X n) → (y : X m) →  SplitSupport $ EqWitness x y
  EqWitnessSplitSupport x y = Collapsible→SplitSupport $ Decidable→Collapsible 
    isPropEqualAt isDecEqualAt

  EqWitness-refl : {n : ℕ} (x : X n) → EqWitness x x
  EqWitness-refl {n} x = n , ≤-refl , ≤-refl , refl 

  EqWitness-sym : {n m : ℕ} (x : X n) (y : X m) → EqWitness x y → EqWitness y x
  EqWitness-sym x y (k , ≤1 , ≤2 , p) = k , ≤2 , ≤1 , sym p 

  EqWitness-suc : {n : ℕ} → (x : X n) → EqWitness x (Xmap x)
  EqWitness-suc {n = n} x = suc n , ≤-sucℕ , ≤-refl , refl 

  EqWitness-trans : {n m k : ℕ} → (x : X n) → (y : X m) → (z : X k) → 
    EqWitness x y → EqWitness y z → EqWitness x z 
  EqWitness-trans x y z (l , n≤l , m≤l , ιx=ιy) (r , m≤r , k≤r , ιy=ιz) = 
    max l r , ≤-trans n≤l left-≤-max , ≤-trans k≤r (right-≤-max {m = l}) , 
    (ιnm _ x  ≡⟨ ιnmPres _ _ left-≤-max _ (≤-trans m≤l (left-≤-max {m = l} {n = r}) ) x y ιx=ιy ⟩ 
    ιnm _ y ≡⟨ ιnmPres _ _ (right-≤-max {n = r} {m = l}) _ _ y z ιy=ιz ⟩ 
    ιnm _ z ∎ )

  EqWitness-trans-inc : {n m : ℕ} → (x : X n) → (y : X m) → EqWitness x y → EqWitness x (Xmap y)
  EqWitness-trans-inc x y Eqxy = EqWitness-trans x y (Xmap y) Eqxy (EqWitness-suc y)
  
  EqWitness-trans-inc-sym : {n m : ℕ} → (x : X n) → (y : X m) → EqWitness x (Xmap y) → EqWitness x y
  EqWitness-trans-inc-sym x y EqxMy = EqWitness-trans x (Xmap y) y EqxMy (EqWitness-sym y (Xmap y) (EqWitness-suc y))

  EqWitnessPushCase→ : {n m : ℕ} (x : X n) (y : X m) → ∥ EqWitness x y ∥₁ → ∥ EqWitness x  (Xmap y) ∥₁ 
  EqWitnessPushCase→ x y = PT.map (EqWitness-trans-inc x y) 

  EqWitnessPushCase← : {n m : ℕ} (x : X n) (y : X m) → ∥ EqWitness x (Xmap y) ∥₁ → ∥ EqWitness x y ∥₁ 
  EqWitnessPushCase← x y = PT.map (EqWitness-trans-inc-sym x y) 
  
  EqWitness→EqX∞ : {n m : ℕ} → (x : X n) → (y : X m) → EqWitness x y → 
    incl {n = n} x ≡ incl {n = m} y 
  EqWitness→EqX∞ x y (k , n≤k , m≤k , ιnmx=ιnmy ) = {!  ιnmPres !} 

  Code : (n : ℕ) → (x : X n) (y : X∞) → Type
  Code n x (incl y) = ∥ EqWitness x y ∥₁
  Code n x (push y i) = hPropExt squash₁ squash₁ (EqWitnessPushCase→ x y) (EqWitnessPushCase← x y) i 
  
  encode : (n : ℕ) (x : X n) (y : X∞) → incl x ≡ y → Code n x y 
  encode n x y p = J (λ y p → Code n x y) ∣ EqWitness-refl x ∣₁ p 

  decode : (n : ℕ) (x : X n) (y : X∞) → Code n x y → incl x ≡ y
  decode n x (incl x₁) c = {! !}
  decode n x (push x₁ i) c = {! !} 
