module OvertlyDiscrete.SeqColim where
-- originally human, then cleaned up and refactored with AI help. See 9cfdd16c9820ce97dbb46cb70846233738f5c184 for the version that was human
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence 
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit
open import Cubical.Relation.Nullary
open import Cubical.Data.FinSet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat.Order.Recursive using (Decidable→Collapsible)

-- ════════════════════════════════════════════════════════════════
-- § Inductive ≤ (≤E) — better for recursion/induction on proofs
-- ════════════════════════════════════════════════════════════════

data _≤E_ : ℕ → ℕ → Type where
  ≤E-refl : {n : ℕ} → n ≤E n
  ≤E-step : {n m : ℕ} → n ≤E m → n ≤E suc m

≤E-trans : {n m k : ℕ} → n ≤E m → m ≤E k → n ≤E k
≤E-trans p ≤E-refl = p
≤E-trans p (≤E-step q) = ≤E-step (≤E-trans p q)

≤E→≤ : {n m : ℕ} → n ≤E m → n ≤ m
≤E→≤ ≤E-refl = ≤-refl
≤E→≤ (≤E-step p) = ≤-suc (≤E→≤ p)

≤→≤E : {n m : ℕ} → n ≤ m → n ≤E m
≤→≤E {n} {m} (k , p) = go n m k p where
  go : (n m k : ℕ) → k + n ≡ m → n ≤E m
  go n m zero p = subst (n ≤E_) p ≤E-refl
  go n zero (suc k) p = ex-falso (¬-<-zero (n , +-comm n (suc k) ∙ p))
  go n (suc m) (suc k) p = ≤E-step (go n m k (cong predℕ p))

≤E-retract : {n m : ℕ} (p : n ≤E m) → ≤→≤E (≤E→≤ p) ≡ p
≤E-retract ≤E-refl = transportRefl ≤E-refl
≤E-retract (≤E-step q) = ≤→≤E-suc (≤E→≤ q) ∙ cong ≤E-step (≤E-retract q) where 
  ≤→≤E-suc : {n m : ℕ} (p : n ≤ m) → ≤→≤E (≤-suc p) ≡ ≤E-step (≤→≤E p)
  ≤→≤E-suc (k , e) = refl

isProp≤E : {n m : ℕ} → isProp (n ≤E m)
isProp≤E = isPropRetract ≤E→≤ ≤→≤E ≤E-retract isProp≤

-- ════════════════════════════════════════════════════════════════
-- § Sequential colimit: iterated maps and incl compatibility
-- ════════════════════════════════════════════════════════════════

module SeqColimMaps {ℓ : Level} (S : Sequence ℓ) where

  private
    X = Sequence.obj S
    f = Sequence.map S

  ι : {n m : ℕ} → n ≤E m → X n → X m
  ι ≤E-refl x = x
  ι (≤E-step p) x = f (ι p x)

  ι≤ : {n m : ℕ} → n ≤ m → X n → X m
  ι≤ p = ι (≤→≤E p)

  ι-propIrrel : {n m : ℕ} (p q : n ≤E m) (x : X n) → ι p x ≡ ι q x
  ι-propIrrel p q x = cong (λ r → ι r x) (isProp≤E p q)

  ι-comp : {n m k : ℕ} (p : n ≤E m) (q : m ≤E k) (x : X n)
    → ι q (ι p x) ≡ ι (≤E-trans p q) x
  ι-comp p ≤E-refl x = refl
  ι-comp p (≤E-step q) x = cong f (ι-comp p q x)

  ι-incl : {n m : ℕ} (p : n ≤E m) (x : X n)
    → incl {X = S} x ≡ incl (ι p x)
  ι-incl ≤E-refl x = refl
  ι-incl (≤E-step p) x =
    ι-incl p x ∙ push (ι p x)

  ι≤-incl : {n m : ℕ} (p : n ≤ m) (x : X n)
    → incl {X = S} x ≡ incl (ι≤ p x)
  ι≤-incl p = ι-incl (≤→≤E p)

  ι-pres : {n m k l : ℕ}
    (p : n ≤E k) (q : m ≤E k) (r : k ≤E l)
    (s : n ≤E l) (t : m ≤E l)
    (x : X n) (y : X m)
    → ι p x ≡ ι q y → ι s x ≡ ι t y
  ι-pres {n} {m} {k} {l} p q r s t x y e =
    ι s x                ≡⟨ ι-propIrrel s (≤E-trans p r) x ⟩
    ι (≤E-trans p r) x   ≡⟨ sym (ι-comp p r x) ⟩
    ι r (ι p x)          ≡⟨ cong (ι r) e ⟩
    ι r (ι q y)          ≡⟨ ι-comp q r y ⟩
    ι (≤E-trans q r) y   ≡⟨ ι-propIrrel (≤E-trans q r) t y ⟩
    ι t y               ∎

-- ═════════════════════════════════
-- § Finite-type sequential colimits 
-- ═════════════════════════════════

decΣProp : {A : Type} {B : A → Type}
  → isProp A → ((a : A) → isProp (B a))
  → Dec A → ((a : A) → Dec (B a)) → Dec (Σ A B)
decΣProp Ap Bp (yes a) Bd with Bd a
... | yes b = yes (a , b)
... | no ¬b = no λ (a' , b) → ¬b (subst _ (Ap a' a) b)
decΣProp Ap Bp (no ¬a) Bd = no (¬a ∘ fst)

≤E-Dec : (n m : ℕ) → Dec (n ≤E m)
≤E-Dec n m with ≤Dec n m
... | yes p = yes (≤→≤E p)
... | no ¬p = no (¬p ∘ ≤E→≤)

module FiniteSeqColim
  (X : ℕ → Type) (Xmap : {n : ℕ} → X n → X (suc n))
  (isFin : (n : ℕ) → isFinSet (X n)) where

  Xseq : Sequence _
  Xseq .Sequence.obj = X
  Xseq .Sequence.map = Xmap

  open SeqColimMaps Xseq 

  X∞ : Type
  X∞ = SeqColim Xseq

  EqualAt : {n m : ℕ} → X n → X m → ℕ → Type
  EqualAt {n} {m} x y k =
    Σ[ p ∈ n ≤E k ] Σ[ q ∈ m ≤E k ] ι p x ≡ ι q y

  isPropEqualAt : {n m : ℕ} {x : X n} {y : X m} (k : ℕ) → isProp (EqualAt x y k)
  isPropEqualAt k =
    isPropΣ isProp≤E λ _ →
    isPropΣ isProp≤E λ _ →
    isFinSet→isSet (isFin k) _ _

  isDecEqualAt : {n m : ℕ} {x : X n} {y : X m} (k : ℕ) → Dec (EqualAt x y k)
  isDecEqualAt {n} {m} k =
    decΣProp isProp≤E (λ _ → isPropΣ isProp≤E λ _ → isFinSet→isSet (isFin k) _ _)
      (≤E-Dec n k) λ _ →
    decΣProp isProp≤E (λ _ → isFinSet→isSet (isFin k) _ _)
      (≤E-Dec m k) λ _ →
    isFinSet→Discrete (isFin k) _ _

  EqWitness : {n m : ℕ} → X n → X m → Type
  EqWitness x y = Σ[ k ∈ ℕ ] EqualAt x y k

  EqWitness-splitSupport : {n m : ℕ} (x : X n) (y : X m) → SplitSupport (EqWitness x y)
  EqWitness-splitSupport x y =
    Collapsible→SplitSupport (Decidable→Collapsible isPropEqualAt isDecEqualAt)

  EqWitness-refl : {n : ℕ} (x : X n) → EqWitness x x
  EqWitness-refl x = _ , ≤E-refl , ≤E-refl , refl

  EqWitness-sym : {n m : ℕ} (x : X n) (y : X m) → EqWitness x y → EqWitness y x
  EqWitness-sym _ _ (k , p , q , e) = k , q , p , sym e

  EqWitness-suc : {n : ℕ} (x : X n) → EqWitness x (Xmap x)
  EqWitness-suc x = _ , ≤E-step ≤E-refl , ≤E-refl , refl

  EqWitness-trans : {n m l : ℕ} (x : X n) (y : X m) (z : X l)
    → EqWitness x y → EqWitness y z → EqWitness x z
  EqWitness-trans x y z (j , n≤j , m≤j , ιx≡ιy) (k , m≤k , l≤k , ιy≡ιz) =
    max j k ,
    n≤max ,
    l≤max ,
    ι-pres n≤j m≤j j≤max n≤max m≤max x y ιx≡ιy
    ∙ 
    ι-pres m≤k l≤k k≤max m≤max l≤max y z ιy≡ιz
    where
    j≤max = ≤→≤E (left-≤-max {m = j})
    k≤max = ≤→≤E (right-≤-max {m = j})
    n≤max = ≤E-trans n≤j j≤max
    m≤max = ≤E-trans m≤j j≤max
    l≤max = ≤E-trans l≤k k≤max

  EqWitness→Path : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x y → incl x ≡ incl y
  EqWitness→Path {n = n} {m} x y (k , n≤k , m≤k , p) =
    incl x ≡⟨ ι-incl n≤k x ⟩ 
    incl (ι n≤k x) ≡⟨ cong incl p ⟩
    incl (ι m≤k y) ≡⟨ sym (ι-incl m≤k y) ⟩ 
    incl y ∎

  Code : (n : ℕ) → X n → X∞ → Type
  Code n x (incl y) = ∥ EqWitness x y ∥₁
  Code n x (push y i) =
    hPropExt squash₁ squash₁
      (PT.map (EqWitness-push→ x y))
      (PT.map (EqWitness-push← x y)) i where

    EqWitness-push→ : {n m : ℕ} (x : X n) (y : X m)
      → EqWitness x y → EqWitness x (Xmap y)
    EqWitness-push→ x y w = 
      EqWitness-trans x y _ w (EqWitness-suc y)

    EqWitness-push← : {n m : ℕ} (x : X n) (y : X m)
      → EqWitness x (Xmap y) → EqWitness x y
    EqWitness-push← x y w = 
      EqWitness-trans x (Xmap y) y w 
      (EqWitness-sym y _ (EqWitness-suc y))


  encode : (n : ℕ) (x : X n) (y : X∞) → incl x ≡ y → Code n x y
  encode n x y p = J (λ y _ → Code n x y) ∣ EqWitness-refl x ∣₁ p

  y=pushyi : {n : ℕ} → (y : X n) → (i : I)  → PathP (λ j → X∞) (incl y) (push y i) 
  y=pushyi {n = n} y i j = push {n = n} y (i ∧ j) 
  my=pushyi : {n : ℕ} → (y : X n) → (i : I)  → PathP (λ j → X∞) (push y i) (incl (Xmap y))
  my=pushyi {n = n} y i j = push {n = n} y (i ∨ j) 
  pushyi=pushyj : {n : ℕ} → (y : X n) → (i j : I) → PathP (λ k → X∞) (push y i) (push y j)
  pushyi=pushyj y i j = (sym $ y=pushyi y i) ∙ y=pushyi y j 

  decode : (n : ℕ) (x : X n) (y : X∞) → Code n x y → incl x ≡ y
  decode n x (incl y) c = EqWitness→Path x y (EqWitness-splitSupport x y c)
  decode n x (push {n = m} y i) c = {! x=pushyi i1 !} where
    c' : Code n x (push y i)
    c' = c 
    cAt0' : Code n x (incl y) 
    cAt0' = {! !} 
    cAt0 : Code n x (incl y)
    cAt0 = subst (λ a → Code n x a) (sym (y=pushyi y i)) c 
--    cAt1 : Code n x (incl (Xmap y))
--    cAt1 = subst (λ a → Code n x a) (my=pushyi y i) c 
--    cPath : PathP (λ j → (Code n x (push y j))) cAt0 cAt1 
--    cPath j = subst (λ a → Code n x a) (pushyi=pushyj y i {! i !}) c 

    Eqxy : EqWitness x y 
    Eqxy = EqWitness-splitSupport x y cAt0 
    x=y : incl x ≡ incl y 
    x=y = EqWitness→Path x y Eqxy 
    x=pushyi : incl x ≡ push y i
    x=pushyi = x=y ∙ λ j → push y (i ∧ j) 
    
    x=my : incl x ≡ incl (Xmap y)
    x=my = {! !} 

    {-


    decodeAt0 : incl x ≡ incl y 
    decodeAt0 = decode n x (incl y) cAt0
    decodeAt1 : incl x ≡ incl (Xmap y)
    decodeAt1 = decode n x (incl (Xmap y)) cAt1
--    decodePath : PathP (λ j → incl x ≡ (push y j)) decodeAt0 {! !}
--    decodePath = {! !}
--
--    codingFam : PathP (λ j → Code n x (push y j)) cAt0 cAt1
--    codingFam = {! !} 
----    codingFam j = subst (λ a → Code n x a) (pushyi=pushyj y i j) c --subst (λ a → Code n x a) (pushyi=pushyj y i {! !}) c 
--    eqWitness : Σ[ k ∈ ℕ ] EqualAt x y k
--    eqWitness = EqWitness-splitSupport x y {! c !} 
--    
----    c-at : ∀ j → Code n x (push y j) 
----    c-at j = transp (λ k → Code n x (push y {! k ∧ i  !})) {! !} {! !} 
--    codePath : (p : EqWitness x y) → (q : EqWitness x (Xmap y)) → PathP (λ i → Code n x (push y i)) ∣ p ∣₁ ∣ q ∣₁ 
--    codePath p q = {! c !} 
--    codePath' : PathP (λ i → incl x ≡ incl (push y i)) (decode n x (incl y) {! codePath i0 !}) {!  !} 
--    codePath' = {! !} 
--    cstart : Code n x (incl y) 
--    cstart = {!  !} 
--    startpath : incl y ≡ incl (Xmap y) 
--    startpath = push y 
--    inclx=incly : incl x ≡ incl y 
--    inclx=incly = EqWitness→Path x y (EqWitness-splitSupport x y {!  c !}) 
-}
