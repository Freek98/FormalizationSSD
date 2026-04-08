{-# OPTIONS --lossy-unification #-}
module OvertlyDiscrete.SeqColim where
-- at some points cleaned up with AI help. See 9cfdd16c9820ce97dbb46cb70846233738f5c184 for the version that was human
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence 
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
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

  ι-propIrrel : {n m : ℕ} (n≤m n≤m' : n ≤E m) (x : X n) → ι n≤m x ≡ ι n≤m' x
  ι-propIrrel n≤m n≤m' x = cong (λ r → ι r x) (isProp≤E n≤m n≤m')

  ι-comp : {n m k : ℕ} (p : n ≤E m) (q : m ≤E k) (x : X n)
    → ι q (ι p x) ≡ ι (≤E-trans p q) x
  ι-comp p ≤E-refl x = refl
  ι-comp p (≤E-step q) x = cong f (ι-comp p q x)

  ι-incl : {n m : ℕ} (p : n ≤E m) (x : X n)
    → incl {X = S} x ≡ incl (ι p x)
  ι-incl ≤E-refl x = refl
  ι-incl (≤E-step p) x =
    ι-incl p x ∙ push (ι p x)
  -- so as a matter of fact, ι-incl is a lot of compositions with push. 
  -- And actually, it's the only equality in X∞ we actually use. 
  -- Shouldn't this be sufficient somehow to prove that in the end, we only pick out one equality, namely one that comes from composing many pushes? 

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
  EqWitness-suc {n = n} x = suc n , ≤E-step ≤E-refl , ≤E-refl , refl

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
  -- We thus have a composition of ι-incl, then conging with equality, and then a flipped around ι-incl. Thus we have many pushes, then cong incl p, then some push backs. 
  -- But if p = refl, then we have only a composition of ι-incl. 
  -- Even better, p is equal to refl, as it's an equality in a set. 
  -- So we should be able to prove by induction that if y = Xmap y, the difference is composing with push. 
  --

  module helpWithPaths where
    repPush : {n : ℕ} (x : X n) (y : X n) (k : ℕ) (n≤k : n ≤E k) → 
      (p : x ≡ y) → (q : ι n≤k x ≡ ι n≤k y) → 
      (cong incl p) ∙ (ι-incl n≤k y) ≡ (ι-incl n≤k x) ∙ cong incl q
    repPush x y k n≤k p q = naturality ∙ cong (λ h → ι-incl n≤k x ∙ cong incl h) qirrel where
      naturality : (cong incl p) ∙ (ι-incl n≤k y) ≡ (ι-incl n≤k x) ∙ cong incl (cong (ι n≤k) p)
      naturality = sym $ homotopyNatural (ι-incl n≤k) p
      qirrel : cong (ι n≤k) p ≡ q
      qirrel = isFinSet→isSet (isFin k) _ _ (cong (ι n≤k) p) q 
  
  EqWitnessDon'tCareHelper : {n m : ℕ} (x : X n) (y : X m)
    (k  : ℕ) → (n≤k  : n ≤E k ) → (m≤k  : m ≤E k ) → (p : ι n≤k  x ≡ ι m≤k  y) → 
    (k' : ℕ) → (n≤k' : n ≤E k') → (m≤k' : m ≤E k') → (q : ι n≤k' x ≡ ι m≤k' y) → 
    EqWitness→Path x y (k  , n≤k  , m≤k  , p) ≡ 
    EqWitness→Path x y (k' , n≤k' , m≤k' , q)
  EqWitnessDon'tCareHelper x y k n≤k m≤k p k' n≤k' m≤k' q = {! !}

  EqWitnessDon'tCare : {n m : ℕ} (x : X n) (y : X m) → 
    (a b : EqWitness x y) → EqWitness→Path x y a ≡ EqWitness→Path x y b
  EqWitnessDon'tCare  x y (k , n≤k , m≤k , p) (k' , n≤k' , m≤k' , q) = 
    EqWitnessDon'tCareHelper x y k n≤k m≤k p k' n≤k' m≤k' q 



    


        


  EqWitnessPathIsPushComposition : {n m : ℕ} (x : X n) (y : X m)
    (k  : ℕ) → (n≤k  : n ≤E k ) → (m≤k  : m ≤E k ) → (p : ι n≤k  x ≡ ι m≤k  y) → 
    (k' : ℕ) → (n≤k' : n ≤E k') → (m≤k' : suc m ≤E k') → (q : ι n≤k' x ≡ ι m≤k' (Xmap y)) → 
    EqWitness→Path x y (k , n≤k , m≤k , p) ∙ push y ≡ 
    EqWitness→Path x (Xmap y) (k' , n≤k' , m≤k' , q)
  EqWitnessPathIsPushComposition x y k n≤k m≤k p k' n≤k' m≤k' q = {! !}

  EqWitnessPathComp : {n m : ℕ} (x : X n) (y : X m) → 
   (a : EqWitness x y) → (b : EqWitness x (Xmap y)) → 
   EqWitness→Path x y a ∙ push y ≡ EqWitness→Path x (Xmap y) b 

  EqWitnessPathComp x y (k , n≤k , m≤k , p) (k' , n≤k' , m≤k' , q) = 
    EqWitnessPathIsPushComposition x y k n≤k m≤k p k' n≤k' m≤k' q 

  EqWitness-push→ : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x y → EqWitness x (Xmap y)
  EqWitness-push→ x y w = 
    EqWitness-trans x y _ w (EqWitness-suc y)

  EqWitness-push← : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x (Xmap y) → EqWitness x y
  EqWitness-push← x y w = 
    EqWitness-trans x (Xmap y) y w 
    (EqWitness-sym y _ (EqWitness-suc y))

  Code : (n : ℕ) → X n → X∞ → Type
  Code n x (incl y) = ∥ EqWitness x y ∥₁
  Code n x (push y i) =
    hPropExt squash₁ squash₁
      (PT.map (EqWitness-push→ x y))
      (PT.map (EqWitness-push← x y)) i 

  encode : (n : ℕ) (x : X n) (y : X∞) → incl x ≡ y → Code n x y
  encode n x y p = J (λ y _ → Code n x y) ∣ EqWitness-refl x ∣₁ p
  -- inzicht: gebruik splitsupport om dingen gelijk te krijgen in EqWitness x y en EqWitness x (Xmap y)
  -- Kan je niet ervoor zorgen dat EqWitness altijd k gebruikt zodat die ook werkt voor Xmap y. 
  -- Of makkelijker geval, wat als je alleen bewijst dat 
  -- EqWitness x x en EqWitness x (Xmap x) behandelt?
  -- 

--  y=pushyi : {n : ℕ} → (y : X n) → (i : I)  → PathP (λ j → X∞) (incl y) (push y i) 
--  y=pushyi {n = n} y i j = push {n = n} y (i ∧ j) 
--  my=pushyi : {n : ℕ} → (y : X n) → (i : I)  → PathP (λ j → X∞) (push y i) (incl (Xmap y))
--  my=pushyi {n = n} y i j = push {n = n} y (i ∨ j) 
--  pushyi=pushyj : {n : ℕ} → (y : X n) → (i j : I) → PathP (λ k → X∞) (push y i) (push y j)
--  pushyi=pushyj y i j = (sym $ y=pushyi y i) ∙ y=pushyi y j 

  decode : (n : ℕ) (x : X n) (y : X∞) → Code n x y → incl x ≡ y
  decode n x (incl y) c = EqWitness→Path x y (EqWitness-splitSupport x y c)
  decode n x (push {n = m} y i) c = 
    ua→ {A₀ = ∥ EqWitness x y ∥₁ } {A₁ = ∥ EqWitness x (Xmap y) ∥₁ } 
        {e = propBiimpl→Equiv squash₁ squash₁ 
          (PT.map $ EqWitness-push→ x y) (PT.map $ EqWitness-push← x y  )  } 
        {B = λ j → incl x ≡ (push y j) } 
        {f₀ = λ c → EqWitness→Path x y (EqWitness-splitSupport x y c)} 
        {f₁  = λ c → EqWitness→Path x (Xmap y) (EqWitness-splitSupport x (Xmap y) c )} 
        f i c where 
--    f' : (a : ∥ EqWitness x y ∥₁) → PathP (λ j → incl x ≡ push y j) 
--         (EqWitness→Path x y (EqWitness-splitSupport x y a)) 
--         (EqWitness→Path x (Xmap y) (EqWitness-push→ x y (EqWitness-splitSupport x y a))) 
--    f' a = {!   !} 

    f : (a : ∥ EqWitness x y ∥₁) → PathP (λ j → incl x ≡ push y j) 
        (EqWitness→Path x y (EqWitness-splitSupport x y a)) 
        (EqWitness→Path x (Xmap y) (EqWitness-splitSupport x (Xmap y) 
        (PT.map (EqWitness-push→ x y) a))) 
    f a = {! EqWitnessPathComp !} where -- J {! !} {! !} (snd $ snd $ snd sup)  where
      sup = EqWitness-splitSupport x y a
      
    {- 
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

    EqxMy : EqWitness x (Xmap y)
    EqxMy = EqWitness-push→ x y Eqxy 

    x=y : incl x ≡ incl y 
    x=y = EqWitness→Path x y Eqxy 
    
    x=my : incl x ≡ incl (Xmap y)
    x=my = EqWitness→Path x (Xmap y) EqxMy 


    {-        x=y
    --     ιx---ιy
    --     |    |
    -- refl|    | ??? 
    --     |    |
    --     ιx---ι(m y)     
    --        x=my
    --
    --  goal : x = push y i with these end points. 
    -}
    x=pushyi : incl x ≡ push y i
    x=pushyi = x=y ∙ λ j → push y (i ∧ j) 
    
    pushyi=my : (push y i) ≡ incl (Xmap y)
    pushyi=my = λ j → push y (i ∨ j) 
-}
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
