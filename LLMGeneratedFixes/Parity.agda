module LLMGeneratedFixes.Parity where
-- AI generated, lightly skimmed. Needed things at the end.
-- ═══════════════════════════════════════════════════════════════
-- Even/Odd library for natural numbers
-- Multiple interfaces: Bool-valued, Type-valued, Σ-witness, data
-- ═══════════════════════════════════════════════════════════════

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool
  hiding (_≤_ ; _≥_)
open import Cubical.Data.Nat
  renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

-- ───────────────────────────────────────────────────────────────
-- Section 1: Core functions (doubleℕ, half)
-- ───────────────────────────────────────────────────────────────
half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

-- ───────────────────────────────────────────────────────────────
-- Section 2: doubleℕ n ≡ n +ℕ n
-- ───────────────────────────────────────────────────────────────

doubleℕ≡+self : (n : ℕ) → doubleℕ n ≡ n +ℕ n
doubleℕ≡+self zero = refl
doubleℕ≡+self (suc n) =
  cong suc (cong suc (doubleℕ≡+self n) ∙ sym (+-suc n n))

-- ───────────────────────────────────────────────────────────────
-- Section 3: Bool-valued parity identities
-- ───────────────────────────────────────────────────────────────

-- isEven, isOdd : ℕ → Bool  are from Cubical.Data.Nat

isEven-suc-suc : (n : ℕ) → isEven (suc (suc n)) ≡ isEven n
isEven-suc-suc n = refl

isOdd≡not-isEven : (n : ℕ) → isOdd n ≡ not (isEven n)
isOdd≡not-isEven zero = refl
isOdd≡not-isEven (suc zero) = refl
isOdd≡not-isEven (suc (suc n)) = isOdd≡not-isEven n

isEven≡not-isOdd : (n : ℕ) → isEven n ≡ not (isOdd n)
isEven≡not-isOdd zero = refl
isEven≡not-isOdd (suc zero) = refl
isEven≡not-isOdd (suc (suc n)) = isEven≡not-isOdd n

-- Complement lemmas
isEven-false→isOdd-true : {n : ℕ} → isEven n ≡ false → isOdd n ≡ true
isEven-false→isOdd-true {n} p = isOdd≡not-isEven n ∙ cong not p

isOdd-false→isEven-true : {n : ℕ} → isOdd n ≡ false → isEven n ≡ true
isOdd-false→isEven-true {n} p = isEven≡not-isOdd n ∙ cong not p

-- ───────────────────────────────────────────────────────────────
-- Section 4: isEven/isOdd of doubleℕ and suc∘doubleℕ
-- ───────────────────────────────────────────────────────────────

isEven-doubleℕ : (k : ℕ) → isEven (doubleℕ k) ≡ true
isEven-doubleℕ zero = refl
isEven-doubleℕ (suc k) = isEven-doubleℕ k

isEven-suc-doubleℕ : (k : ℕ) → isEven (suc (doubleℕ k)) ≡ false
isEven-suc-doubleℕ zero = refl
isEven-suc-doubleℕ (suc k) = isEven-suc-doubleℕ k

isOdd-doubleℕ : (k : ℕ) → isOdd (doubleℕ k) ≡ false
isOdd-doubleℕ zero = refl
isOdd-doubleℕ (suc k) = isOdd-doubleℕ k

isOdd-suc-doubleℕ : (k : ℕ) → isOdd (suc (doubleℕ k)) ≡ true
isOdd-suc-doubleℕ k = isEven-doubleℕ k

-- ───────────────────────────────────────────────────────────────
-- Section 5: half ∘ doubleℕ and doubleℕ ∘ half round-trips
-- ───────────────────────────────────────────────────────────────

half-doubleℕ : (k : ℕ) → half (doubleℕ k) ≡ k
half-doubleℕ zero = refl
half-doubleℕ (suc k) = cong suc (half-doubleℕ k)

half-suc-doubleℕ : (k : ℕ) → half (suc (doubleℕ k)) ≡ k
half-suc-doubleℕ zero = refl
half-suc-doubleℕ (suc k) = cong suc (half-suc-doubleℕ k)

doubleℕ-half-even : (n : ℕ) → isEven n ≡ true → doubleℕ (half n) ≡ n
doubleℕ-half-even zero _ = refl
doubleℕ-half-even (suc zero) p = ⊥.rec (false≢true p)
doubleℕ-half-even (suc (suc n)) p = cong (suc ∘ suc) (doubleℕ-half-even n p)

suc-doubleℕ-half-odd : (n : ℕ) → isEven n ≡ false → suc (doubleℕ (half n)) ≡ n
suc-doubleℕ-half-odd zero p = ⊥.rec (true≢false p)
suc-doubleℕ-half-odd (suc zero) _ = refl
suc-doubleℕ-half-odd (suc (suc n)) p = cong (suc ∘ suc) (suc-doubleℕ-half-odd n p)

-- ───────────────────────────────────────────────────────────────
-- Section 6: Inductive data type for parity
-- ───────────────────────────────────────────────────────────────

data Parity : ℕ → Type where
  even : (k : ℕ) → Parity (doubleℕ k)
  odd  : (k : ℕ) → Parity (suc (doubleℕ k))

parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
... | even k = odd k
... | odd k  = even (suc k)

-- ───────────────────────────────────────────────────────────────
-- Section 7: Σ-type witnesses
-- ───────────────────────────────────────────────────────────────

-- n is even ↔ ∃ k, n ≡ doubleℕ k
Even : ℕ → Type
Even n = Σ[ k ∈ ℕ ] n ≡ doubleℕ k

-- n is odd ↔ ∃ k, n ≡ suc (doubleℕ k)
Odd : ℕ → Type
Odd n = Σ[ k ∈ ℕ ] n ≡ suc (doubleℕ k)

-- n is even ↔ ∃ k, n ≡ k + k
Even+ : ℕ → Type
Even+ n = Σ[ k ∈ ℕ ] n ≡ k +ℕ k

-- n is odd ↔ ∃ k, n ≡ k + k + 1
Odd+ : ℕ → Type
Odd+ n = Σ[ k ∈ ℕ ] n ≡ k +ℕ k +ℕ 1

-- n is odd ↔ ∃ k, n ≡ 1 + (k + k)
Odd+' : ℕ → Type
Odd+' n = Σ[ k ∈ ℕ ] n ≡ 1 +ℕ (k +ℕ k)

-- ───────────────────────────────────────────────────────────────
-- Section 8: Conversions between Even/Odd interfaces
-- ───────────────────────────────────────────────────────────────

Even→Even+ : {n : ℕ} → Even n → Even+ n
Even→Even+ (k , p) = k , p ∙ doubleℕ≡+self k

Even+→Even : {n : ℕ} → Even+ n → Even n
Even+→Even (k , p) = k , p ∙ sym (doubleℕ≡+self k)

Odd→Odd+ : {n : ℕ} → Odd n → Odd+ n
Odd→Odd+ (k , p) = k , p ∙ cong suc (doubleℕ≡+self k) ∙ +-comm 1 (k +ℕ k)

Odd+→Odd : {n : ℕ} → Odd+ n → Odd n
Odd+→Odd (k , p) = k , p ∙ +-comm (k +ℕ k) 1 ∙ cong suc (sym (doubleℕ≡+self k))

Odd→Odd+' : {n : ℕ} → Odd n → Odd+' n
Odd→Odd+' (k , p) = k , p ∙ cong suc (doubleℕ≡+self k)

Odd+'→Odd : {n : ℕ} → Odd+' n → Odd n
Odd+'→Odd (k , p) = k , p ∙ cong suc (sym (doubleℕ≡+self k))

-- ───────────────────────────────────────────────────────────────
-- Section 9: Bool-valued ↔ Σ-witness conversions
-- ───────────────────────────────────────────────────────────────

-- isEven true → Even (using half)
isEven→Even : {n : ℕ} → isEven n ≡ true → Even n
isEven→Even {n} p = half n , sym (doubleℕ-half-even n p)

-- Even → isEven true
Even→isEven : {n : ℕ} → Even n → isEven n ≡ true
Even→isEven (k , p) = subst (λ m → isEven m ≡ true) (sym p) (isEven-doubleℕ k)

-- isEven false → Odd (using half)
isEvenFalse→Odd : {n : ℕ} → isEven n ≡ false → Odd n
isEvenFalse→Odd {n} p = half n , sym (suc-doubleℕ-half-odd n p)

-- Odd → isEven false
Odd→isEvenFalse : {n : ℕ} → Odd n → isEven n ≡ false
Odd→isEvenFalse (k , p) = subst (λ m → isEven m ≡ false) (sym p) (isEven-suc-doubleℕ k)

-- isOdd true → Odd
isOdd→Odd : {n : ℕ} → isOdd n ≡ true → Odd n
isOdd→Odd {n} p = isEvenFalse→Odd (isEven≡not-isOdd n ∙ cong not p)

-- Odd → isOdd true
Odd→isOdd : {n : ℕ} → Odd n → isOdd n ≡ true
Odd→isOdd {n} o = isEven-false→isOdd-true {n} (Odd→isEvenFalse o)

-- isOdd false → Even
isOddFalse→Even : {n : ℕ} → isOdd n ≡ false → Even n
isOddFalse→Even {n} p = isEven→Even (isOdd-false→isEven-true {n} p)

-- Even → isOdd false
Even→isOdd : {n : ℕ} → Even n → isOdd n ≡ false
Even→isOdd {n} e = isOdd≡not-isEven n ∙ cong not (Even→isEven e)

-- ───────────────────────────────────────────────────────────────
-- Section 10: Parity data ↔ other interfaces
-- ───────────────────────────────────────────────────────────────

Parity→Even⊎Odd : {n : ℕ} → Parity n → Even n ⊎ Odd n
Parity→Even⊎Odd (even k) = inl (k , refl)
Parity→Even⊎Odd (odd k)  = inr (k , refl)

Even→Parity : {n : ℕ} → Even n → Parity n
Even→Parity (k , p) = subst Parity (sym p) (even k)

Odd→Parity : {n : ℕ} → Odd n → Parity n
Odd→Parity (k , p) = subst Parity (sym p) (odd k)

-- ───────────────────────────────────────────────────────────────
-- Section 11: Decidability and mutual exclusion
-- ───────────────────────────────────────────────────────────────

even-or-odd : (n : ℕ) → Even n ⊎ Odd n
even-or-odd n = Parity→Even⊎Odd (parity n)

¬Even∧Odd : {n : ℕ} → Even n → Odd n → ⊥
¬Even∧Odd e o = true≢false (sym (Even→isEven e) ∙ Odd→isEvenFalse o)

even-xor-odd : (n : ℕ) → (Even n × (Odd n → ⊥)) ⊎ (Odd n × (Even n → ⊥))
even-xor-odd n with even-or-odd n
... | inl e = inl (e , λ o → ¬Even∧Odd e o)
... | inr o = inr (o , λ e → ¬Even∧Odd e o)

-- ───────────────────────────────────────────────────────────────
-- Section 12: Even/Odd of zero, suc, doubleℕ
-- ───────────────────────────────────────────────────────────────

Even-zero : Even zero
Even-zero = 0 , refl

Odd-one : Odd 1
Odd-one = 0 , refl

Even-doubleℕ : (k : ℕ) → Even (doubleℕ k)
Even-doubleℕ k = k , refl

Odd-suc-doubleℕ : (k : ℕ) → Odd (suc (doubleℕ k))
Odd-suc-doubleℕ k = k , refl

-- suc swaps parity
Even-suc→Odd : {n : ℕ} → Even (suc n) → Odd n
Even-suc→Odd (zero , p) = ⊥.rec (snotz p)
Even-suc→Odd (suc k , p) = k , injSuc p

Odd-suc→Even : {n : ℕ} → Odd (suc n) → Even n
Odd-suc→Even (k , p) = k , injSuc p

Even→Odd-suc : {n : ℕ} → Even n → Odd (suc n)
Even→Odd-suc (k , p) = k , cong suc p

Odd→Even-suc : {n : ℕ} → Odd n → Even (suc n)
Odd→Even-suc (k , p) = suc k , cong suc p

-- ───────────────────────────────────────────────────────────────
-- Section 13: Injectivity of doubleℕ
-- ───────────────────────────────────────────────────────────────

doubleℕ-inj : (m n : ℕ) → doubleℕ m ≡ doubleℕ n → m ≡ n
doubleℕ-inj zero zero _ = refl
doubleℕ-inj zero (suc n) p = ⊥.rec (znots p)
doubleℕ-inj (suc m) zero p = ⊥.rec (snotz p)
doubleℕ-inj (suc m) (suc n) p = cong suc (doubleℕ-inj m n (injSuc (injSuc p)))

suc-doubleℕ-inj : (m n : ℕ) → suc (doubleℕ m) ≡ suc (doubleℕ n) → m ≡ n
suc-doubleℕ-inj m n p = doubleℕ-inj m n (injSuc p)

-- doubleℕ k ≠ suc (doubleℕ j) : even ≠ odd
doubleℕ≢suc-doubleℕ : (j k : ℕ) → doubleℕ k ≡ suc (doubleℕ j) → ⊥
doubleℕ≢suc-doubleℕ j k p = true≢false (sym (isEven-doubleℕ k) ∙ subst (λ m → isEven m ≡ false) (sym p) (isEven-suc-doubleℕ j))

-- Even and Odd witnesses are unique
Even-unique : {n : ℕ} → (e₁ e₂ : Even n) → fst e₁ ≡ fst e₂
Even-unique (j , p) (k , q) = doubleℕ-inj j k (sym p ∙ q)

Odd-unique : {n : ℕ} → (o₁ o₂ : Odd n) → fst o₁ ≡ fst o₂
Odd-unique (j , p) (k , q) = suc-doubleℕ-inj j k (sym p ∙ q)

-- ───────────────────────────────────────────────────────────────
-- Section 14: Reconstruction from parity and half
-- ───────────────────────────────────────────────────────────────

-- If two numbers have the same parity and same half, they are equal
even→eq : (n m : ℕ) → isEven n ≡ true → isEven m ≡ true → half n ≡ half m → n ≡ m
even→eq n m en em hq =
  sym (doubleℕ-half-even n en) ∙ cong doubleℕ hq ∙ doubleℕ-half-even m em

odd→eq : (n m : ℕ) → isEven n ≡ false → isEven m ≡ false → half n ≡ half m → n ≡ m
odd→eq n m on om hq =
  sym (suc-doubleℕ-half-odd n on) ∙ cong (suc ∘ doubleℕ) hq ∙ suc-doubleℕ-half-odd m om

-- ───────────────────────────────────────────────────────────────
-- Section 15: half is bounded
-- ───────────────────────────────────────────────────────────────

half≤ : (n : ℕ) → half n ≤ n
half≤ zero = zero , refl
half≤ (suc zero) = 1 , refl
half≤ (suc (suc n)) =
  let (d , p) = half≤ n
  in suc d , cong suc (+-suc d (half n)) ∙ cong (suc ∘ suc) p

-- ───────────────────────────────────────────────────────────────
-- Section 16: doubleℕ is monotone
-- ───────────────────────────────────────────────────────────────

doubleℕ-suc : (n : ℕ) → doubleℕ (suc n) ≡ suc (suc (doubleℕ n))
doubleℕ-suc n = refl

private
  doubleℕ-+ : (a b : ℕ) → doubleℕ (a +ℕ b) ≡ doubleℕ a +ℕ doubleℕ b
  doubleℕ-+ zero b = refl
  doubleℕ-+ (suc a) b = cong (suc ∘ suc) (doubleℕ-+ a b)

doubleℕ-mono : (m n : ℕ) → m ≤ n → doubleℕ m ≤ doubleℕ n
doubleℕ-mono m n (d , p) = doubleℕ d , sym (doubleℕ-+ d m) ∙ cong doubleℕ p

-- ───────────────────────────────────────────────────────────────
-- Section 17: Parity of addition
-- ───────────────────────────────────────────────────────────────

Even+Even→Even : {m n : ℕ} → Even m → Even n → Even (m +ℕ n)
Even+Even→Even {m} {n} (j , p) (k , q) =
  j +ℕ k , cong (_+ℕ n) p ∙ cong (doubleℕ j +ℕ_) q ∙ sym (doubleℕ-+ j k)

Odd+Odd→Even : {m n : ℕ} → Odd m → Odd n → Even (m +ℕ n)
Odd+Odd→Even {m} {n} (j , p) (k , q) =
  suc (j +ℕ k) , cong (_+ℕ n) p ∙ cong (suc (doubleℕ j) +ℕ_) q ∙ lem j k
  where
  lem : (a b : ℕ) → suc (doubleℕ a) +ℕ suc (doubleℕ b) ≡ doubleℕ (suc (a +ℕ b))
  lem zero b = refl
  lem (suc a) b = cong (suc ∘ suc) (lem a b)

Even+Odd→Odd : {m n : ℕ} → Even m → Odd n → Odd (m +ℕ n)
Even+Odd→Odd {m} {n} (j , p) (k , q) =
  j +ℕ k , cong (_+ℕ n) p ∙ cong (doubleℕ j +ℕ_) q ∙ lem j k
  where
  lem : (a b : ℕ) → doubleℕ a +ℕ suc (doubleℕ b) ≡ suc (doubleℕ (a +ℕ b))
  lem zero b = refl
  lem (suc a) b = cong (suc ∘ suc) (lem a b)

Odd+Even→Odd : {m n : ℕ} → Odd m → Even n → Odd (m +ℕ n)
Odd+Even→Odd {m} {n} (j , p) (k , q) =
  j +ℕ k , cong (_+ℕ n) p ∙ cong (suc (doubleℕ j) +ℕ_) q ∙ lem j k
  where
  lem : (a b : ℕ) → suc (doubleℕ a) +ℕ doubleℕ b ≡ suc (doubleℕ (a +ℕ b))
  lem zero b = refl
  lem (suc a) b = cong (suc ∘ suc) (lem a b)

-- ───────────────────────────────────────────────────────────────
-- Section 18: Convenience eliminators
-- ───────────────────────────────────────────────────────────────

-- Eliminate by parity into any type family
parityElim : ∀ {ℓ} {A : ℕ → Type ℓ}
  → ((k : ℕ) → A (doubleℕ k))
  → ((k : ℕ) → A (suc (doubleℕ k)))
  → (n : ℕ) → A n
parityElim fe fo n with parity n
... | even k = fe k
... | odd k  = fo k

-- Non-dependent parity case split
parityRec : ∀ {ℓ} {A : Type ℓ}
  → ((k : ℕ) → A)
  → ((k : ℕ) → A)
  → (n : ℕ) → A
parityRec {A = A} fe fo = parityElim {A = λ _ → A} fe fo

-- Case split using Even/Odd witnesses
evenOddElim : ∀ {ℓ} {A : ℕ → Type ℓ}
  → ((n : ℕ) → Even n → A n)
  → ((n : ℕ) → Odd n → A n)
  → (n : ℕ) → A n
evenOddElim fe fo n with even-or-odd n
... | inl e = fe n e
... | inr o = fo n o

-- Computation rules for evenOddElim
evenOddElim-even : ∀ {ℓ} {A : ℕ → Type ℓ}
  → {fe : (n : ℕ) → Even n → A n}
  → {fo : (n : ℕ) → Odd n → A n}
  → (k : ℕ)
  → evenOddElim fe fo (doubleℕ k) ≡ fe (doubleℕ k) (Even-doubleℕ k)
evenOddElim-even {fe = fe} {fo = fo} k with even-or-odd (doubleℕ k)
... | inl e = cong (fe (doubleℕ k)) (Σ≡Prop (λ j → isSetℕ _ _) (Even-unique e (Even-doubleℕ k)))
... | inr o = ⊥.rec (¬Even∧Odd (Even-doubleℕ k) o)

evenOddElim-odd : ∀ {ℓ} {A : ℕ → Type ℓ}
  → {fe : (n : ℕ) → Even n → A n}
  → {fo : (n : ℕ) → Odd n → A n}
  → (k : ℕ)
  → evenOddElim fe fo (suc (doubleℕ k)) ≡ fo (suc (doubleℕ k)) (Odd-suc-doubleℕ k)
evenOddElim-odd {fe = fe} {fo = fo} k with even-or-odd (suc (doubleℕ k))
... | inl e = ⊥.rec (¬Even∧Odd e (Odd-suc-doubleℕ k))
... | inr o = cong (fo (suc (doubleℕ k))) (Σ≡Prop (λ j → isSetℕ _ _) (Odd-unique o (Odd-suc-doubleℕ k)))
