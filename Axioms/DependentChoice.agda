module Axioms.DependentChoice where
open import BasicDefinitions
open import Cubical.Data.Bool renaming ( _≤_ to _≤B_ ; _≥_ to _≥B_ ; _≟_ to _=B_)
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁ ; ∥_∥₁)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary

-- dual to Sequence as SequentialColimit
record Tower (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor tower
  field
    obj : ℕ → Type ℓ
    map : {n : ℕ} → obj (suc n) → obj n

open Tower

private
  variable
    ℓ : Level

record SequentialLimit (T : Tower ℓ) : Type ℓ where
  constructor limitPoint
  field
    branch : (n : ℕ) → obj T n
    commutes : (n : ℕ) → map T (branch (suc n)) ≡ branch n

projection : (T : Tower ℓ) → (n : ℕ) →  SequentialLimit T → Tower.obj T n
projection T n (limitPoint branch _) = branch n

allMapsSurjective : (Tower ℓ) → Type ℓ
allMapsSurjective (tower _ map) = (n : ℕ) → isSurjection (map {n})

projectionSurjective : (T : Tower ℓ) → Type ℓ
projectionSurjective T = isSurjection (projection T 0)

DependentChoiceTowerAxiom : {ℓ : Level} → Type (ℓ-suc ℓ)
DependentChoiceTowerAxiom {ℓ} = (T : Tower ℓ) → allMapsSurjective T → projectionSurjective T

DependentChoiceFor : (P : ℕ → Type ℓ) → Type _
DependentChoiceFor P = ((n : ℕ) → P n → ∥ P (suc n) ∥₁) → ∥ P 0 ∥₁  → ∥ ((n : ℕ) → P n) ∥₁

DependentChoice : {ℓ : Level} → Type _
DependentChoice {ℓ} = (P : ℕ → Type ℓ) → DependentChoiceFor P


ℕChoiceFor : (P : ℕ → Type ℓ) → Type _
ℕChoiceFor P = (∀ (n : ℕ) → ∥ P n ∥₁) → ∥ ((n : ℕ) → P n) ∥₁

DependentChoiceForToℕChoiceFor : (P : ℕ → Type ℓ) → DependentChoiceFor P → ℕChoiceFor P
DependentChoiceForToℕChoiceFor P dc ∀∃ = dc (λ n _ → ∀∃ (suc n)) (∀∃ zero)

ℕChoice : {ℓ : Level} → Type _
ℕChoice {ℓ} = (P : ℕ → Type ℓ) → ℕChoiceFor P

CountableChoice : {ℓ ℓ' : Level} → Type _
CountableChoice {ℓ} {ℓ'} = (A : Type ℓ) → has-Countability-structure A →
  (P : A → Type ℓ') → ((a : A) → ∥ P a ∥₁) → ∥ ((a : A) → P a) ∥₁

ℕChoiceToCountableChoice : {ℓ ℓ' : Level} → ℕChoice {ℓ'} → CountableChoice {ℓ} {ℓ'}
ℕChoiceToCountableChoice ℕchoice A (α , A=Σα) P ∀a|Pa| = PT.map Pℕ→PA (ℕchoice Pℕ ∀n|Pℕn|) where
  PAℕ : (n : ℕ) → (αn : α n ≡ true) → Type _
  PAℕ n αn = P $ Iso.inv A=Σα (n , αn)
  Pℕ : ℕ → Type _
  Pℕ n = (αn : α n ≡ true) → PAℕ n αn
  ∀n|Pℕn| : (n : ℕ) → ∥ Pℕ n ∥₁
  ∀n|Pℕn| n with (α n =B true)
  ... | yes αn = PT.map
    (λ pn αn' → subst (PAℕ n) (isSetBool (α n) true αn αn') pn)
    (∀a|Pa| (Iso.inv A=Σα (n , αn)))
  ... | no ¬αn = ∣ ex-falso ∘ ¬αn ∣₁
  Pℕ→PA : ((n : ℕ) → Pℕ n) → (a : A) → P a
  Pℕ→PA Pn a = subst P (Iso.ret A=Σα a) (uncurry Pn (Iso.fun A=Σα a))

DependentChoiceToℕChoice : {ℓ : Level} → DependentChoice {ℓ} → ℕChoice {ℓ}
DependentChoiceToℕChoice dc P = DependentChoiceForToℕChoiceFor P (dc P)

module TowerChoiceToDependentChoice {ℓ : Level} (dc : DependentChoiceTowerAxiom {ℓ})
  (P : ℕ → Type ℓ) (pSuc : (n : ℕ) → P n → ∥ P (suc n) ∥₁) (p0 : ∥ P 0 ∥₁ )   where
  PupTo : ℕ → Type ℓ
  PupTo zero = P 0
  PupTo (suc n) = PupTo n × P (suc n)

  |Pn| : (n : ℕ) → ∥ P n ∥₁
  |Pn| zero = p0
  |Pn| (suc n) = PT.rec PT.squash₁ (pSuc n) (|Pn| n)

  lastChoice : (n : ℕ) → PupTo n → P n
  lastChoice zero    p0 = p0
  lastChoice (suc n) (_ , pn+1) = pn+1

  forgetLastChoice : (n : ℕ) → PupTo (suc n) → PupTo n
  forgetLastChoice n = fst

  fstSurjective : (n : ℕ) → isSurjection $ forgetLastChoice n
  fstSurjective n pUpTon = PT.map
    (λ pn+1 → (pUpTon , pn+1 ) , refl)
    (pSuc n $ lastChoice n pUpTon)

  partialChoiceTower : Tower ℓ
  partialChoiceTower .obj = PupTo
  partialChoiceTower .map = fst

  projectionSurjectivePartialChoiceTower : projectionSurjective partialChoiceTower
  projectionSurjectivePartialChoiceTower = dc partialChoiceTower fstSurjective

  infiniteBranch : ∥ ((n : ℕ) → P n) ∥₁
  infiniteBranch = do
    p0elem    ← p0
    (limitPoint pUpTo _ , _) ← dc partialChoiceTower fstSurjective p0elem
    return λ n → lastChoice n (pUpTo n)

DependentChoiceTowerAxiomToDependentChoice : DependentChoiceTowerAxiom {ℓ} → DependentChoice {ℓ}
DependentChoiceTowerAxiomToDependentChoice = TowerChoiceToDependentChoice.infiniteBranch

