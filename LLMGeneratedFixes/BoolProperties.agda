module LLMGeneratedFixes.BoolProperties where
open import Cubical.Data.Bool
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.Sum

not≡true→≡false : (b : Bool) → not b ≡ true → b ≡ false
not≡true→≡false false _ = refl
not≡true→≡false true  p = ex-falso (false≢true p)

not≡false→≡true : (b : Bool) → not b ≡ false → b ≡ true
not≡false→≡true false p = ex-falso (true≢false p)
not≡false→≡true true  _ = refl

¬true→not≡true : (b : Bool) → ¬ b ≡ true → not b ≡ true
¬true→not≡true b p = cong not $ ¬true→false b p

and-elim-left : (a b : Bool) → a and b ≡ true → a ≡ true
and-elim-left false b p = ex-falso (false≢true p)
and-elim-left true _  _ = refl

and-elim-right : (a b : Bool) → a and b ≡ true → b ≡ true
and-elim-right a false p = ex-falso (true≢false (sym p ∙ and-comm a false))
and-elim-right _ true  _ = refl

deMorganBool : (a b : Bool) → a and b ≡ false → (a ≡ false) ⊎ (b ≡ false)
deMorganBool false _ _ = inl refl
deMorganBool true  b p = inr p

