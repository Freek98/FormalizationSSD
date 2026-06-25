{-# OPTIONS --lossy-unification #-}
-- AI generated for Markov principle proof
module CommRingQuotients.ZeroInQuotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.Kernel
open import Cubical.Algebra.CommRing.Quotient.Base

private
  variable
    ℓ : Level

-- If x becomes 0 in the quotient ring R / I, then x lies in the ideal I.
--
-- This is the converse of `zeroOnIdeal` from
-- Cubical.Algebra.CommRing.Quotient.Base, and is obtained the same way:
-- membership of x in the kernel of the quotient map π : R → R/I is, by
-- definition, the proposition `π x ≡ 0`. The library result `kernel≡I`
-- identifies that kernel with I, so we just transport the membership
-- proof along it (here without the `sym` that `zeroOnIdeal` uses).
module _ {R : CommRing ℓ} (I : IdealsIn R) where
  private
    π = quotientHom R I

  open CommRingStr (snd (R / I)) using (0r)

  zeroInQuotient→inIdeal : (x : ⟨ R ⟩) → fst π x ≡ 0r → x ∈ fst I
  zeroInQuotient→inIdeal x x≡0 =
    subst (λ P → fst ((fst P) x)) (kernel≡I I) x≡0

