{-# OPTIONS --cubical --guardedness #-}
module StoneSpaces.Examples.Cantor where

open import StoneSpaces.Spectrum
open import Cubical.Data.Unit

open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.HITs.PropositionalTruncation as PT
open import CountablyPresentedBooleanRings.Examples.Bool
open import CountablyPresentedBooleanRings.Examples.TrivialBA
open import Cubical.Algebra.BooleanRing.Initial
open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import BooleanRing.FreeBooleanRing.FreeBool
open import Cubical.Algebra.CommRing

open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import AntiEquivalence
open import BasicDefinitions

freeℕCP : countablyPresentedBooleanRing
freeℕCP = freeBA ℕ , ∣ free-on-countable-has-freeℕ-presentation ℕ countℕ ∣₁ 

CantorIsStone : hasStoneStr binarySequence
CantorIsStone .fst = freeℕCP
CantorIsStone .snd = sym $ ua (isoToEquiv (freeBA-universal-property ℕ BoolBR)) 

CantorSpace : StoneSpace
CantorSpace = binarySequence , CantorIsStone

