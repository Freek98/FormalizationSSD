
module StoneSpaces.Examples.Singleton where

open import StoneSpaces.Spectrum
open import Cubical.Data.Unit

open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import CountablyPresentedBooleanRings.Examples.Bool
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Algebra.CommRing

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

only1Map : isContr (SpGeneralBooleanRing BoolBR)
only1Map = BoolBR→ BoolBR , λ f → sym (CommRingHom≡ $ BoolBR→IsUnique BoolBR f) 

UnitIsStone : hasStoneStr Unit
UnitIsStone .fst = BoolCP
UnitIsStone .snd = isContr→≡Unit only1Map 

PointSpace : StoneSpace
PointSpace = Unit , UnitIsStone
