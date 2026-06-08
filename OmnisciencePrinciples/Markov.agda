module OmnisciencePrinciples.Markov where 

open import Axioms.StoneDuality
open import AntiEquivalence
open import BinarySequences 
open import BinarySequences.Properties

open import StoneSpaces.Spectrum
open import StoneSpaces.Examples.ClosedProp

open import CommRingQuotients.TrivialIdeal

open import CountablyPresentedBooleanRings.Examples.BoolQuotientByBinarySequence
open import CountablyPresentedBooleanRings.Definitions


open import Cubical.Functions.Fixpoint
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing.Quotient.Base
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.FreeBool
open  import BooleanRing.FreeBooleanRing.SurjectiveTerms
open  import BooleanRing.FreeBooleanRing.freeBATerms

open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base
open import Cubical.Tactics.CommRingSolver
open import CommRingQuotients.IdealTerms
open import BasicDefinitions 

MarkovPrinciple : Type₀ 
MarkovPrinciple = (α : binarySequence) → ¬ (∀ n → α n ≡ false) → Σ[ n ∈ ℕ ] α n ≡ true

weakMarkovPrinciple : Type₀ 
weakMarkovPrinciple = (α : binarySequence) → ¬ (∀ n → α n ≡ false) → ∃[ n ∈ ℕ ] α n ≡ true

weakMP→MP : weakMarkovPrinciple → MarkovPrinciple
weakMP→MP wMP α = hasSplitSupportΣℕ1 α ∘ wMP α

module _ (α : binarySequence) (α≠0 : ¬ (∀ n → α n ≡ false)) where
  2/αAsBA : countablyPresentedBooleanRing 
  2/αAsBA = 2/α α 
 
  module _ (f : Sp 2/αAsBA) where
    open BooleanRingStr (snd (fst 2/αAsBA))
    open IsCommRingHom
    
    f' : BoolHom BoolBR BoolBR
    f' = f ∘cr quotientImageHom

    f'αn=0 : (n : ℕ) → f' $cr (α n) ≡ false
    f'αn=0 n =  f' $cr (α n) ≡⟨⟩ 
                fst f (quotientImageHom $cr (α n)) ≡⟨ cong (fst f) (zeroOnImage n) ⟩ 
                fst f 𝟘 ≡⟨ pres0 (snd f)⟩ 
                false ∎ 

    f'=id : (x : Bool) → f' $cr x ≡ x
    f'=id false = pres0 (snd f')
    f'=id true  = pres1 (snd f') 
  
    αn=0 : (n : ℕ) → α n ≡ false
    αn=0 n = sym (f'=id (α n)) ∙ f'αn=0 n

    emptySp : ⊥
    emptySp = α≠0 αn=0 
 
  open BooleanRingStr (snd (fst 2/αAsBA))
  0=1In2/α : StoneDualityAxiom → 𝟘 ≡ 𝟙
  0=1In2/α sd = 0≡1-in-B sd 2/αAsBA emptySp where
    open SpectrumEmptyImpliesTrivial
  
  αIdeal : IdealsIn BoolCR
  αIdeal = IQ.genIdeal BoolCR α
  
  opaque 
    unfolding _/Im_
    1inαIdeal : StoneDualityAxiom → IQ.generatedIdeal BoolCR α true
    1inαIdeal sd = trivialQuotient→1∈I BoolCR αIdeal (sym $ 0=1In2/α sd) 
  
module _ (α : binarySequence)  where
  t∈I→αn : isInIdeal BoolCR α true → Σ[ n ∈ ℕ ] α n ≡ true
  t∈I→αn (isImage .true n αn=true)          = n , αn=true
  t∈I→αn (iszero  .true f=t)                = ex-falso (false≢true f=t)
  t∈I→αn (isSum .true false false t=f _ _ ) = ex-falso (true≢false t=f)
  t∈I→αn (isSum .true false true  _ _ t∈I ) = t∈I→αn t∈I
  t∈I→αn (isSum .true true  _     _ t∈I _ ) = t∈I→αn t∈I
  t∈I→αn (isMul .true false _     t=f _   ) = ex-falso (true≢false t=f)
  t∈I→αn (isMul .true true  false t=f _   ) = ex-falso (true≢false t=f)
  t∈I→αn (isMul .true true  true  _ t∈I   ) = t∈I→αn t∈I 

  αI = IQ.generatedIdeal BoolCR α
  
  ∃αn : αI true → ∃[ n ∈ ℕ ] α n ≡ true 
  ∃αn x = PT.map t∈I→αn (idealDecomp BoolCR α true x) 
 
weakMP : StoneDualityAxiom → weakMarkovPrinciple
weakMP sd α α≠0 = ∃αn α (1inαIdeal α α≠0 sd)

MP : StoneDualityAxiom → MarkovPrinciple 
MP = weakMP→MP ∘ weakMP 
