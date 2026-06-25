
module CategoryTheory.StuffFromStoneAboutBAs where
open import BooleanRing.BooleanRingMaps
open import CountablyPresentedBooleanRings.Definitions 
open import Cubical.Data.Sigma
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sum
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso ; rec* to empty-func)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning
open import Cubical.Data.Nat.Bijections.Sum

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism renaming (isIso to isRealIso ; compIso to compRealIso)
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary hiding (⟪_⟫)

open import Cubical.HITs.PropositionalTruncation as PT

open import CountablyPresentedBooleanRings.Examples.Bool
open import QuickFixes
open import StoneSpaces.Spectrum

open import BooleanRing.BoolRingUnivalence

open import Cubical.Categories.Category.Base 
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor 
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Equivalence.AdjointEquivalence hiding (adjunction)
open import Cubical.Categories.Isomorphism renaming (invIso to CatInvIso)
open import Cubical.Categories.Instances.Sets
open import Cubical.Tactics.CategorySolver.Reflection

open import CategoryTheory.BasicFacts
open import CategoryTheory.SigmaPropCat
open import CategoryTheory.Image

open import CategoryTheory.StuffThatWasInStoneAndShouldBeOrganized 

open Category hiding (_∘_)
open Functor
open isUnivalent 

private 
  variable ℓ ℓ' : Level

BACat : Category (ℓ-suc ℓ) ℓ
BACat {ℓ} .ob                   = BooleanRing ℓ
BACat .Hom[_,_]                 = BoolHom
BACat .id {x = B}               = idBoolHom B
BACat ._⋆_ f g                  = g ∘cr f
BACat .⋆IdL _                   = CommRingHom≡ refl
BACat .⋆IdR _                   = CommRingHom≡ refl
BACat .⋆Assoc _ _ _             = CommRingHom≡ refl
BACat .isSetHom {x = B} {y = C} = isSetBoolHom B C 

--BooleωCat : Category (ℓ-suc ℓ-zero) ℓ-zero
--BooleωCat = ΣPropCat BACat λ B → is-countably-presented B , squash₁ 
-- Annoyingly, there is some level stuff here that makes we have to make choices. 
BooleωCat : Category (ℓ-suc ℓ-zero) ℓ-zero
BooleωCat = ΣPropCat* BACat λ B → is-countably-presented-alt B , squash₁ 

module _ (B C : BooleanRing ℓ-zero)  where
  open isIso
  -- Idea : show BACAT is Univalent 
  -- we need to show that the map B ≡ C → CatIso BooleωCat B C  induced by sending refl to IdIso
  -- is itself an equivalence. We will decompose it into BoolPath followed by the following:
  -- Then we show using J that this is indeed a decomposition, and thus the map is an equivalence
  -- I instead went for the same result for BooleanRing, and think that if C is univalent, 
  -- so is any full subcategory of C. 

  BAIso≅BAEquiv : Iso (CatIso BACat B C) (BooleanRingEquiv B C)
  BAIso≅BAEquiv .Iso.fun ((f , fHom) , fIso) .fst = isoToEquiv $ 
    iso f (fst $ inv fIso) (funExt⁻ $ cong fst $ sec fIso) (funExt⁻ $ cong fst $ ret fIso)
  BAIso≅BAEquiv .Iso.fun ((f , fHom) , fIso) .snd = fHom
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .fst .fst = f 
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .fst .snd = fHom
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .snd .inv .fst = fst $ invEquiv (f , fEqu)
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .snd .inv .snd = invIsHom B C (f , fHom) (IsoToIsIso (equivToIso (f , fEqu)))
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .snd .sec = CommRingHom≡ $ cong fst (invEquiv-is-linv (f , fEqu))
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .snd .ret = CommRingHom≡ $ cong fst (invEquiv-is-rinv (f , fEqu))
  BAIso≅BAEquiv .Iso.sec e = BooleanRingEquiv≡ B C _ e refl
  BAIso≅BAEquiv .Iso.ret  e = CatIso≡ _ e refl 
  
  pathToIsoDecomp : (B ≡ C) ≃ (CatIso BACat B C)
  pathToIsoDecomp = compEquiv (invEquiv $ BoolRingPath B C) (isoToEquiv (invIso BAIso≅BAEquiv)) 

pathToIsoDecompAtRefl : (B : BooleanRing ℓ-zero) → fst (pathToIsoDecomp B B) refl ≡ idCatIso
pathToIsoDecompAtRefl B = CatIso≡ _ _ (CommRingHom≡ (BoolRingPathInvRefl≡Idfun B)) 

pathToIsoDecompIsDecomp : (B C : BooleanRing ℓ-zero) → pathToIso {x = B} {y = C} ≡ fst (pathToIsoDecomp B C)
pathToIsoDecompIsDecomp B C = funExt $ 
  J (λ C' p → pathToIso {x = B} {y = C'} p ≡ fst (pathToIsoDecomp B C') p) 
  (pathToIso-refl ∙ (sym $ pathToIsoDecompAtRefl B)) 

BACatUnivalent : isUnivalent BACat
BACatUnivalent .univ B C = subst isEquiv (sym (pathToIsoDecompIsDecomp B C)) (snd $ pathToIsoDecomp B C) 

BooleωEmbedding : Functor BooleωCat BACat
BooleωEmbedding .F-ob      = fst
BooleωEmbedding .F-hom f   = f
BooleωEmbedding .F-id      = refl
BooleωEmbedding .F-seq _ _ = refl 

BooleωEmbeddingIsFullyFaithful : isFullyFaithful BooleωEmbedding
BooleωEmbeddingIsFullyFaithful B C .equiv-proof f .fst .fst           = f
BooleωEmbeddingIsFullyFaithful B C .equiv-proof f .fst .snd           = refl
BooleωEmbeddingIsFullyFaithful B C .equiv-proof f .snd (g , Embedg=f) = Σ≡Prop 
 (λ _ → isSetBoolHom (fst B) (fst C) _ f) $ sym Embedg=f

BooleωEmbeddingIsEmbedding : isEmbedding (BooleωEmbedding .F-ob)
BooleωEmbeddingIsEmbedding = snd (EmbeddingΣProp λ _ → squash₁)

BooleωUnivalent : isUnivalent BooleωCat 
BooleωUnivalent = Cuniv BooleωCat BACat BACatUnivalent BooleωEmbedding BooleωEmbeddingIsEmbedding
 BooleωEmbeddingIsFullyFaithful 

SpGeneralFunctor : Functor BACat ((SET ℓ-zero) ^op) 
SpGeneralFunctor .F-ob  B   = SpGeneralBooleanRing B , isSetBoolHom B BoolBR
SpGeneralFunctor .F-hom f g = g ∘cr f
SpGeneralFunctor .F-id      = funExt λ _ → CommRingHom≡ refl
SpGeneralFunctor .F-seq _ _ = funExt λ _ → CommRingHom≡ refl

module _ where
  open IsCommRingHom
  -- this, just as pointwisestructure, looks generizalable
  evaluationIsHom' : (B : BooleanRing ℓ-zero) → IsBoolRingHom (snd B) (evaluationMapGeneralBooleanRing B) 
    (snd $ 2^ (SpGeneralBooleanRing B))
  evaluationIsHom' B .pres0     = funExt λ f → pres0 (snd f)
  evaluationIsHom' B .pres1     = funExt λ f → pres1 (snd f)
  evaluationIsHom' B .pres+ x y = funExt λ f → pres+ (snd f) x y
  evaluationIsHom' B .pres· x y = funExt λ f → pres· (snd f) x y
  evaluationIsHom' B .pres- x   = funExt λ f → pres- (snd f) x 

  evaluationIsHom : (B : Booleω) → IsBoolRingHom (snd (fst B)) (evaluationMap B) (snd $ 2^ (Sp B))
  evaluationIsHom B = evaluationIsHom' (fst B)

  evaluationHomGeneralBooleanRing : (B : BooleanRing ℓ-zero) → BoolHom B (2^ (SpGeneralBooleanRing B))
  evaluationHomGeneralBooleanRing B .fst = evaluationMapGeneralBooleanRing B
  evaluationHomGeneralBooleanRing B .snd = evaluationIsHom' B 

  evaluationHom : (B : Booleω) → BoolHom (fst B) (2^ (Sp B))
  evaluationHom B = evaluationHomGeneralBooleanRing (fst B)

  

module SpDecAdjunction (B : BooleanRing ℓ-zero) (X : Set) where
  flipArgs : BoolHom B (2^ X) → X → ⟨ B ⟩ → Bool
  flipArgs f x b = (f $cr b) x 

  open IsCommRingHom
  flipArgsGivesHom : (f : BoolHom B (2^ X)) → (x : X) → IsBoolRingHom (snd B) (flipArgs f x) (snd BoolBR)
  flipArgsGivesHom f x .pres0     = cong (λ f → f x) (pres0 (snd f))
  flipArgsGivesHom f x .pres1     = cong (λ f → f x) (pres1 (snd f))
  flipArgsGivesHom f x .pres+ a b = cong (λ f → f x) (pres+ (snd f) a b)
  flipArgsGivesHom f x .pres· a b = cong (λ f → f x) (pres· (snd f) a b)
  flipArgsGivesHom f x .pres- a   = cong (λ f → f x) (pres- (snd f) a) 

  BoolHom→SetHom : (f : BoolHom B (2^ X)) → (x : X) → SpGeneralBooleanRing B
  BoolHom→SetHom f x = flipArgs f x , flipArgsGivesHom f x 

  flipArgsOtherDirection : (X → SpGeneralBooleanRing B) → ⟨ B ⟩ → X → Bool
  flipArgsOtherDirection f b x = f x $cr b 

  flipArgsOtherDirectionGivesHom : (f : (X → SpGeneralBooleanRing B)) → 
    IsBoolRingHom (snd B) (flipArgsOtherDirection f) (snd $ 2^ X)
  flipArgsOtherDirectionGivesHom f .pres0     = funExt λ x → pres0 (snd $ f x)
  flipArgsOtherDirectionGivesHom f .pres1     = funExt λ x → pres1 (snd $ f x)
  flipArgsOtherDirectionGivesHom f .pres+ a b = funExt λ x → pres+ (snd $ f x) a b
  flipArgsOtherDirectionGivesHom f .pres· a b = funExt λ x → pres· (snd $ f x) a b
  flipArgsOtherDirectionGivesHom f .pres- a   = funExt λ x → pres- (snd $ f x) a 

  SetHom→BoolHom : (X → SpGeneralBooleanRing B) → BoolHom B (2^ X)
  SetHom→BoolHom f = flipArgsOtherDirection f , flipArgsOtherDirectionGivesHom f

  adjunction : BoolHom B (2^ X) ≃ (X → SpGeneralBooleanRing B)
  adjunction .fst                          = BoolHom→SetHom 
  adjunction .snd .equiv-proof f .fst .fst = SetHom→BoolHom f
  adjunction .snd .equiv-proof f .fst .snd = funExt λ _ → CommRingHom≡ refl
  adjunction .snd .equiv-proof f .snd (g , flipArgsG≡f) = Σ≡Prop 
    (λ x → isSet→ (isSetSp B) (BoolHom→SetHom x) f) 
    (cong SetHom→BoolHom (sym flipArgsG≡f) ∙ CommRingHom≡ (funExt λ x → refl) ) 

2^Functor : Functor (SET ℓ-zero ^op) (BACat)
2^Functor .F-ob X = 2^ ⟨ X ⟩
2^Functor .F-hom f .fst g x = g (f x)
2^Functor .F-hom f .snd .IsCommRingHom.pres0     = refl
2^Functor .F-hom f .snd .IsCommRingHom.pres1     = refl
2^Functor .F-hom f .snd .IsCommRingHom.pres+ a b = refl
2^Functor .F-hom f .snd .IsCommRingHom.pres· a b = refl
2^Functor .F-hom f .snd .IsCommRingHom.pres- a   = refl
2^Functor .F-id                     = CommRingHom≡ refl
2^Functor .F-seq f g                = CommRingHom≡ refl 

Sp⊣2^' : SpGeneralFunctor NaturalBijection.⊣ 2^Functor
Sp⊣2^' .NaturalBijection._⊣_.adjIso    {c = B} {d = X}  = invIso $ equivToIso $ SpDecAdjunction.adjunction B ⟨ X ⟩
Sp⊣2^' .NaturalBijection._⊣_.adjNatInD _ _              = CommRingHom≡ refl
Sp⊣2^' .NaturalBijection._⊣_.adjNatInC _ _ = funExt λ _ → CommRingHom≡ refl

Sp⊣2^ : SpGeneralFunctor UnitCounit.⊣ 2^Functor
Sp⊣2^ = adj'→adj _ _ Sp⊣2^' 

ηBA : 𝟙⟨ BACat ⟩ ⇒  2^Functor ∘F SpGeneralFunctor
ηBA = UnitCounit._⊣_.η Sp⊣2^ 

ηBA' : (B : BooleanRing ℓ-zero) → BoolHom B (2^ (SpGeneralBooleanRing B))
ηBA' B = NatTrans.N-ob ηBA B 

ηBA'Agrees : (B : BooleanRing ℓ-zero) → ηBA' B ≡ evaluationHomGeneralBooleanRing B
ηBA'Agrees B = CommRingHom≡ refl

ηBooleω' : 𝟙⟨ BACat ⟩ ∘F BooleωEmbedding ⇒  (2^Functor ∘F SpGeneralFunctor) ∘F BooleωEmbedding
ηBooleω' = ηBA ∘ˡ BooleωEmbedding 

ηBooleω : BooleωEmbedding ⇒ (2^Functor ∘F SpGeneralFunctor) ∘F BooleωEmbedding
ηBooleω = subst  (λ F → F ⇒ (2^Functor ∘F SpGeneralFunctor) ∘F BooleωEmbedding) F-rUnit ηBooleω' 

SpFunctor : Functor BooleωCat ((SET ℓ-zero) ^op)
SpFunctor = SpGeneralFunctor ∘F BooleωEmbedding
