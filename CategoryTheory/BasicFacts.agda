
module CategoryTheory.BasicFacts where
open import Cubical.Data.Sigma
open import Cubical.Categories.Instances.Functors
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
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism renaming (isIso to isRealIso ; compIso to compRealIso)
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation as PT

open import QuickFixes
open import Cubical.Categories.Category.Base 
open import Cubical.Categories.Category.Path
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Category 
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor 
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Equivalence.AdjointEquivalence hiding (adjunction)
open import Cubical.Categories.Isomorphism renaming (invIso to CatInvIso)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Opposite
open import Cubical.Tactics.CategorySolver.Reflection

open Category ⦃...⦄ hiding (_∘_)
private 
  variable ℓ ℓ' : Level

module isoUniqueness 
  {ℓ ℓ' : Level} {D : Category ℓ ℓ'}
  {x y  : D .ob} {f : D [ x , y ]} {g : D [ y , x ]} 
  (compToId : f ⋆⟨ D ⟩ g ≡ D .id) where
  open isIso
  SectionIsIsoToIsIso : isIso D f → isIso D g 
  SectionIsIsoToIsIso fIso = subst (isIso D) claim (snd invF) where 
    invF = CatInvIso (f , fIso)
    claim : fst invF ≡ g
    claim = fst invF                     ≡⟨ (sym $ D .⋆IdR (fst invF)) ⟩ 
            fst invF ⋆⟨ D ⟩ D .id        ≡⟨ cong (λ h → fst invF ⋆⟨ D ⟩ h) (sym compToId)  ⟩ 
            fst invF ⋆⟨ D ⟩ (f ⋆⟨ D ⟩ g) ≡⟨ sym (D .⋆Assoc (fst invF) f g) ⟩
            (fst invF ⋆⟨ D ⟩ f) ⋆⟨ D ⟩ g ≡⟨ cong (λ h → h ⋆⟨ D ⟩ g) (sec fIso) ⟩
            D .id ⋆⟨ D ⟩ g               ≡⟨ D .⋆IdL g ⟩
            g ∎ 
  RetractionIsIsoToIsIso : isIso D g → isIso D f
  RetractionIsIsoToIsIso gIso = subst (isIso D) claim (snd invG) where
    invG = CatInvIso (g , gIso)
    claim : fst invG ≡ f
    claim = fst invG                     ≡⟨ sym (D .⋆IdL (fst invG)) ⟩
            D . id ⋆⟨ D ⟩ fst invG       ≡⟨ cong (λ h → seq' D h (fst invG)) (sym compToId) ⟩
            (f ⋆⟨ D ⟩ g) ⋆⟨ D ⟩ fst invG ≡⟨ D .⋆Assoc f g (fst invG) ⟩
            f ⋆⟨ D ⟩ (g ⋆⟨ D ⟩ fst invG) ≡⟨ cong (λ h → f ⋆⟨ D ⟩ h) (ret gIso) ⟩
            f ⋆⟨ D ⟩ D .id               ≡⟨ D .⋆IdR f ⟩
            f ∎

module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') {x y : C .ob} (e : C [ x , y ]) (eIso : isIso C e) {z : C .ob} where
  open isIso 
  composeWithIsoLIso : Iso (C [ y , z ]) (C [ x , z ])
  composeWithIsoLIso .Iso.fun f = e        ⋆⟨ C ⟩ f 
  composeWithIsoLIso .Iso.inv g = inv eIso ⋆⟨ C ⟩ g
  composeWithIsoLIso .Iso.sec g = 
    e ⋆⟨ C ⟩ (inv eIso ⋆⟨ C ⟩ g) 
       ≡⟨ (sym $ C .⋆Assoc _ _ _) ⟩ 
    (e ⋆⟨ C ⟩ inv eIso) ⋆⟨ C ⟩ g
       ≡⟨ cong (λ h → h ⋆⟨ C ⟩ g) (ret eIso) ⟩ 
    C .id ⋆⟨ C ⟩ g
       ≡⟨ C .⋆IdL g ⟩ 
    g  ∎
  composeWithIsoLIso .Iso.ret  f = 
    inv eIso ⋆⟨ C ⟩ (e ⋆⟨ C ⟩ f) 
       ≡⟨ (sym $ C .⋆Assoc _ _ _) ⟩ 
    (inv eIso ⋆⟨ C ⟩ e) ⋆⟨ C ⟩ f
       ≡⟨ cong (λ h → h ⋆⟨ C ⟩ f) (sec eIso) ⟩ 
    C .id ⋆⟨ C ⟩ f
       ≡⟨ C .⋆IdL f ⟩ 
    f  ∎
  composeWithIsoRIso : Iso (C [ z , x ]) (C [ z , y ])
  composeWithIsoRIso .Iso.fun f = f ⋆⟨ C ⟩ e
  composeWithIsoRIso .Iso.inv g = g ⋆⟨ C ⟩ inv eIso
  composeWithIsoRIso .Iso.sec g = 
    g ⋆⟨ C ⟩ inv eIso ⋆⟨ C ⟩ e 
      ≡⟨ C .⋆Assoc _ _ _ ⟩ 
    g ⋆⟨ C ⟩ (inv eIso ⋆⟨ C ⟩ e)
      ≡⟨ cong (λ h → g ⋆⟨ C ⟩ h) (sec eIso) ⟩ 
    g ⋆⟨ C ⟩ C .id
      ≡⟨ C .⋆IdR g ⟩ 
    g ∎ 
  composeWithIsoRIso .Iso.ret f =
    f ⋆⟨ C ⟩ e ⋆⟨ C ⟩ inv eIso
      ≡⟨ C .⋆Assoc _ _ _ ⟩ 
    f ⋆⟨ C ⟩ (e ⋆⟨ C ⟩ inv eIso)
      ≡⟨ cong (λ h → f ⋆⟨ C ⟩ h) (ret eIso) ⟩ 
    f ⋆⟨ C ⟩ C .id
      ≡⟨ C .⋆IdR f ⟩ 
    f ∎ 

  composeWithIsoLisIso : isRealIso (λ (f : C [ y , z ] ) → e ⋆⟨ C ⟩ f) 
  composeWithIsoLisIso = IsoToIsIso composeWithIsoLIso 

  composeWithIsoRisIso : isRealIso (λ (f : C [ z , x ] ) → f ⋆⟨ C ⟩ e) 
  composeWithIsoRisIso = IsoToIsIso composeWithIsoRIso 

module _ {C : Category ℓ ℓ'} where
  instance
    _ = C
  open isUnivalent
  open Functor

  contravariantHomIso→CatIso : {c d : ob}
    → CatIso (PresheafCategory C ℓ') (C [-, c ]) (C [-, d ])
    → CatIso C c d
  contravariantHomIso→CatIso = liftIso {F = YO} isFullyFaithfulYO

  contravariantHomPath→CatIso : {c d : ob}
    → C [-, c ] ≡ C [-, d ]
    → CatIso C c d
  contravariantHomPath→CatIso p =
    contravariantHomIso→CatIso (pathToIso {C = PresheafCategory C _} p)

  contravariantHomPath→Path : isUnivalent C → {c d : ob}
    → C [-, c ] ≡ C [-, d ]
    → c ≡ d
  contravariantHomPath→Path univC p =
    CatIsoToPath univC (contravariantHomPath→CatIso p)


-- Covariant hom functor: C[c, -]
-- Reduced to the contravariant case by applying YO to C^op.
-- The only bridge needed: a path C[c,-] ≡ C[d,-] (Functor C (SET ℓ'))
-- induces a path (C^op)[-, c] ≡ (C^op)[-, d] (Functor (C^op^op) (SET ℓ'))
-- since C and (C^op)^op have the same Hom types definitionally.
module _ {C : Category ℓ ℓ'} where
  open Category
  open isUnivalent
  open Functor

  -- C ^op ^op ≡ C: all data (ob, Hom, id, ⋆) is definitionally the same.
  op-op≡ : C ^op ^op ≡ C
  op-op≡ = CategoryPath.mk≡ cp where
    open CategoryPath
    cp : CategoryPath (C ^op ^op) C
    ob≡ cp = refl
    Hom≡ cp = refl
    id≡ cp = refl
    ⋆≡ cp = refl

  -- Bridge: extract F-ob/F-hom paths from a C-functor path
  -- to build a (C^op)^op-functor path.
  private
    covPath→opOpPath : {c d : C .ob}
      → C [ c ,-] ≡ C [ d ,-]
      → (C ^op) [-, c ] ≡ (C ^op) [-, d ]
    covPath→opOpPath p = Functor≡
      (λ x → cong (λ F → F-ob F x) p)
      (λ f → cong (λ F → F-hom F f) p)

  covariantHomIso→CatIso^op : {c d : C .ob}
    → CatIso (PresheafCategory (C ^op) ℓ') ((C ^op) [-, c ]) ((C ^op) [-, d ])
    → CatIso (C ^op) c d
  covariantHomIso→CatIso^op = contravariantHomIso→CatIso {C = C ^op}

  covariantHomPath→CatIso^op : {c d : C .ob}
    → C [ c ,-] ≡ C [ d ,-]
    → CatIso (C ^op) c d
  covariantHomPath→CatIso^op p =
    contravariantHomPath→CatIso {C = C ^op} (covPath→opOpPath p)

  covariantHomPath→Path : isUnivalent (C ^op) → {c d : C .ob}
    → C [ c ,-] ≡ C [ d ,-]
    → c ≡ d
  covariantHomPath→Path univC^op p =
    CatIsoToPath univC^op (covariantHomPath→CatIso^op p)
