module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice
public import CFSG.Quasithin.Chapter14.Section06.SourceFactorizationComplete

/-!
# Residual factorizations for the constructed suitable vector

The separated-support construction supplies (U1)--(U3), including its
local Sylow clause, for the same H, M and Mc. The complete source 14.6.9
then applies at every actual IStar choice. The source rank and core-index
hypotheses are retained explicitly; neither is inferred from suitability.

Source: Aschbacher--Smith, 14.6.9, 14.6.17 and 14.6.24,
printed pp.1025--1028,1035--1036,1038--1039.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))

include hG hempty hM hunique hmany hcard e hab H hH

/-- Both original residual products for a vector constructed on separated supports. -/
theorem source_factorizations_of_separated_support
    (K W S : Subgroup G)
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ conjugateSpanBy (localModule T M) H)
    (hZW : centralInvolutions T ≤ W)
    (hKW : K ≤ normalizer (W : Set G))
    (hST : S ≤ (T : Subgroup G)) (hindex : S.relIndex (T : Subgroup G) = 2)
    (hU3 : Mc ⊓ normalizer (S : Set G) = (T : Subgroup G))
    (hseparate : ∀ t ∈ (T : Subgroup G), t ∉ S →
      W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralInvolutions T ∧
      K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G))
    (u : G) (huW : u ∈ W)
    (hfixed : ∀ s ∈ S, ⁅u,s⁆ ∈ centralInvolutions T)
    (hmoved : ∃ k ∈ K, ⁅u,k⁆ ∉ centralInvolutions T)
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (let L := sourceResidual M Mc
     let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  obtain ⟨heq,hm,hp,hl⟩ := source_suitable_of_separated_support
    hG T hempty hM hunique hmany hcard e hab H hH K W S hK hWU hZW hKW
      hST hindex hU3 hseparate u huW hfixed hmoved
  apply source_factorizations hG T hempty hM hunique hmany hcard e hab H hH u
    (hWU huW) _ hm hp _ hl hcoreIndex hrank I hI
  · rwa [heq]
  · rwa [heq]

/-- Select the involution and apply both residual factorizations to that same
choice. The branch still supplies its support geometry and source rank bounds. -/
theorem source_exists_suitable_with_factorizations_of_fixed_free_support
    (K W S : Subgroup G)
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ conjugateSpanBy (localModule T M) H)
    (hZW : centralInvolutions T < W)
    (hKW : K ≤ normalizer (W : Set G))
    (hSW : S ≤ normalizer (W : Set G))
    (hST : S ≤ (T : Subgroup G)) (hindex : S.relIndex (T : Subgroup G) = 2)
    (hU3 : Mc ⊓ normalizer (S : Set G) = (T : Subgroup G))
    (hseparate : ∀ t ∈ (T : Subgroup G), t ∉ S →
      W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralInvolutions T ∧
      K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G))
    (hfixedFree : ∀ u ∈ W, (∀ k ∈ K, ⁅u,k⁆ ∈ centralInvolutions T) →
      u ∈ centralInvolutions T)
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H))) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = S ∧
      ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G) ∧
      (∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (H ⊓ centralizer ({u} : Set G)) ∧
      (∀ I : Subgroup G, I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
        ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M) →
        let L := sourceResidual M Mc
        let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
        (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
          (L ⊔ (T : Subgroup G) : Subgroup G) =
            (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
              ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  obtain ⟨u,hu,hu2,hune,heq,hm,hp,hl,_⟩ :=
    source_exists_suitable_of_fixed_free_support
      hG T hempty hM hunique hmany hcard e hab H hH K W S
        hK hWU hZW hKW hSW hST hindex hU3 hseparate hfixedFree
  refine ⟨u,hu,hu2,hune,heq,hm,hp,hl,?_⟩
  intro I hI
  apply source_factorizations hG T hempty hM hunique hmany hcard e hab H hH u
    (hWU hu) _ hm hp _ hl hcoreIndex hrank I hI
  · rwa [heq]
  · rwa [heq]

end CFSG.Quasithin.Chapter14.Section06
