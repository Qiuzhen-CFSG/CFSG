module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
public import CFSG.Quasithin.Chapter3.Section02.FundamentalModule
public import CFSG.Quasithin.Chapter3.Section02.SourceLocalConsequences
public import CFSG.Quasithin.Chapter3.Section01.Source318
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.ReducedNormal.SubspaceQuotientAction
/-!
# The original 3.1.8 bound on the whole chosen-module orbit

The Fundamental Setup gives the literal Sylow centralizer of V^T. Internal
reduced-module theory proves this same orbit is reduced, and completed A/C
gives the unique maximal two-local N_G(L). Hence the original theorem
3.1.8(1) applies to LT/C_LT(V^T). The intrinsic quotient and vector
identifications transfer its bound to the existing faithful orbit action.

Only the genuine earlier SourceTheorem318One remains an input. No cubic
bound on the seed and no selected quotient-model list is assumed.
Source: Aschbacher--Smith 3.1.8(1), 3.2.5 and 12.2.2, pp.576,580,794--795.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)

include D h

theorem orbit_centralizer :
    (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let F := D.fundamentalSetup h
  have hu := F.lemma_3_2_3_uniqueness
    (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      h.simpleQTKE T h.maximal_faithful.1)
  have hc := Chapter3.Section02.source_reduced_seed_local_centralizer T
    (Chapter3.Section02.localOrbit T L) F.maximalLocal
    (Chapter3.Section02.localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
    F.simpleQTKE hu.1 F.internal_actor_residual F.internal_actor_cases
    F.seedSpace F.homogeneous.isIrrPlus
  change (T : Subgroup G) ⊓ centralizer (componentOrbit F.seed (T : Subgroup G) : Set G) =
    (Chapter3.Section02.localOrbit T L ⊔ (T : Subgroup G)).pCoreIn 2 at hc
  rwa [D.localOrbit_eq, D.fundamentalSetup_seed h] at hc

theorem orbit_intrinsic_centralizer :
    (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
      centralizer (ReducedNormal.intrinsicSubspace (L ⊔ (T : Subgroup G))
        D.orbitSpace : Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let H := L ⊔ (T : Subgroup G)
  let Q := ReducedNormal.intrinsicSubspace H D.orbitSpace
  have hmap : Q.map H.subtype = componentOrbit V (T : Subgroup G) := D.orbitSpace_image
  have he : ((T : Subgroup G).subgroupOf H ⊓ centralizer (Q : Set H)).map H.subtype =
      (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [← hmap]
    ext g
    constructor
    · rintro ⟨x, ⟨hxT, hxC⟩, rfl⟩
      refine ⟨hxT, ?_⟩
      rintro _ ⟨v, hv, rfl⟩
      exact congrArg (fun y : H => (y : G)) (hxC v hv)
    · rintro ⟨hxT, hxC⟩
      let x : H := ⟨g, (show (T : Subgroup G) ≤ H from le_sup_right) hxT⟩
      refine ⟨x, ⟨hxT, ?_⟩, rfl⟩
      intro v hv
      exact Subtype.ext (hxC v (mem_map_of_mem _ hv))
  apply Subgroup.map_injective H.subtype_injective
  exact he.trans (D.orbit_centralizer h)

theorem orbit_cubicRatio_le_of_source318 (h318 : Chapter3.SourceTheorem318One G) :
    cubicRatio D.orbitRepresentation ≤ 2 := by
  let H := L ⊔ (T : Subgroup G)
  let Q := ReducedNormal.intrinsicSubspace H D.orbitSpace
  have hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (ReducedNormal.representation H)
      D.orbitSpace := orbitSpan_invariant _ ⊤ D.space
  have hr : IsPReduced 2 Q := by
    change IsPReduced 2 (ReducedNormal.intrinsicSubspace H D.orbitSpace)
    rw [ReducedNormal.intrinsicSubspace_eq]
    exact ReducedNormal.subspaceImage_isPReduced_of_action_core H D.orbitSpace hW
      (D.orbit_twoCore_eq_bot h)
  let := hr.normal
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      h.simpleQTKE T h.maximal_faithful.1
  have hn : (L.subgroupOf (normalizer (L : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  have he : componentOrbit L (T : Subgroup G) = L := D.localOrbit_eq
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [he] using hu.normalizer_maximal
  have hj : H ≤ normalizer (L : Set G) := by
    simpa only [he] using hu.normalizer_contains
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
      N = normalizer (L : Set G) := by
    simpa only [he] using hu.normalizer_unique
  have hb := h318 T L (normalizer (L : Set G)) h.maximal_faithful.2.1.2.1
    L.le_normalizer hn hm hj huniq
    Q hr (D.orbit_intrinsic_centralizer h)
  exact ReducedNormal.cubicRatio_image_le_of_intrinsic_quotient H D.orbitSpace hW 2 hb
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
