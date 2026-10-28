module

public import CFSG.Quasithin.Chapter3.Section02.ReducedOrbit

/-!
# The local orbit module V in the original FSU

Apply the internal-module construction to H=L₀T itself. Its SQTK property
comes from the original maximal two-local subgroup; its actor alternative
comes directly from the original local C-component. Since L₀ fixes the
seed and normalizes its T-orbit span, the full H-orbit span is exactly V.
D.3.3 and D.3.4 then prove reducedness of this original local subgroup.

Source: Aschbacher–Smith, Lemma 3.2.2(8), combined manuscript of
1 March 2004, printed p.579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

/-- The source internal hypotheses also hold in the original L₀T. -/
theorem local_internal_module
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    InternalModuleHypotheses K (ReducedNormal.representation (localJoin T L))
      (T.subtype le_sup_right) ((localOrbit T L).subgroupOf (localJoin T L))
      D.seedSpace := by
  let H := localJoin T L
  let X := (localOrbit T L).subgroupOf H
  have hXM : H ≤ D.maximalLocal := (D.lemma_3_2_3_uniqueness h127).2.1
  have hHM := (D.simpleQTKE.twoLocal_sqtk
    (D.lemma_3_2_3_uniqueness h127).1.1).subgroup (H.subgroupOf D.maximalLocal)
  have hH : IsSQTK K H := (IsSQTK.equiv (subgroupOfEquivOfLe hXM)).mp hHM
  have hn : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  let := hn
  have hpX : pResidual 2 X = ⊤ := (pResidual_eq_top_iff 2 X).mpr
    (((pResidual_eq_top_iff 2 (localOrbit T L)).mp D.orbit_residual).of_surjective
      (subgroupOfEquivOfLe (show localOrbit T L ≤ H from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show localOrbit T L ≤ H from le_sup_left)).symm.surjective)
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hL : (L.subgroupOf H).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  let e := subgroupOfEquivOfLe hLH
  let q := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
    (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact IsPGroup.of_bot)
  let := D.quasisimple
  have hq : IsQuasisimple ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv q.symm
  have hcases : InternalActorCases (T.subtype le_sup_right) X
      (by rw [normalizer_eq_top]; exact le_top) := by
    refine Or.inl ⟨L.subgroupOf H, hL, hq, ?_⟩
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (show localOrbit T L ≤ H from le_sup_left),
      map_componentOrbit, map_subgroupOf_eq_of_le hLH]
    change localOrbit T L = componentOrbit L
      (((T : Subgroup G).subgroupOf H).map H.subtype)
    rw [map_subgroupOf_eq_of_le le_sup_right]
  refine ⟨hH, inferInstance, hn, hpX, hcases,
    ReducedNormal.normal_actor_representation_twoCore_eq_bot H X,
    D.homogeneous.isIrrPlus, ?_⟩
  have hj : X ⊔ ((T.subtype le_sup_right : Sylow 2 H) : Subgroup H) = ⊤ := by
    change (localOrbit T L).subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  rw [hj]
  have he : (⊤ : Subgroup H).pCoreIn 2 = pCore 2 H := pCore_map_iso 2 topEquiv
  rw [he]
  exact ReducedNormal.representation_twoCore_stabilizes H D.seedSpace

/-- The original seed's full L₀T-orbit is its prescribed T-orbit. -/
theorem local_orbitSpan_eq_sylowSpan :
    orbitSpan (ReducedNormal.representation (localJoin T L)) ⊤ D.seedSpace =
      orbitSpan (ReducedNormal.representation (localJoin T L))
        ((T : Subgroup G).subgroupOf (localJoin T L)) D.seedSpace := by
  let ρ := ReducedNormal.representation (localJoin T L)
  let X := (localOrbit T L).subgroupOf (localJoin T L)
  let S := (T : Subgroup G).subgroupOf (localJoin T L)
  have hj : X ⊔ S = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hs : (⊤ : Subgroup (localJoin T L)) ≤
      subspaceStabilizer ρ (orbitSpan ρ S D.seedSpace) := by
    rw [← hj]
    exact sup_le (orbitSpan_component_invariant ρ D.homogeneous.normalizes
      D.homogeneous.isIrrPlus) (orbitSpan_invariant ρ S D.seedSpace)
  exact le_antisymm (orbitSpan_le ρ (le_orbitSpan ρ S D.seedSpace) hs)
    (orbitSpan_le ρ (le_orbitSpan ρ ⊤ D.seedSpace)
      (le_top.trans (orbitSpan_invariant ρ ⊤ D.seedSpace)))

/-- The linear local orbit is exactly the original subgroup V. -/
theorem local_orbitImage_eq_module :
    ReducedNormal.subspaceImage (localJoin T L)
      (orbitSpan (ReducedNormal.representation (localJoin T L)) ⊤ D.seedSpace) =
        D.moduleSubgroup := by
  rw [D.local_orbitSpan_eq_sylowSpan]
  exact D.module_eq_subspaceImage.symm

/-- The original V is a member of R₂(L₀T), not just contained in it. -/
theorem module_reduced
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    IsPReduced 2 (D.moduleSubgroup.subgroupOf (localJoin T L)) := by
  have hi := D.local_internal_module h127
  have hr := ReducedNormal.subspaceImage_isPReduced_of_action_core (localJoin T L)
    (orbitSpan (ReducedNormal.representation (localJoin T L)) ⊤ D.seedSpace)
    (orbitSpan_invariant _ ⊤ D.seedSpace) hi.faithfulOrbit_twoCore_eq_bot
  rwa [D.local_orbitImage_eq_module] at hr

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
