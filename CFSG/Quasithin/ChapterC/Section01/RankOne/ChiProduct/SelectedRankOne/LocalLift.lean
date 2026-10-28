module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.ThompsonSeed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ControlSource
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
/-!
# Lifting the actual local χ-seed in C.1.28

An escaping moved χ-block in a Sylow overgroup retains its original
Thompson movement and block module under inclusion. Its local omega-center
span maps into the ambient canonical module. The proved C.1.27/B.1.13 lift
and exceptional-A₇ control then produce an actual ambient moved χ-block.
All maps are the given subgroup inclusions.

Source: Aschbacher–Smith C.1.27–28, printed pp.132–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]

theorem ambient_outside_of_local_moved_chi
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hf : generalizedFitting G = pCore 2 G)
    (M H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hM : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (K : Subgroup H) (hK : IsChiBlockIn K) (hout : ¬ K ≤ M.subgroupOf H)
    (hm : K = ⁅K,elementaryAbelianMaxJ (T.subtype hTH : Subgroup H)⁆)
    (hsupport : (blockU K).map K.subtype ≤
      normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H)) :
    ∃ L : Subgroup G, ¬ L ≤ M ∧ IsChiBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let A := K.map H.subtype
  let V := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
  have hV := omegaCenter_normalClosure_reduced T
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
  let : IsElementaryAbelian 2 V := hV.elementary
  let e : K ≃* A := K.equivMapOfInjective H.subtype H.subtype_injective
  have hAc : IsChiBlock A := chi_of_equiv e hK.2
  have hKH : A ≤ H := map_subtype_le _
  have hAH : A ⊔ (T : Subgroup G) ≤ H := sup_le hKH hTH
  have hks : (A.subgroupOf H).IsSubnormal := by
    simpa only [A,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hK.1.subnormal
  have hsub : (A.subgroupOf (A ⊔ (T : Subgroup G))).IsSubnormal :=
    hks.comap (inclusion hAH)
  have hAJ : A = ⁅A,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
    have hh := congrArg (Subgroup.map H.subtype) hm
    rwa [map_commutator,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hh
  have hlocal : (normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H)).map
      H.subtype ≤ V := by
    apply map_le_iff_le_comap.mpr
    apply normalClosure_le_normal
    apply map_le_iff_le_comap.mp
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
    exact le_normalClosure
  have hUA : (blockU A).map A.subtype ≤ V := by
    rw [←Solvable.blockU_map_equiv e,map_map]
    have hh := (map_mono (f := H.subtype) hsupport).trans hlocal
    rw [map_map] at hh
    exact hh
  have hAo : ¬ A ≤ M := fun ha => hout (map_le_iff_le_comap.mp ha)
  obtain ⟨L,_,hLM,hLc,_,hLJ⟩ := BlockModuleSource.source_outside_moved_chi_of_thompson_seed
    hA hC h4 hG T hf M A V hM hAo rfl hAc hsub hUA hAJ
  exact ⟨L,hLM,hLc,hLJ⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
