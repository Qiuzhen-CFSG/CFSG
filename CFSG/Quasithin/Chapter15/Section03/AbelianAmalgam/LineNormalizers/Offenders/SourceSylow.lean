module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.SourceAssembly.Original
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement

/-!
# The unchanged Sylow and maximum families in the source replacement

Intersect the actual Sylow T_E with the normal centralizer C_H(E), then
map its intrinsic Sylow through the real temporary-core quotient. The
result is exactly q(S_E), with no arbitrary Sylow placement. Conjugacy in
that centralizer transfers maximum elementary orders and hence the literal
maximum family. The source Thompson containment supplies the maximum witness,
and escape of original I from M supplies nontriviality of q(J(C_H(E))).

These discharge the maximum, compatible Sylow, nontriviality and SQTK inputs
of BestReduction.SourceAssembly.Original. They keep the original Q_E distinct
from the full temporary core.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceSylow
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer
  BestReduction.SourceAssembly
variable {G : Type*} [Group G] [Finite G]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]

theorem centralizer_sylow (o : Geometry.OriginalData Y T V M E Pc) :
    ∃ S : Sylow 2 (localCentralizer T V E),
      (S : Subgroup _).map (localCentralizer T V E).subtype = centralizerSylow T V E := by
  let H := temporaryLineNormalizer T V E
  let C := localCentralizer T V E
  let : C.Normal := temporaryCentralizer_normal_of_original T V E
  obtain ⟨P, hP⟩ := (temporary_sylow_witnesses_of_original o).1
  obtain ⟨S, hS⟩ := P.exists_sylow_map_eq_inf_of_normal C
  refine ⟨S, hS.trans ?_⟩
  have hP' : (P : Subgroup H) = (lineT T E).subgroupOf H := by
    rw [← hP, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  rw [hP']
  ext x
  change ((x.val ∈ T ∧ x.val ∈ lineNormalizer E) ∧
    (x.val ∈ H ∧ x.val ∈ centralizer (E : Set G))) ↔
    (x.val ∈ T ∧ x.val ∈ centralizer (E : Set G))
  exact ⟨fun h => ⟨h.1.1, h.2.2⟩,
    fun h => ⟨⟨h.1, Subgroup.centralizer_le_normalizer _ h.2⟩, x.property, h.2⟩⟩

theorem quotient_sylow (o : Geometry.OriginalData Y T V M E Pc) :
    ∃ S : Sylow 2 ((localCentralizer T V E).map (QuotientGroup.mk' (localCore T V E))),
      (S : Subgroup _).map ((localCentralizer T V E).map
        (QuotientGroup.mk' (localCore T V E))).subtype =
        (centralizerSylow T V E).map (QuotientGroup.mk' (localCore T V E)) := by
  let C := localCentralizer T V E
  let q := QuotientGroup.mk' (localCore T V E)
  obtain ⟨S, hS⟩ := centralizer_sylow o
  refine ⟨S.mapSurjective (f := q.subgroupMap C) (q.subgroupMap_surjective C), ?_⟩
  rw [Sylow.coe_mapSurjective, map_map]
  change (S : Subgroup C).map (q.comp C.subtype) = _
  rw [← map_map, hS]

theorem maximum_comparison (o : Geometry.OriginalData Y T V M E Pc)
    (A : Subgroup (temporaryLineNormalizer T V E))
    (hA : A ∈ elementaryAbelianMaxSubgroups (centralizerSylow T V E)) :
    A ∈ elementaryAbelianMaxSubgroups (localCentralizer T V E) := by
  let C := localCentralizer T V E
  obtain ⟨S, hS⟩ := centralizer_sylow o
  have hSC : centralizerSylow T V E ≤ C := hS ▸ map_subtype_le _
  have hAC : A ≤ C := hA.1.trans hSC
  have hA' : A.subgroupOf C ∈ elementaryAbelianMaxSubgroups (S : Subgroup C) := by
    let := hA.2.1
    refine ⟨?_, IsElementaryAbelian.subgroupOf hAC, ?_⟩
    · intro a ha
      have hh : a.val ∈ (S : Subgroup C).map C.subtype := hS.symm ▸ hA.1 ha
      have hh' : a ∈ ((S : Subgroup C).map C.subtype).comap C.subtype := hh
      rwa [comap_map_eq_self_of_injective C.subtype_injective] at hh'
    · intro B hB hBe
      have h := hA.2.2 (B.map C.subtype) ((map_mono hB).trans_eq hS) (hBe.map C.subtype)
      rw [card_map_of_injective C.subtype_injective] at h
      rwa [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv]
  have htop := maxFamily_of_sylow_overgroup S (S : Subgroup C) (A.subgroupOf C) le_rfl hA'
  refine ⟨hAC, hA.2.1, fun B hBC hBe => ?_⟩
  let := hBe
  have h := htop.2.2 (B.subgroupOf C) le_top (IsElementaryAbelian.subgroupOf hBC)
  calc
    Nat.card B = Nat.card (B.subgroupOf C) := (Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv).symm
    _ ≤ Nat.card (A.subgroupOf C) := h
    _ = Nat.card A := Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv

theorem maximum_exists (o : Geometry.OriginalData Y T V M E Pc)
    (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G)) :
    ∃ B ∈ elementaryAbelianMaxSubgroups
      ((lineT T E).subgroupOf (temporaryLineNormalizer T V E)),
      B ≤ localCentralizer T V E := by
  let H := temporaryLineNormalizer T V E
  let S := (lineT T E).subgroupOf H
  obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty S
  have hmap : (elementaryAbelianMaxJ S).map H.subtype = elementaryAbelianMaxJ (lineT T E) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (lineT_le_temporary T V E o.line_le)]
  refine ⟨B, hB, fun b hb => ⟨b.property, ?_⟩⟩
  exact hJ (hmap ▸ mem_map_of_mem H.subtype (le_sSup hB hb))

theorem actor_nontrivial (o : Geometry.OriginalData Y T V M E Pc)
    (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G))
    (hNM : normalizer (V : Set G) ≤ M) (hI : ¬ lineI E ≤ lineM M E) :
    thompsonImage T V E ≠ ⊥ := by
  obtain ⟨S, hS, A, hA, hAC, hne⟩ := exists_temporary_max_of_local_structure
    M Y T V E o.line_le o.module_le_sylow o.sylow o.sylow_image o.residual_normal
    o.core_le_kernel (Geometry.OriginalData.residual_section_kernel_le_core o)
    o.local_core o.seed_commutator hNM hI hJ
  have htop := maxFamily_of_sylow_overgroup S (S : Subgroup _) A le_rfl hA
  have hmax : A ∈ elementaryAbelianMaxSubgroups (localCentralizer T V E) :=
    ⟨hAC, hA.2.1, fun B _ hB => htop.2.2 B le_top hB⟩
  intro hzero
  apply hne
  apply bot_unique
  have hle := map_mono (f := QuotientGroup.mk' (localCore T V E)) (le_sSup hmax)
  exact hle.trans_eq hzero

omit [IsMulCommutative V] in
theorem temporary_sqtk {K : GroupClass} (hG : IsSQTK K (lineNormalizer E)) :
    IsSQTK K (temporaryLineNormalizer T V E) :=
  (IsSQTK.equiv (subgroupOfEquivOfLe
    (show temporaryLineNormalizer T V E ≤ lineNormalizer E from inf_le_left))).mp
      (hG.subgroup ((temporaryLineNormalizer T V E).subgroupOf (lineNormalizer E)))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceSylow
