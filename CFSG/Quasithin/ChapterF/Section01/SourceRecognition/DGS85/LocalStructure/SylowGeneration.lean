module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CoreClosure
public import Theory.GroupTheory.SylowCenterFixedSpan
public import Theory.GroupTheory.AmalgamGraph.SylowGenerated

/-!
# Sylow generation of the genuine Chapter 6 local group

The full Borel core generates L = G* O₂(B) under the vertex stabilizer:
otherwise its normal closure lies in the two-closed Borel and the marked
starred Sylow becomes normal, contradicting rank-one properness. Thus L is
the intrinsic span of all vertex Sylows and is not two-closed. This also
proves that the definition is independent of the starred presentation.

Sylow conjugacy gives fixed-subgroup generation for the original Z under
this same L. When Z equals a Sylow omega-center, Sylow generation identifies
it with Ω₁(Z(L)), giving the exact second alternative in source 6.2(c).
The reduced F1.11 applications discharge the local Sylow and Borel premises.

Source: DGS, *Groups and Graphs* (1985), 6.0--6.2, pp.118--119, and the
fixed-space-generation correction required by 5.12. Model recognition in
6.1 is not asserted by these Sylow-generation results.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P B : Subgroup G}

theorem source_all_sylows_le_enlargement (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype ≤ B)
    (T : Sylow 2 P) : (T : Subgroup P).map P.subtype ≤ localEnlargement d := by
  let := d.finite_P
  obtain ⟨R, hR⟩ := hS
  have hRL : (R : Subgroup P).map P.subtype ≤ localEnlargement d :=
    (sylow_image_eq_edge_core P B (le_sup_right.trans d.supplement.le) hB R hR).le.trans le_sup_right
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq P R T
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact le_normalizer_iff.mp (localEnlargement_normalized d) g g.property x
    (hRL (mem_map_of_mem _ hx))

private theorem star_sylow_not_le_core (d : LocalRankOneData P B) :
    ¬ (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ P.pCoreIn 2 := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  intro hle
  have hc : P.pCoreIn 2 = d.Pstar.pCoreIn 2 := d.same_core.symm
  rw [hc] at hle
  have he : (d.sylow : Subgroup d.Pstar) = pCore 2 d.Pstar :=
    le_antisymm ((map_le_map_iff_of_injective d.Pstar.subtype_injective).mp hle)
      (pCore_isPGroup.le_sylow_of_normal d.sylow)
  have hn : (d.sylow : Subgroup d.Pstar).Normal := he ▸ inferInstance
  exact (rankOneSylowFacts_of_rankOneQuotient d.quotient d.sylow).proper.ne
    (normalizer_eq_top_iff.mpr hn)

theorem localEnlargement_eq_sylow_span (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B) :
    localEnlargement d = conjugateSpanBy (B.pCoreIn 2) P := by
  let := d.finite_P
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  let N := conjugateSpanBy (B.pCoreIn 2) P
  have hNL : N ≤ localEnlargement d := conjugateSpanBy_le le_sup_right (localEnlargement_normalized d)
  have hNP : N ≤ P := hNL.trans (localEnlargement_le d)
  let : Finite N := Finite.of_injective (inclusion hNP) (inclusion_injective _)
  have hTS : (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ B.pCoreIn 2 :=
    pGroup_le_core_of_core_sylow B _ (source_star_sylow_le_borel d) (d.sylow.isPGroup'.map _) hB
  apply le_antisymm _ hNL
  rcases source_overgroup_star_or_borel d N hNP (hTS.trans (le_conjugateSpanBy _ _)) with hl | hn
  · exact sup_le hl (le_conjugateSpanBy _ _)
  · have hcore : B.pCoreIn 2 ≤ N.pCoreIn 2 :=
      pGroup_le_core_of_core_sylow N _ (le_conjugateSpanBy _ _) (isPGroup_pCoreIn 2 B)
        (core_sylow_of_le B N hn hB)
    exact (star_sylow_not_le_core d (hTS.trans (hcore.trans
      (pCoreIn_mono_of_normalizes hNP (le_normalizer_conjugateSpanBy _ _))))).elim

theorem localEnlargement_eq_any_sylow_span (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype ≤ B)
    (T : Sylow 2 P) :
    localEnlargement d = conjugateSpanBy ((T : Subgroup P).map P.subtype) P := by
  let := d.finite_P
  obtain ⟨R, hR⟩ := hS
  have hRS := sylow_image_eq_edge_core P B (le_sup_right.trans d.supplement.le) hB R hR
  rw [localEnlargement_eq_sylow_span d hB, ← hRS]
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq P R T
  have hn : P ≤ normalizer (conjugateSpanBy ((R : Subgroup P).map P.subtype) P : Set G) :=
    le_normalizer_conjugateSpanBy _ _
  have hs : ((g • R : Sylow 2 P) : Subgroup P).map P.subtype =
      ((R : Subgroup P).map P.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    change ((R : Subgroup P).map (MulAut.conj g).toMonoidHom).map P.subtype = _
    rw [map_map, map_map]
    rfl
  rw [hs]
  have hP : P.map (MulAut.conj (g : G)).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer g.property)
  have hm := map_conjugateSpanBy ((R : Subgroup P).map P.subtype) P
    (MulAut.conj (g : G)).toMonoidHom
  rw [hP] at hm
  exact (mem_normalizer_iff_map_conj_eq.mp (hn g.property)).symm.trans hm

/-- The source enlargement is the intrinsic span of all vertex Sylows. -/
theorem localEnlargement_eq_sylowGenerated (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype ≤ B) :
    localEnlargement d = sylowGenerated P := by
  let := d.finite_P
  obtain ⟨T, hT⟩ := hS
  exact (localEnlargement_eq_any_sylow_span d hB ⟨T, hT⟩ T).trans
    (sylowGenerated_eq_span P T).symm

/-- The actual enlargement is not two-closed, since its marked starred
Sylow would otherwise lie in the unchanged vertex core. -/
theorem localEnlargement_not_closed (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B) :
    ¬ ∃ T : Sylow 2 (localEnlargement d),
      (T : Subgroup (localEnlargement d)) = pCore 2 (localEnlargement d) := by
  let := d.finite_P
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  let : Finite (localEnlargement d) := Finite.of_injective
    (inclusion (localEnlargement_le d)) (inclusion_injective _)
  intro hclosed
  have hTS : (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ B.pCoreIn 2 :=
    pGroup_le_core_of_core_sylow B _ (source_star_sylow_le_borel d) (d.sylow.isPGroup'.map _) hB
  apply star_sylow_not_le_core d
  exact (pGroup_le_core_of_core_sylow (localEnlargement d) _ (hTS.trans le_sup_right)
    (d.sylow.isPGroup'.map _) hclosed).trans_eq (localEnlargement_core d)

/-- The second alternative of 6.2(c) is the omega-center of the actual L. -/
theorem source_center_eq_enlargement_omega_of_seed (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype ≤ B)
    (T : Sylow 2 P)
    (he : sylowCenterSpan P = omegaCenterIn ((T : Subgroup P).map P.subtype)) :
    sylowCenterSpan P = omegaCenterIn (localEnlargement d) := by
  let := d.finite_P
  rw [localEnlargement_eq_sylowGenerated d hB hS]
  exact sylowCenterSpan_eq_generated_omega_of_seed P (source_core_selfCentralizing d) T he

theorem source_center_generated_by_enlargement_fixed (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype ≤ B)
    (T : Sylow 2 P) :
    conjugateSpanBy (sylowCenterSpan P ⊓ centralizer
      (((T : Subgroup P).map P.subtype : Subgroup G) : Set G)) (localEnlargement d) =
        sylowCenterSpan P := by
  let := d.finite_P
  exact sylowCenterSpan_generated_by_sylow_fixed P (localEnlargement d)
    (localEnlargement_le d) (source_all_sylows_le_enlargement d hB hS) T

theorem source_centralizer_sylow_or_enlargement_omega (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype ≤ B) :
    (∃ T : Sylow 2 (P ⊓ centralizer (sylowCenterSpan P : Set G) : Subgroup G),
      (T : Subgroup (P ⊓ centralizer (sylowCenterSpan P : Set G) : Subgroup G)).map
        (P ⊓ centralizer (sylowCenterSpan P : Set G)).subtype = P.pCoreIn 2) ∨
      sylowCenterSpan P = omegaCenterIn (localEnlargement d) := by
  let := d.finite_P
  rcases centralizer_sylow_or_span_eq P B (le_sup_right.trans d.supplement.le)
    (source_borel_maximal d) hB hS (source_core_selfCentralizing d) with hs | he
  · exact Or.inl hs
  · obtain ⟨T, hT⟩ := hS
    exact Or.inr (source_center_eq_enlargement_omega_of_seed d hB ⟨T, hT⟩ T (he T))

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

theorem reduced_enlargement_sylow_generation (h : HypothesisF11 L S) (i : Fin 2) :
    let d := Classical.choice ((reduced_triple h).local_data i)
    localEnlargement d = conjugateSpanBy (((B₀ L S).subgroupOf (G₀ L S)).pCoreIn 2)
      ((P₀ L S i).subgroupOf (G₀ L S)) :=
  localEnlargement_eq_sylow_span (Classical.choice ((reduced_triple h).local_data i))
    (reduced_borel_core_sylow h)

theorem reduced_enlargement_center_dichotomy (h : HypothesisF11 L S) (i : Fin 2) :
    let R := (P₀ L S i).subgroupOf (G₀ L S)
    let d := Classical.choice ((reduced_triple h).local_data i)
    (∃ T : Sylow 2 (R ⊓ centralizer (sylowCenterSpan R : Set (G₀ L S)) : Subgroup (G₀ L S)),
      (T : Subgroup (R ⊓ centralizer (sylowCenterSpan R : Set (G₀ L S)) : Subgroup (G₀ L S))).map
        (R ⊓ centralizer (sylowCenterSpan R : Set (G₀ L S))).subtype = R.pCoreIn 2) ∨
      sylowCenterSpan R = omegaCenterIn (localEnlargement d) :=
  source_centralizer_sylow_or_enlargement_omega (Classical.choice ((reduced_triple h).local_data i))
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h i)

theorem reduced_enlargement_fixed_generation (h : HypothesisF11 L S) (i : Fin 2)
    (T : Sylow 2 ((P₀ L S i).subgroupOf (G₀ L S))) :
    let R := (P₀ L S i).subgroupOf (G₀ L S)
    let d := Classical.choice ((reduced_triple h).local_data i)
    conjugateSpanBy (sylowCenterSpan R ⊓ centralizer
      (((T : Subgroup R).map R.subtype : Subgroup (G₀ L S)) : Set (G₀ L S)))
        (localEnlargement d) = sylowCenterSpan R :=
  source_center_generated_by_enlargement_fixed (Classical.choice ((reduced_triple h).local_data i))
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h i) T
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
