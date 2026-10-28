module
public import Theory.GroupTheory.AmalgamGraph.SylowCenterSpan
public import Theory.GroupTheory.AmalgamGraph.KernelSylow
public import Theory.GroupTheory.PCoreImage

/-!
# Sylow control of the local center centralizer

Let P be finite, with maximal edge subgroup B having a normal Sylow two-subgroup
which is also Sylow in P. If O₂(P) is self-centralizing, either it is Sylow in
C_P(Z), or the span Z of all Sylow omega-centers equals every one of those
omega-centers. If C_P(Z) lies in B, normal-Sylow inheritance gives the first
alternative. Otherwise maximality gives C_P(Z)B = P; both factors normalize
the selected omega-center, and Sylow conjugacy gives the second alternative.
The ambient completion need not be finite.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (6.2)(c), printed p.119.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]

private theorem centerSeed_conjugate (P : Subgroup G) (T : Sylow 2 P) (g : P) :
    omegaCenterIn (((g • T : Sylow 2 P) : Subgroup P).map P.subtype) =
      (omegaCenterIn ((T : Subgroup P).map P.subtype)).map
        (MulAut.conj (g : G)).toMonoidHom := by
  have hm : (((g • T : Sylow 2 P) : Subgroup P).map P.subtype) =
      ((T : Subgroup P).map P.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    change ((T : Subgroup P).map (MulAut.conj g).toMonoidHom).map _ = _
    rw [map_map, map_map]
    rfl
  rw [hm, NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj (g : G)).injective]

/-- A normalized Sylow omega-center already equals the full Sylow-center span. -/
theorem sylowCenterSpan_eq_seed_of_normalized (P : Subgroup G) [Finite P]
    (T : Sylow 2 P)
    (hn : P ≤ normalizer (omegaCenterIn ((T : Subgroup P).map P.subtype) : Set G)) :
    sylowCenterSpan P = omegaCenterIn ((T : Subgroup P).map P.subtype) := by
  apply le_antisymm _ (le_iSup _ T)
  apply iSup_le
  intro R
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq P T R
  rw [centerSeed_conjugate]
  exact (mem_normalizer_iff_map_conj_eq.mp (hn g.property)).le

/-- If one Sylow omega-center equals the normal span, they all do. -/
theorem sylowCenterSpan_eq_all_seeds_of_eq (P : Subgroup G) [Finite P]
    (T : Sylow 2 P) (he : sylowCenterSpan P = omegaCenterIn ((T : Subgroup P).map P.subtype))
    (R : Sylow 2 P) :
    sylowCenterSpan P = omegaCenterIn ((R : Subgroup P).map P.subtype) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq P T R
  rw [centerSeed_conjugate, ← he]
  exact (mem_normalizer_iff_map_conj_eq.mp
    (((normal_subgroupOf_iff_le_normalizer (sylowCenterSpan_le P)).mp
      (sylowCenterSpan_normal P)) g.property)).symm

/-- A vertex Sylow inside a two-closed edge is exactly the edge's embedded core. -/
theorem sylow_image_eq_edge_core (P B : Subgroup G) [Finite P]
    (hBP : B ≤ P) (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (T : Sylow 2 P) (hT : (T : Subgroup P).map P.subtype ≤ B) :
    (T : Subgroup P).map P.subtype = B.pCoreIn 2 := by
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  have ht := pGroup_le_core_of_core_sylow B _ hT (T.isPGroup'.map _) hB
  have he : (B.pCoreIn 2).subgroupOf P = (T : Subgroup P) :=
    T.is_maximal' (isPGroup_pCoreIn 2 B).comap_subtype (by
      intro x hx
      exact ht (mem_map_of_mem P.subtype hx))
  have hm := congrArg (map P.subtype) he
  rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 B).trans hBP)] at hm
  exact hm.symm

/-- In a finite primitive local pair with two-closed edge, the actual two-core
is Sylow in the centralizer of the Sylow-center span, or that span is a single
Sylow omega-center. No ambient finiteness or equality of core and kernel is used. -/
theorem centralizer_sylow_or_span_eq (P B : Subgroup G) [Finite P]
    (hBP : B ≤ P)
    (hmax : ∀ M : Subgroup G, B ≤ M → M ≤ P → M = B ∨ M = P)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hT : ∃ T : Sylow 2 P, (T : Subgroup P).map P.subtype ≤ B)
    (hc : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    (∃ R : Sylow 2 (P ⊓ centralizer (sylowCenterSpan P : Set G) : Subgroup G),
      (R : Subgroup (P ⊓ centralizer (sylowCenterSpan P : Set G) : Subgroup G)).map
        (P ⊓ centralizer (sylowCenterSpan P : Set G)).subtype = P.pCoreIn 2) ∨
    ∀ T : Sylow 2 P, sylowCenterSpan P = omegaCenterIn ((T : Subgroup P).map P.subtype) := by
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  let W := sylowCenterSpan P
  let C := P ⊓ centralizer (W : Set G)
  have hnW : P ≤ normalizer (W : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sylowCenterSpan_le P)).mp (sylowCenterSpan_normal P)
  have hnC : P ≤ normalizer (C : Set G) :=
    (le_inf P.le_normalizer (hnW.trans (normalizer_le_normalizer_centralizer W))).trans
      inf_normalizer_le_normalizer_inf
  have hQC : P.pCoreIn 2 ≤ C := by
    apply le_inf (pCoreIn_le 2 P)
    rw [le_centralizer_iff]
    exact (sylowCenterSpan_le_coreOmega P hc).trans
      (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
  by_cases hCB : C ≤ B
  · left
    obtain ⟨R, hR⟩ := core_sylow_of_le B C hCB hB
    refine ⟨R, ?_⟩
    rw [hR]
    apply le_antisymm (pCoreIn_mono_of_normalizes inf_le_left hnC)
    have h := inf_pCoreIn_le_of_le 2 (show C ≤ P from inf_le_left)
    rwa [inf_eq_right.mpr hQC] at h
  · right
    obtain ⟨T, hT⟩ := hT
    let E := omegaCenterIn ((T : Subgroup P).map P.subtype)
    have hEW : E ≤ W := le_iSup (fun R : Sylow 2 P =>
      omegaCenterIn ((R : Subgroup P).map P.subtype)) T
    have hnB : B ≤ normalizer (E : Set G) := by
      apply le_trans _ (normalizer_le_normalizer_omegaCenterIn _)
      rw [sylow_image_eq_edge_core P B hBP hB T hT]
      exact B.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
    have hnCE : C ≤ normalizer (E : Set G) :=
      (inf_le_right.trans (centralizer_le hEW)).trans (centralizer_le_normalizer _)
    have hcover : C ⊔ B = P := by
      rcases hmax (C ⊔ B) le_sup_right (sup_le inf_le_left hBP) with he | he
      · exact (hCB (le_sup_left.trans he.le)).elim
      · exact he
    apply sylowCenterSpan_eq_all_seeds_of_eq P T
    apply sylowCenterSpan_eq_seed_of_normalized
    exact hcover.ge.trans (sup_le hnCE hnB)
end Theory.GroupTheory.AmalgamGraph
