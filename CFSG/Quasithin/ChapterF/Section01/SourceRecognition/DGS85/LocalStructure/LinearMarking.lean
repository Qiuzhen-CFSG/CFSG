module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs
public import Theory.SpecificGroups.SL2.BorelSupplementAction
public import Theory.GroupTheory.SylowLocalCore

/-!
# Marking the linear quotient at an actual neighbor

The full Borel is the full-vertex normalizer of its two-core. Its
intersection with the normal starred factor is the given starred Sylow,
so any additional normalizer would normalize that same Sylow and already
belong to the Borel. Conjugation transports the identity to every edge.

The edge core remains Sylow in the intrinsic Sylow-generated local group.
A surjective linear quotient with the actual vertex-core kernel can
therefore be conjugated in its target to send that Sylow onto the upper
root group. The preimage of the matrix Borel is then exactly the chosen
neighbor stabilizer. The quotient, field, and kernel are retained; no
independent action-marking assumption is needed for the path application.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, Hypothesis B', 6.0, and the proof of 6.8(a), pp.94--96, 118, 123.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P B : Subgroup G}

/-- The full Borel normalizes exactly its two-core in the full endpoint. -/
theorem source_full_normalizer_borel_core (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B) :
    P ⊓ normalizer (B.pCoreIn 2 : Set G) = B := by
  let := d.finite_P
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  let T := (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype
  have hTS : T ≤ B.pCoreIn 2 := pGroup_le_core_of_core_sylow B T
    (source_star_sylow_le_borel d) (d.sylow.isPGroup'.map _) hB
  have he : B.pCoreIn 2 ⊓ d.Pstar = T := by
    have hs : (B.pCoreIn 2).subgroupOf d.Pstar = (d.sylow : Subgroup d.Pstar) :=
      d.sylow.is_maximal' (isPGroup_pCoreIn 2 B).comap_subtype (by
        intro x hx
        exact hTS (mem_map_of_mem d.Pstar.subtype hx))
    have hm := congrArg (map d.Pstar.subtype) hs
    rwa [subgroupOf_map_subtype] at hm
  apply le_antisymm
  · have hn : P ⊓ normalizer (B.pCoreIn 2 : Set G) ≤ normalizer (T : Set G) := by
      rw [← he]
      exact (le_inf inf_le_right
        (inf_le_left.trans ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal))).trans
          inf_normalizer_le_normalizer_inf
    exact (le_inf inf_le_left hn).trans_eq (source_full_normalizer_star_sylow d)
  · exact le_inf hBP
      (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))

variable {P : Fin 2 → Subgroup G}
/-- This full-normalizer identity transports the literal edge core at every edge. -/
theorem source_edge_core_normalizer (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    stabilizer (family P) v ⊓ normalizer
      ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 : Set G) =
      stabilizer (family P) v ⊓ stabilizer (family P) w := by
  obtain ⟨g,hP,hE⟩ := source_edge_transport h hvw
  rw [hE,hP, Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
    2 (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    ← map_equiv_normalizer_eq,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
  congr 1
  cases ht : v.type
  · exact source_full_normalizer_borel_core (Classical.choice (h.local_data 0)) hB
  · exact source_full_normalizer_borel_core (Classical.choice (h.local_data 1)) hB

private theorem exists_borel_marking {J K : Type*} [Group J] [Finite J]
    [Field K] [Finite K] [CharP K 2]
    (q : J →* Matrix.SpecialLinearGroup (Fin 2) K) (hq : Function.Surjective q)
    (T : Sylow 2 J) (hk : q.ker ≤ (T : Subgroup J)) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 2) K,
      normalizer (T : Set J) = (Matrix.SpecialLinearGroup.rankOneBorel K).comap
        ((MulAut.conj a).toMonoidHom.comp q) := by
  let R := T.mapSurjective hq
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) K)
    R (Matrix.SpecialLinearGroup.upperUnipotentSylow K 2)
  let q' := (MulAut.conj a).toMonoidHom.comp q
  have hq' : Function.Surjective q' := (MulAut.conj a).surjective.comp hq
  have hroot : (T : Subgroup J).map q' = Matrix.SpecialLinearGroup.upperUnipotent K := by
    rw [show q' = (MulAut.conj a).toMonoidHom.comp q from rfl, ←Subgroup.map_map]
    change ((a • R : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) K)) :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) = _
    rw [ha]
    rfl
  have hk' : q'.ker ≤ (T : Subgroup J) := by
    intro x hx
    exact hk ((MulAut.conj a).map_eq_one_iff.mp hx)
  have hpre : (Matrix.SpecialLinearGroup.upperUnipotent K).comap q' = T := by
    rw [←hroot, comap_map_eq_self hk']
  refine ⟨a, ?_⟩
  change _ = (Matrix.SpecialLinearGroup.rankOneBorel K).comap q'
  rw [Matrix.SpecialLinearGroup.rankOneBorel, comap_normalizer_eq_of_surjective _ hq',
    hpre, T.coe_coe]

/-- Any actual linear quotient with the vertex-core kernel can be marked
at the chosen neighbor by conjugating the same quotient in its target. -/
theorem source_linear_borel_marking (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (q : graphLocalGroup (family P) v →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hq : Function.Surjective q)
    (hk : q.ker = (Q (family P) v).subgroupOf (graphLocalGroup (family P) v)) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 2) K,
      (stabilizer (family P) w).subgroupOf (graphLocalGroup (family P) v) =
        (Matrix.SpecialLinearGroup.rankOneBorel K).comap ((MulAut.conj a).toMonoidHom.comp q) := by
  let := finite_endpoints h
  let L := graphLocalGroup (family P) v
  let E := stabilizer (family P) v ⊓ stabilizer (family P) w
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hvw
  have he := sylow_image_eq_edge_core (stabilizer (family P) v) E inf_le_left
    (source_edge_core_sylow h hB hvw) T hT
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le (H := L) (sylowGenerated_le _)
    (sylow_le_sylowGenerated _ T)
  have hRs : (R : Subgroup L) = (E.pCoreIn 2).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hR, he, map_subgroupOf_eq_of_le]
    exact he ▸ sylow_le_sylowGenerated _ T
  have hkR : q.ker ≤ (R : Subgroup L) := by
    rw [hk,hRs]
    apply comap_mono
    exact (pCoreIn_le_sylow _ T).trans_eq he
  obtain ⟨a,ha⟩ := exists_borel_marking q hq R hkR
  refine ⟨a, ?_⟩
  rw [← ha]
  have hN : normalizer (R : Set L) =
      (normalizer (E.pCoreIn 2 : Set G)).subgroupOf L := by
    rw [← R.coe_coe,hRs]
    exact (subgroupOf_normalizer_eq (by
      rw [←he]
      exact sylow_le_sylowGenerated _ T)).symm
  rw [hN]
  have hn := congrArg (fun D : Subgroup G => D.subgroupOf L)
    (source_edge_core_normalizer h hB hvw)
  have hleft : (stabilizer (family P) v).subgroupOf L = ⊤ :=
    subgroupOf_eq_top.mpr (sylowGenerated_le _)
  change (stabilizer (family P) v).comap L.subtype = ⊤ at hleft
  simpa only [subgroupOf, comap_inf, hleft, top_inf_eq] using hn.symm
end CFSG.Quasithin.ChapterF.Source.DGS85
