/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.HeptadPairCounts
public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadPairCounts

/-!
# HeptadIntersections

Derived heptads inherit their intersection possibilities from octads by restoring the
removed coordinate. Incidence double-counting and the pair counts then determine the
number of heptads with a specified one-point intersection.

Source: `Atlas/Mathieu/HeptadIntersections.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance heptadIntersectionPointsFintype (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

theorem octad_intersection_sizes (O P : Finset Omega) (hO : O ∈ octads) (hP : P ∈ octads) :
    (O ∩ P).card = 0 ∨ (O ∩ P).card = 2 ∨ (O ∩ P).card = 4 ∨ (O ∩ P).card = 8 := by
  obtain ⟨u,hu,rfl⟩ := (octads_mem O).mp hO
  obtain ⟨v,hv,rfl⟩ := (octads_mem P).mp hP
  have he := binary_weight_add u.val v.val
  rw [hu,hv,overlap_inter] at he
  have hs := golay_weights ⟨u.val+v.val,golay.add_mem u.prop v.prop⟩
  change hammingNorm (u.val+v.val) = 0 ∨ hammingNorm (u.val+v.val) = 8 ∨
    hammingNorm (u.val+v.val) = 12 ∨ hammingNorm (u.val+v.val) = 16 ∨
    hammingNorm (u.val+v.val) = 24 at hs
  omega

theorem mathieu23BlockLift_inter (a : Omega) (B C : Finset (Mathieu23Points a)) :
    mathieu23BlockLift a (B ∩ C) = mathieu23BlockLift a B ∩ mathieu23BlockLift a C := by
  simp [mathieu23BlockLift,Finset.map_inter]

theorem mathieu23_heptad_intersection (a : Omega) (B C : Finset (Mathieu23Points a))
    (hB : B ∈ mathieu23Blocks a) (hC : C ∈ mathieu23Blocks a) (hBC : B ≠ C) :
    (B ∩ C).card = 1 ∨ (B ∩ C).card = 3 := by
  have h := octad_intersection_sizes _ _ ((mathieu23Blocks_mem a B).mp hB)
    ((mathieu23Blocks_mem a C).mp hC)
  have he : (insert a (mathieu23BlockLift a B) ∩ insert a (mathieu23BlockLift a C)).card =
      (B ∩ C).card+1 := by
    rw [← Finset.insert_inter_distrib,← mathieu23BlockLift_inter,
      Finset.card_insert_of_notMem (mathieu23BlockLift_not_mem _ _),mathieu23BlockLift_card]
  rw [he] at h
  have hne : (B ∩ C).card ≠ 7 := by
    intro hh
    have h1 : B ∩ C = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [hh,mathieu23Blocks_size a B hB])
    have h2 : B ∩ C = C := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      (by rw [hh,mathieu23Blocks_size a C hC])
    exact hBC (h1.symm.trans h2)
  omega

theorem mathieu23_heptads_through_point_card (a : Omega) (b : Mathieu23Points a) :
    ((mathieu23Blocks a).filter (fun B => b ∈ B)).card = 77 := by
  rw [← Atlas.Combinatorics.derivedBlocks_through_card]
  exact mathieu22Blocks_card a b

theorem mathieu23_heptad_incidence_sum (a : Omega) (b : Mathieu23Points a)
    (D : Finset (Mathieu23Points a)) (hD : D ∈ mathieu23Blocks a) (hb : b ∉ D) :
    (∑ B ∈ (mathieu23Blocks a).filter (fun B => b ∈ B), (D ∩ B).card) = 147 := by
  have hc (d : Mathieu23Points a) (hd : d ∈ D) :
      (((mathieu23Blocks a).filter (fun B => b ∈ B)).filter (fun B => d ∈ B)).card = 21 := by
    rw [Finset.filter_filter]
    exact mathieu23Blocks_through_pair_card a b d (fun h => hb (h ▸ hd))
  have he (B : Finset (Mathieu23Points a)) : (D ∩ B).card = ∑ d ∈ D, if d ∈ B then 1 else 0 := by
    rw [← Finset.card_filter]
    rw [Finset.filter_mem_eq_inter]
  simp_rw [he]
  rw [Finset.sum_comm]
  have hf (d : Mathieu23Points a) (hd : d ∈ D) :
      (∑ B ∈ (mathieu23Blocks a).filter (fun B => b ∈ B), if d ∈ B then 1 else 0) = 21 := by
    rw [← Finset.card_filter]
    exact hc d hd
  rw [Finset.sum_congr rfl hf]
  simp [mathieu23Blocks_size a D hD]

theorem mathieu23_heptad_intersection_one_card (a : Omega) (b : Mathieu23Points a)
    (D : Finset (Mathieu23Points a)) (hD : D ∈ mathieu23Blocks a) (hb : b ∉ D) :
    ((mathieu23Blocks a).filter (fun B => b ∈ B ∧ (D ∩ B).card = 1)).card = 42 := by
  let S := (mathieu23Blocks a).filter (fun B => b ∈ B)
  have hs : S.card = 77 := mathieu23_heptads_through_point_card a b
  have hi (B : Finset (Mathieu23Points a)) (hB : B ∈ S) :
      (D ∩ B).card = 1 ∨ (D ∩ B).card = 3 := by
    obtain ⟨hB,hbB⟩ := Finset.mem_filter.mp hB
    exact mathieu23_heptad_intersection a D B hD hB (fun h => hb (h.symm ▸ hbB))
  have hc := Finset.card_filter_add_card_filter_not (s := S) (p := fun B => (D ∩ B).card = 1)
  have hm := mathieu23_heptad_incidence_sum a b D hD hb
  have he : (∑ B ∈ S, (D ∩ B).card) =
      (S.filter (fun B => (D ∩ B).card = 1)).card +
      3*(S.filter (fun B => (D ∩ B).card ≠ 1)).card := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun B => (D ∩ B).card = 1)]
    have h1 : (∑ B ∈ S.filter (fun B => (D ∩ B).card = 1), (D ∩ B).card) =
        (S.filter (fun B => (D ∩ B).card = 1)).card := by
      simp only [Finset.sum_congr rfl (fun B hB => (Finset.mem_filter.mp hB).2),Finset.sum_const,smul_eq_mul,mul_one]
    have h3 : (∑ B ∈ S.filter (fun B => (D ∩ B).card ≠ 1), (D ∩ B).card) =
        3*(S.filter (fun B => (D ∩ B).card ≠ 1)).card := by
      have hx := Finset.sum_congr rfl (fun B hB => (hi B (Finset.mem_filter.mp hB).1).resolve_left (Finset.mem_filter.mp hB).2)
      rw [hx]; simp [Nat.mul_comm]
    rw [h1,h3]
  change (∑ B ∈ S, (D ∩ B).card) = 147 at hm
  rw [hs] at hc
  rw [he] at hm
  have hf : S.filter (fun B => ¬(D ∩ B).card = 1) = S.filter (fun B => (D ∩ B).card ≠ 1) := by
    ext B; simp
  rw [hf] at hc
  have hn : (S.filter (fun B => (D ∩ B).card = 1)).card = 42 := by omega
  simpa only [S,Finset.filter_filter] using hn

end Atlas.Codes
