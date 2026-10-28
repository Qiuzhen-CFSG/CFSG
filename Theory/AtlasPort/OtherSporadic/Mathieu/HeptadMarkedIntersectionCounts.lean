/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Mathieu/HeptadMarkedIntersectionCounts.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.HeptadIntersections

/-!
Heptad intersection counts with a marked point in the Mathieu23 design.
Double-counting point incidences and using the possible intersection sizes
determines the marked intersections of sizes one and three.

Source: Gerald Höhn, ATLAS, `Atlas/Mathieu/HeptadMarkedIntersectionCounts.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance markedHeptadPointsFintype (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

theorem mathieu23_heptad_incidence_sum_inside (a : Omega) (b : Mathieu23Points a)
    (D : Finset (Mathieu23Points a)) (hD : D ∈ mathieu23Blocks a) (hb : b ∈ D) :
    (∑ B ∈ (mathieu23Blocks a).filter (fun B => b ∈ B), (D ∩ B).card) = 203 := by
  let S := (mathieu23Blocks a).filter (fun B => b ∈ B)
  have he (B : Finset (Mathieu23Points a)) : (D ∩ B).card = ∑ d ∈ D, if d ∈ B then 1 else 0 := by
    rw [← Finset.card_filter,Finset.filter_mem_eq_inter]
  simp_rw [he]
  rw [Finset.sum_comm]
  have hc (d : Mathieu23Points a) (hd : d ∈ D) :
      (∑ B ∈ S, if d ∈ B then 1 else 0) = if d = b then 77 else 21 := by
    rw [← Finset.card_filter]
    by_cases hdb : d = b
    · subst d
      simpa [S,Finset.filter_filter] using mathieu23_heptads_through_point_card a b
    · simp only [if_neg hdb,S,Finset.filter_filter]
      exact mathieu23Blocks_through_pair_card a b d (Ne.symm hdb)
  change (∑ d ∈ D, ∑ B ∈ S, if d ∈ B then 1 else 0) = 203
  rw [Finset.sum_congr rfl hc]
  have heq (d : Mathieu23Points a) : (if d = b then 77 else 21) = 21 + if d = b then 56 else 0 := by
    split_ifs <;> omega
  simp_rw [heq]
  simp [Finset.sum_add_distrib,hb,mathieu23Blocks_size a D hD]

theorem mathieu23_heptad_marked_one_card (a : Omega) (b : Mathieu23Points a)
    (D : Finset (Mathieu23Points a)) (hD : D ∈ mathieu23Blocks a) :
    ((mathieu23Blocks a).filter (fun B => b ∈ B ∧ (D ∩ B).card = 1)).card =
      if b ∈ D then 16 else 42 := by
  by_cases hb : b ∈ D
  · rw [if_pos hb]
    let S := (mathieu23Blocks a).filter (fun B => b ∈ B)
    have hs : S.card = 77 := mathieu23_heptads_through_point_card a b
    have hm : (∑ B ∈ S, (D ∩ B).card) = 203 :=
      mathieu23_heptad_incidence_sum_inside a b D hD hb
    have hid (B : Finset (Mathieu23Points a)) (hB : B ∈ S) :
        (D ∩ B).card + 2*(if (D ∩ B).card = 1 then 1 else 0) =
          3 + 4*(if B = D then 1 else 0) := by
      by_cases hBD : B = D
      · subst B
        rw [Finset.inter_self,mathieu23Blocks_size a D hD]
        simp
      · have hh := mathieu23_heptad_intersection a D B hD (Finset.mem_filter.mp hB).1 (Ne.symm hBD)
        rcases hh with hh | hh <;> simp [hh,hBD]
    have hh := Finset.sum_congr rfl hid
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.card_filter] at hh
    have hself : (S.filter (fun B => B = D)).card = 1 := by
      have he : S.filter (fun B => B = D) = {D} := by
        ext B; simp [S,Finset.mem_filter,and_assoc]; aesop
      rw [he]; rfl
    simp only [hm,hself,Finset.sum_const,smul_eq_mul,hs] at hh
    have hc : (S.filter (fun B => (D ∩ B).card = 1)).card = 16 := by omega
    simpa only [S,Finset.filter_filter] using hc
  · rw [if_neg hb]
    exact mathieu23_heptad_intersection_one_card a b D hD hb


theorem mathieu23_heptad_marked_three_card (a : Omega) (b : Mathieu23Points a)
    (D : Finset (Mathieu23Points a)) (hD : D ∈ mathieu23Blocks a) :
    ((mathieu23Blocks a).filter (fun B => b ∈ B ∧ (D ∩ B).card = 3)).card =
      if b ∈ D then 60 else 35 := by
  let S := (mathieu23Blocks a).filter (fun B => b ∈ B)
  have hs : S.card = 77 := mathieu23_heptads_through_point_card a b
  have hid (B : Finset (Mathieu23Points a)) (hB : B ∈ S) :
      (if (D ∩ B).card = 1 then 1 else 0) + (if (D ∩ B).card = 3 then 1 else 0) +
        (if B = D then 1 else 0) = (1 : ℕ) := by
    by_cases hBD : B = D
    · subst B; simp [mathieu23Blocks_size a D hD]
    · have hh := mathieu23_heptad_intersection a D B hD (Finset.mem_filter.mp hB).1 (Ne.symm hBD)
      rcases hh with hh | hh <;> simp [hh,hBD]
  have hh := Finset.sum_congr rfl hid
  simp only [Finset.sum_add_distrib,← Finset.card_filter,Finset.sum_const,smul_eq_mul,mul_one,hs] at hh
  have hself : (S.filter (fun B => B = D)).card = if b ∈ D then 1 else 0 := by
    by_cases hb : b ∈ D
    · have he : S.filter (fun B => B = D) = {D} := by
        ext B; simp [S,Finset.mem_filter,and_assoc]; aesop
      rw [he]; simp [hb]
    · have he : S.filter (fun B => B = D) = ∅ := by
        ext B; simp [S,Finset.mem_filter,and_assoc]; aesop
      rw [he]; simp [hb]
  have hone := mathieu23_heptad_marked_one_card a b D hD
  have hon : (S.filter (fun B => (D ∩ B).card = 1)).card = if b ∈ D then 16 else 42 := by
    simpa only [S,Finset.filter_filter] using hone
  rw [hself,hon] at hh
  have hres : (S.filter (fun B => (D ∩ B).card = 3)).card = if b ∈ D then 60 else 35 := by
    split_ifs at hh ⊢ <;> omega
  simpa only [S,Finset.filter_filter] using hres

end Atlas.Codes
