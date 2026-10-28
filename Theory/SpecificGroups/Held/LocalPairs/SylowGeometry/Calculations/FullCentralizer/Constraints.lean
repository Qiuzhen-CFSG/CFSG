module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.Action
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.ZeroCheckPart0
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.ZeroCheckPart1
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.ZeroCheckPart2
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.ZeroCheckPart3
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.ZeroCheckPart4
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.ZeroCheckPart5
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.ZeroCheckPart6
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.ZeroCheckPart7
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer.ZeroCheckPart8
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Separation

/-!
# Rigidity of the Held representative's graph centralizer

A commuting permutation has at most two possible images of point zero.
If it fixes zero, it fixes its entire representative orbit. Six points in
that orbit separate point two by graph signatures. Five fixed points from
the orbits of zero and two then separate point one. A word carries two to
three, so the existing four-point graph certificate proves identity.

Every finite signature and path is kernel checked in the original action.
See `Source/README.md` and its reproducible discovery script. This theorem
concerns the full graph-preserving group, without assumptions on P's center,
normalizer, order or Sylow status. Source: ATLAS HeG1-p2058B0; GLS3 Table 5.3p.
-/

public section

namespace Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer
open Held.NormalizerGraph

private theorem candidates0 (x : Fin 2058) (hx : test0 x) : x = 0 ∨ x = 1395 := by
  by_cases h0 : x.val < 256
  · exact zero_candidates_0 x (by omega) h0 hx
  by_cases h1 : x.val < 512
  · exact zero_candidates_1 x (by omega) h1 hx
  by_cases h2 : x.val < 768
  · exact zero_candidates_2 x (by omega) h2 hx
  by_cases h3 : x.val < 1024
  · exact zero_candidates_3 x (by omega) h3 hx
  by_cases h4 : x.val < 1280
  · exact zero_candidates_4 x (by omega) h4 hx
  by_cases h5 : x.val < 1536
  · exact zero_candidates_5 x (by omega) h5 hx
  by_cases h6 : x.val < 1792
  · exact zero_candidates_6 x (by omega) h6 hx
  by_cases h7 : x.val < 2048
  · exact zero_candidates_7 x (by omega) h7 hx
  exact zero_candidates_8 x (by omega) x.isLt hx

private theorem test0_at_zero : test0 0 := by decide +kernel

private lemma test0_invariant (σ : Equiv.Perm (Fin 2058)) (hσ : CommutesGenerators σ)
    (x : Fin 2058) : test0 (σ x) ↔ test0 x := by
  simp only [test0, ne_eq, eq_walk_iff σ hσ]

lemma images_zero (σ : Equiv.Perm (Fin 2058)) (hσ : CommutesGenerators σ) :
    σ 0 = 0 ∨ σ 0 = 1395 :=
  candidates0 _ ((test0_invariant σ hσ 0).mpr test0_at_zero)

private def separators2 : List (Fin 2058) := [0, 1189, 1994, 1419, 1450, 1640]
private def paths2 : List (List (Fin 4)) := [[], [1, 2, 1, 0, 1], [1, 0], [1], [1, 2], [1, 0, 1]]

set_option maxRecDepth 16384 in
private theorem paths2_eq : paths2.map (fun w => walk w 0) = separators2 := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem separate2 : ∀ x : Fin 2058,
    CardBound.baseSignature separators2 x = CardBound.baseSignature separators2 2 → x = 2 := by
  decide +kernel

private def separators1 : List (Fin 2058) := [0, 1471, 1901, 1654, 739]
private def paths1 : List (Fin 2058 × List (Fin 4)) :=
  [(0, []), (2, [1, 3]), (2, [2, 3, 1]), (0, [1, 3]), (2, [0])]

private theorem paths1_eq : paths1.map (fun rw => walk rw.2 rw.1) = separators1 := by decide +kernel

private theorem paths1_roots : ∀ rw ∈ paths1, rw.1 = 0 ∨ rw.1 = 2 := by
  simp [paths1]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem separate1 : ∀ x : Fin 2058,
    CardBound.baseSignature separators1 x = CardBound.baseSignature separators1 1 → x = 1 := by
  decide +kernel

set_option maxRecDepth 16384 in
lemma fix_zero_eq_one (σ : Equiv.Perm (Fin 2058)) (hσ : CommutesGenerators σ)
    (hg : σ ∈ preservingGroup) (h0 : σ 0 = 0) : σ = 1 := by
  have hsep2 : ∀ b ∈ separators2, σ b = b := by
    intro b hb
    rw [← paths2_eq] at hb
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hb
    rw [walk_commute σ hσ, h0]
  have h2 : σ 2 = 2 := separate2 _ (CardBound.baseSignature_invariant _ σ hg hsep2 2)
  have hsep1 : ∀ b ∈ separators1, σ b = b := by
    intro b hb
    rw [← paths1_eq] at hb
    obtain ⟨⟨r, w⟩, hw, rfl⟩ := List.mem_map.mp hb
    rw [walk_commute σ hσ]
    rcases paths1_roots (r, w) hw with he | he
    · change r = 0 at he
      rw [he, h0]
    · change r = 2 at he
      rw [he, h2]
  have h1 : σ 1 = 1 := separate1 _ (CardBound.baseSignature_invariant _ σ hg hsep1 1)
  have h3 : σ 3 = 3 := by
    have hw : walk [3, 1, 0, 2, 1, 3] 2 = 3 := by decide +kernel
    rw [← hw, walk_commute σ hσ, h2]
  apply CardBound.four_fixed_eq_one σ hg
  intro x hx
  have he : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
    have hv : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 := by omega
    rcases hv with h | h | h | h <;> simp only [Fin.ext_iff] <;> omega
  rcases he with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer
