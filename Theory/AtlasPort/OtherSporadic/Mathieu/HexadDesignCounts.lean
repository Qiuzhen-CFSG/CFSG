/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.HeptadIntersections
public import Theory.AtlasPort.OtherSporadic.Combinatorics.SteinerPairCount

/-!
# Incidence and intersections in the derived hexad design

In the twice-derived Golay design, 21 hexads contain a point and five
contain a pair of distinct points. Distinct hexads intersect in zero or two
points. The proofs use derived-design counting and lift intersections to
heptads through the removed coordinate.

Source: `Atlas/Mathieu/HexadDesignCounts.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open Atlas.Combinatorics
attribute [local instance] Classical.propDecidable
local instance (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _
local instance (a : Omega) (p : Mathieu23Points a) : Fintype (Mathieu22Points a p) := Fintype.ofFinite _

theorem mathieu22Blocks_through_point_card (a : Omega) (p : Mathieu23Points a)
    (b : Mathieu22Points a p) :
    ((mathieu22Blocks a p).filter (fun B => b ∈ B)).card = 21 := by
  rw [← derivedBlocks_through_card]
  exact twice_derived_mathieu23Blocks_card a p b

theorem mathieu22Blocks_through_pair_card (a : Omega) (p : Mathieu23Points a)
    (b c : Mathieu22Points a p) (hbc : b ≠ c) :
    ((mathieu22Blocks a p).filter (fun B => b ∈ B ∧ c ∈ B)).card = 5 := by
  have hv : Fintype.card (Mathieu22Points a p) = 22 := by
    rw [← Nat.card_eq_fintype_card,mathieu22_degree]
  have h := steiner_three_pair_count (mathieu22Blocks a p) hv
    (mathieu22Blocks_size a p) (mathieu22_steiner a p) {b,c} (by simp [hbc])
  simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff] at h
  convert h using 1
  congr 1
  ext B
  simp only [Finset.mem_filter]

theorem mathieu22_hexad_intersection (a : Omega) (p : Mathieu23Points a)
    (B C : Finset (Mathieu22Points a p)) (hB : B ∈ mathieu22Blocks a p)
    (hC : C ∈ mathieu22Blocks a p) (hBC : B ≠ C) :
    (B ∩ C).card = 0 ∨ (B ∩ C).card = 2 := by
  let e := derivedBlocksThroughEquiv (mathieu23Blocks a) p
  let B' := e ⟨B,hB⟩
  let C' := e ⟨C,hC⟩
  have hne : B'.val ≠ C'.val := by
    intro h
    have he := e.injective (Subtype.ext h)
    exact hBC (congrArg Subtype.val he)
  have h := mathieu23_heptad_intersection a B'.val C'.val B'.prop.1 C'.prop.1 hne
  have he : (B'.val ∩ C'.val).card = (B ∩ C).card+1 := by
    change (insert p (complementBlockLift p B) ∩ insert p (complementBlockLift p C)).card = _
    rw [← Finset.insert_inter_distrib]
    have hm : complementBlockLift p B ∩ complementBlockLift p C = complementBlockLift p (B ∩ C) := by
      change B.map (Function.Embedding.subtype _) ∩ C.map (Function.Embedding.subtype _) =
        (B ∩ C).map (Function.Embedding.subtype _)
      exact (Finset.map_inter _ _).symm
    rw [hm,Finset.card_insert_of_notMem (complementBlockLift_not_mem _ _),complementBlockLift_card]
    rfl
  rw [he] at h
  omega

end Atlas.Codes
