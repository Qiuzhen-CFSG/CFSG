/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu22PointStabilizer
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu23Witt
public import Theory.AtlasPort.OtherSporadic.Combinatorics.DerivedSteiner

/-!
# Mathieu22Witt

Deriving the degree-twenty-three Witt design at a second coordinate gives the hexad
design on twenty-two points. The derived-design construction gives block sizes,
uniqueness, counts, and preservation by the concrete two-point stabilizer.

Source: `Atlas/Mathieu/Mathieu22Witt.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section
set_option synthInstance.maxHeartbeats 200000

noncomputable section
namespace Atlas.Codes
open Finset
local instance (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _
local instance (a : Omega) (b : Mathieu23Points a) : Fintype (Mathieu22Points a b) := Fintype.ofFinite _

def mathieu22Blocks (a : Omega) (b : Mathieu23Points a) : Finset (Finset (Mathieu22Points a b)) :=
  Atlas.Combinatorics.derivedBlocks (mathieu23Blocks a) b

theorem mathieu22Blocks_size (a : Omega) (b : Mathieu23Points a)
    (B : Finset (Mathieu22Points a b)) (hB : B ∈ mathieu22Blocks a b) : B.card = 6 :=
  Atlas.Combinatorics.derivedBlocks_size (mathieu23Blocks a) b 6 (mathieu23Blocks_size a) B hB

theorem mathieu22_steiner (a : Omega) (b : Mathieu23Points a)
    (T : Finset (Mathieu22Points a b)) (hT : T.card = 3) :
    ∃! B, B ∈ mathieu22Blocks a b ∧ T ⊆ B :=
  Atlas.Combinatorics.derived_steiner (mathieu23Blocks a) b 3 (mathieu23_steiner a) T hT

theorem mathieu22Blocks_card (a : Omega) (b : Mathieu23Points a) :
    (mathieu22Blocks a b).card = 77 := by
  have h := Atlas.Combinatorics.steiner_block_count (mathieu22Blocks a b) 3 6
    (mathieu22Blocks_size a b) (mathieu22_steiner a b)
  have hd : Fintype.card (Mathieu22Points a b) = 22 := by
    rw [← Nat.card_eq_fintype_card, mathieu22_degree]
  rw [hd] at h
  norm_num [Nat.choose] at h
  omega

def mathieu22BlockLift (a : Omega) (b : Mathieu23Points a)
    (B : Finset (Mathieu22Points a b)) : Finset (Mathieu23Points a) :=
  Atlas.Combinatorics.complementBlockLift b B

theorem mathieu22Blocks_mem (a : Omega) (b : Mathieu23Points a)
    (B : Finset (Mathieu22Points a b)) :
    B ∈ mathieu22Blocks a b ↔ insert a (mathieu23BlockLift a (insert b (mathieu22BlockLift a b B))) ∈ octads := by
  exact (Atlas.Combinatorics.derivedBlocks_mem (mathieu23Blocks a) b B).trans
    (mathieu23Blocks_mem a (insert b (mathieu22BlockLift a b B)))

def mathieu22PermuteBlock (a : Omega) (b : Mathieu23Points a) (g : Mathieu22PointModel a b)
    (B : Finset (Mathieu22Points a b)) : Finset (Mathieu22Points a b) := by
  classical
  exact B.image (MulAction.toPermHom (Mathieu22PointModel a b) (Mathieu22Points a b) g)

theorem mathieu22BlockLift_permute (a : Omega) (b : Mathieu23Points a) (g : Mathieu22PointModel a b)
    (B : Finset (Mathieu22Points a b)) :
    mathieu22BlockLift a b (mathieu22PermuteBlock a b g B) =
      mathieu23PermuteBlock a g.val (mathieu22BlockLift a b B) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
    exact mem_image.mpr ⟨z.val, mem_map.mpr ⟨z,hz,rfl⟩, rfl⟩
  · intro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hy
    exact mem_map.mpr ⟨g • (show Mathieu22Points a b from z), mem_image.mpr ⟨z,hz,rfl⟩, rfl⟩

theorem mathieu22Blocks_preserved (a : Omega) (b : Mathieu23Points a) (g : Mathieu22PointModel a b)
    (B : Finset (Mathieu22Points a b)) (hB : B ∈ mathieu22Blocks a b) :
    mathieu22PermuteBlock a b g B ∈ mathieu22Blocks a b := by
  classical
  have hB := (Atlas.Combinatorics.derivedBlocks_mem (mathieu23Blocks a) b B).mp hB
  apply (Atlas.Combinatorics.derivedBlocks_mem (mathieu23Blocks a) b _).mpr
  change insert b (mathieu22BlockLift a b (mathieu22PermuteBlock a b g B)) ∈ mathieu23Blocks a
  rw [mathieu22BlockLift_permute]
  have h := mathieu23Blocks_preserved a g.val (insert b (mathieu22BlockLift a b B)) hB
  have hg : puncturedRestrictionPerm a g.val b = b := g.prop
  simpa [mathieu23PermuteBlock, hg] using h

end Atlas.Codes
