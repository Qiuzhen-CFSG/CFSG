/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.GolayPunctureAutomorphisms
public import Theory.AtlasPort.OtherSporadic.Combinatorics.SteinerCounting

/-!
# Mathieu23Witt

Removing a specified coordinate from the octads containing it gives the Steiner system
with parameters 4, 7, 23 and 253 blocks. Restriction and restoration transfer unique
completion and the coordinate-stabilizer action.

Source: `Atlas/Mathieu/Mathieu23Witt.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open Finset
local instance (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

def mathieu23BlockLift (a : Omega) (B : Finset (Mathieu23Points a)) : Finset Omega :=
  B.map (Function.Embedding.subtype _)

@[simp] theorem mathieu23BlockLift_not_mem (a : Omega) (B : Finset (Mathieu23Points a)) :
    a ∉ mathieu23BlockLift a B := by
  classical
  rintro h
  obtain ⟨x,_,hx⟩ := mem_map.mp h
  exact x.prop hx

@[simp] theorem mathieu23BlockLift_card (a : Omega) (B : Finset (Mathieu23Points a)) :
    (mathieu23BlockLift a B).card = B.card := card_map _

def mathieu23Blocks (a : Omega) : Finset (Finset (Mathieu23Points a)) := by
  classical
  exact univ.filter (fun B => insert a (mathieu23BlockLift a B) ∈ octads)

@[simp] theorem mathieu23Blocks_mem (a : Omega) (B : Finset (Mathieu23Points a)) :
    B ∈ mathieu23Blocks a ↔ insert a (mathieu23BlockLift a B) ∈ octads := by
  classical
  simp [mathieu23Blocks]

theorem mathieu23Blocks_size (a : Omega) (B : Finset (Mathieu23Points a))
    (hB : B ∈ mathieu23Blocks a) : B.card = 7 := by
  have h := octad_size _ ((mathieu23Blocks_mem a B).mp hB)
  simp only [card_insert_of_notMem (mathieu23BlockLift_not_mem a B), mathieu23BlockLift_card] at h
  omega

def mathieu23BlockRestrict (a : Omega) (O : Finset Omega) : Finset (Mathieu23Points a) := by
  classical
  exact O.subtype (fun x => x ∈ Mathieu23Points a)

theorem mathieu23Block_restore (a : Omega) (O : Finset Omega) (ha : a ∈ O) :
    insert a (mathieu23BlockLift a (mathieu23BlockRestrict a O)) = O := by
  classical
  ext x
  simp only [mathieu23BlockLift, mathieu23BlockRestrict, subtype_map, mem_insert, mem_filter,
    SubMulAction.mem_ofStabilizer_iff]
  constructor
  · rintro (rfl | ⟨hx,_⟩)
    · exact ha
    · exact hx
  · intro hx
    by_cases h : x = a
    · exact Or.inl h
    · exact Or.inr ⟨hx,h⟩

theorem mathieu23_steiner (a : Omega) (T : Finset (Mathieu23Points a)) (hT : T.card = 4) :
    ∃! B : Finset (Mathieu23Points a), B ∈ mathieu23Blocks a ∧ T ⊆ B := by
  classical
  obtain ⟨O,⟨hO,hTO⟩,huniq⟩ := octad_steiner (insert a (mathieu23BlockLift a T)) (by simp [hT])
  have ha : a ∈ O := hTO (mem_insert_self _ _)
  refine ⟨mathieu23BlockRestrict a O, ⟨?_,?_⟩,?_⟩
  · rw [mathieu23Blocks_mem, mathieu23Block_restore a O ha]
    exact hO
  · intro x hx
    change x ∈ O.subtype _
    rw [mem_subtype]
    exact hTO (mem_insert_of_mem (mem_map.mpr ⟨x,hx,rfl⟩))
  · intro B hB
    have he : insert a (mathieu23BlockLift a B) = O := huniq _
      ⟨(mathieu23Blocks_mem a B).mp hB.1, insert_subset_insert a (map_subset_map.mpr hB.2)⟩
    ext x
    have hh := congrArg (fun P : Finset Omega => x.val ∈ P) he
    have hx : x.val ≠ a := x.prop
    simpa [mathieu23BlockRestrict, mathieu23BlockLift, hx] using Iff.of_eq hh

theorem mathieu23Blocks_card (a : Omega) : (mathieu23Blocks a).card = 253 := by
  have h := Atlas.Combinatorics.steiner_block_count (mathieu23Blocks a) 4 7
    (mathieu23Blocks_size a) (mathieu23_steiner a)
  have hd : Fintype.card (Mathieu23Points a) = 23 := by
    rw [← Nat.card_eq_fintype_card, mathieu23_degree]
  rw [hd] at h
  norm_num [Nat.choose] at h
  omega


def mathieu23PermuteBlock (a : Omega) (g : Mathieu23PointModel a)
    (B : Finset (Mathieu23Points a)) : Finset (Mathieu23Points a) := by
  classical
  exact B.image (puncturedRestrictionPerm a g)

theorem mathieu23BlockLift_permute (a : Omega) (g : Mathieu23PointModel a)
    (B : Finset (Mathieu23Points a)) :
    mathieu23BlockLift a (mathieu23PermuteBlock a g B) = permuteBlock g.val.val (mathieu23BlockLift a B) := by
  classical
  simp only [mathieu23BlockLift, mathieu23PermuteBlock, permuteBlock, map_eq_image,
    image_image]
  rfl

theorem mathieu23Blocks_preserved (a : Omega) (g : Mathieu23PointModel a)
    (B : Finset (Mathieu23Points a)) (hB : B ∈ mathieu23Blocks a) :
    mathieu23PermuteBlock a g B ∈ mathieu23Blocks a := by
  classical
  rw [mathieu23Blocks_mem, mathieu23BlockLift_permute]
  have h := codePreserving_octad_forward g.val.val g.val.prop
    (insert a (mathieu23BlockLift a B)) ((mathieu23Blocks_mem a B).mp hB)
  have hg : g.val.val a = a := g.prop
  simpa [permuteBlock, hg] using h

end Atlas.Codes
