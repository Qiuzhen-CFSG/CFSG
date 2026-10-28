/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu22Witt
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu21PointStabilizer
public import Theory.AtlasPort.OtherSporadic.Combinatorics.DerivedBlockEquivalence

/-!
# HeptadPairCounts

The number of heptads through a pair is computed by twice deriving the Witt design.
Explicit restriction and restoration identify the twice-derived blocks with the original
heptads through those two coordinates.

Source: `Atlas/Mathieu/HeptadPairCounts.lean`, Gerald Höhn (ATLAS), revision
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
local instance heptadPairPointsFintype (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _
local instance heptadPairComplementFintype (a : Omega) (b : Mathieu23Points a) : Fintype (Mathieu22Points a b) := Fintype.ofFinite _

theorem twice_derived_mathieu23Blocks_card (a : Omega) (b : Mathieu23Points a)
    (c : Mathieu22Points a b) : (derivedBlocks (mathieu22Blocks a b) c).card = 21 := by
  let D := derivedBlocks (mathieu22Blocks a b) c
  have hs : ∀ B ∈ D, B.card = 5 :=
    derivedBlocks_size _ c 5 (mathieu22Blocks_size a b)
  have hu : ∀ T : Finset (PointComplement c), T.card = 2 →
      ∃! B, B ∈ D ∧ T ⊆ B := derived_steiner _ c 2 (mathieu22_steiner a b)
  have h := steiner_block_count D 2 5 hs hu
  have hd : Fintype.card (PointComplement c) = 21 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (Mathieu21Points a b c) = 21
    exact mathieu21_degree a b c
  rw [hd] at h
  norm_num [Nat.choose] at h
  change D.card = 21
  omega

def twiceDerivedHeptadEquiv (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b) :
    {D // D ∈ derivedBlocks (mathieu22Blocks a b) c} ≃
      {B // B ∈ mathieu23Blocks a ∧ b ∈ B ∧ c.val ∈ B} := by
  let e := derivedBlocksThroughEquiv (mathieu23Blocks a) b
  let f := derivedBlocksThroughEquiv (mathieu22Blocks a b) c
  refine f.trans {
    toFun := fun D => ⟨(e ⟨D.val,D.prop.1⟩).val,(e ⟨D.val,D.prop.1⟩).prop.1,
      (e ⟨D.val,D.prop.1⟩).prop.2,?_⟩
    invFun := fun B => ⟨(e.symm ⟨B.val,B.prop.1,B.prop.2.1⟩).val,
      (e.symm ⟨B.val,B.prop.1,B.prop.2.1⟩).prop,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (derivedBlocksThroughEquiv_other_mem (mathieu23Blocks a) b c ⟨D.val,D.prop.1⟩).mpr D.prop.2
  · have h := B.prop.2.2
    have he := congrArg Subtype.val (e.apply_symm_apply ⟨B.val,B.prop.1,B.prop.2.1⟩)
    rw [← he] at h
    exact (derivedBlocksThroughEquiv_other_mem (mathieu23Blocks a) b c _).mp h
  · intro D
    apply Subtype.ext
    exact congrArg (fun z : {D // D ∈ mathieu22Blocks a b} => z.val) (e.symm_apply_apply ⟨D.val,D.prop.1⟩)
  · intro B
    apply Subtype.ext
    exact congrArg (fun z : {B // B ∈ mathieu23Blocks a ∧ b ∈ B} => z.val) (e.apply_symm_apply ⟨B.val,B.prop.1,B.prop.2.1⟩)

theorem mathieu23Blocks_through_pair_card (a : Omega) (b c : Mathieu23Points a) (hbc : b ≠ c) :
    (mathieu23Blocks a |>.filter (fun B => b ∈ B ∧ c ∈ B)).card = 21 := by
  let c' : Mathieu22Points a b := ⟨c,hbc.symm⟩
  have h := Nat.card_congr (twiceDerivedHeptadEquiv a b c')
  have e : {B // B ∈ mathieu23Blocks a ∧ b ∈ B ∧ c ∈ B} ≃
      {B // B ∈ (mathieu23Blocks a).filter (fun B => b ∈ B ∧ c ∈ B)} :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_coe,
    Fintype.card_coe,twice_derived_mathieu23Blocks_card] at h
  exact h.symm

end Atlas.Codes
