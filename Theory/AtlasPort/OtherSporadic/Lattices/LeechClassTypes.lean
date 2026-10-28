/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechClassTypes.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechCrossAction

/-!
The four mod-two class types and their cardinalities.
The saturated shell partition determines each type and its quadratic value.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def leechClassType (a : LeechModTwo) : ℕ :=
  if a = 0 then 0 else if a ∈ shellClasses 4 then 2 else if a ∈ shellClasses 6 then 3 else 4

theorem leechClass_partition (a : LeechModTwo) :
    a = 0 ∨ a ∈ shellClasses 4 ∨ a ∈ shellClasses 6 ∨ a ∈ shellClasses 8 := by
  have h : a ∈ shortClasses := by rw [shortClasses_eq_univ]; exact Finset.mem_univ _
  simpa only [shortClasses,Finset.mem_union,Finset.mem_singleton] using h

theorem leechClassType_fibers (a : LeechModTwo) :
    (leechClassType a = 0 ↔ a = 0) ∧
    (leechClassType a = 2 ↔ a ∈ shellClasses 4) ∧
    (leechClassType a = 3 ↔ a ∈ shellClasses 6) ∧
    (leechClassType a = 4 ↔ a ∈ shellClasses 8) := by
  have h04 := shellClasses_zero_not_mem 4 (by decide)
  have h06 := shellClasses_zero_not_mem 6 (by decide)
  have h08 := shellClasses_zero_not_mem 8 (by decide)
  have h46 : a ∈ shellClasses 4 → a ∈ shellClasses 6 → False :=
    fun h k => Finset.disjoint_left.mp (shellClasses_disjoint 4 6 (by decide) (by decide) (by decide)) h k
  have h48 : a ∈ shellClasses 4 → a ∈ shellClasses 8 → False :=
    fun h k => Finset.disjoint_left.mp (shellClasses_disjoint 4 8 (by decide) (by decide) (by decide)) h k
  have h68 : a ∈ shellClasses 6 → a ∈ shellClasses 8 → False :=
    fun h k => Finset.disjoint_left.mp (shellClasses_disjoint 6 8 (by decide) (by decide) (by decide)) h k
  rcases leechClass_partition a with rfl | h | h | h
  · simp [leechClassType,h04,h06,h08]
  · have h0 : a ≠ 0 := by intro he; subst a; exact h04 h
    have h6 : a ∉ shellClasses 6 := h46 h
    have h8 : a ∉ shellClasses 8 := h48 h
    simp [leechClassType,h0,h,h6,h8]
  · have h0 : a ≠ 0 := by intro he; subst a; exact h06 h
    have h4 : a ∉ shellClasses 4 := fun h4 => h46 h4 h
    have h8 : a ∉ shellClasses 8 := h68 h
    simp [leechClassType,h0,h,h4,h8]
  · have h0 : a ≠ 0 := by intro he; subst a; exact h08 h
    have h4 : a ∉ shellClasses 4 := fun h4 => h48 h4 h
    have h6 : a ∉ shellClasses 6 := fun h6 => h68 h6 h
    simp [leechClassType,h0,h,h4,h6]

theorem leechClassType_counts : Nat.card {a : LeechModTwo // leechClassType a = 0} = 1 ∧
    Nat.card {a : LeechModTwo // leechClassType a = 2} = 98280 ∧
    Nat.card {a : LeechModTwo // leechClassType a = 3} = 8386560 ∧
    Nat.card {a : LeechModTwo // leechClassType a = 4} = 8292375 := by
  constructor
  · rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => (leechClassType_fibers a).1))]
    simp [Nat.card_eq_fintype_card]
  constructor
  · rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => (leechClassType_fibers a).2.1)),
      Nat.card_eq_fintype_card,Fintype.card_coe,shellClasses_counts.1]
  constructor
  · rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => (leechClassType_fibers a).2.2.1)),
      Nat.card_eq_fintype_card,Fintype.card_coe,shellClasses_counts.2.1]
  · rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => (leechClassType_fibers a).2.2.2)),
      Nat.card_eq_fintype_card,Fintype.card_coe,shellClasses_counts.2.2]

theorem leechQuadratic_classType (a : LeechModTwo) : leechQuadratic a = (leechClassType a : Bit) := by
  rcases leechClass_partition a with rfl | h | h | h
  · simp [leechClassType,leechQuadratic_zero]
  · have ht := (leechClassType_fibers a).2.1.mpr h
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h
    have hn : leechHalfNorm x.val = 2 := by have h := leech_shell_halfNorm 4 x; omega
    rw [ht,← hx,leechQuadratic_reduce,hn]
    norm_num
  · have ht := (leechClassType_fibers a).2.2.1.mpr h
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h
    have hn : leechHalfNorm x.val = 3 := by have h := leech_shell_halfNorm 6 x; omega
    rw [ht,← hx,leechQuadratic_reduce,hn]
    norm_num
  · have ht := (leechClassType_fibers a).2.2.2.mpr h
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h
    have hn : leechHalfNorm x.val = 4 := by have h := leech_shell_halfNorm 8 x; omega
    rw [ht,← hx,leechQuadratic_reduce,hn]
    norm_num

end Atlas.Lattices
