module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/GroupTheory/FiniteSuborbitBlocks.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.OtherSporadic.GroupTheory.FiniteSuborbitPrimitivity

/-! A block through a base point is a union of point-stabilizer orbits, with cardinality equal to the sum of their sizes. -/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory
open MulAction
open scoped Pointwise

/-- A block through the base point is exactly a union of its stabilizer classes,
with the matching sum formula for its cardinality. -/
theorem block_suborbit_decomposition {G X I : Type*} [Group G] [MulAction G X]
    [Finite X] [Fintype I] [DecidableEq I] (a : X) (f : X → I)
    (htrans : ∀ x y, f x = f y → ∃ g : stabilizer G a, g • x = y)
    (d : I → ℕ) (hd : ∀ i, Nat.card {x : X // f x = i} = d i)
    (B : Set X) (ha : a ∈ B) (hB : IsBlock G B) :
    ∃ T : Finset I, f a ∈ T ∧ B = {x | f x ∈ T} ∧ Nat.card B = ∑ i ∈ T, d i := by
  classical
  let : Fintype X := Fintype.ofFinite _
  let T := Finset.univ.filter (fun i => ∃ x ∈ B, f x = i)
  have hs (i : I) (hi : i ∈ T) (y : X) (hy : f y = i) : y ∈ B := by
    obtain ⟨x,hx,hf⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨g,hg⟩ := htrans x y (hf.trans hy.symm)
    have hfix : g.val • B = B := hB.stabilizer_le ha g.prop
    rw [← hg]
    change g.val • x ∈ B
    rw [← hfix,Set.smul_mem_smul_set_iff]
    exact hx
  have hf (i : I) : Nat.card {x : B // f x.val = i} = if i ∈ T then d i else 0 := by
    split_ifs with hi
    · let e : {x : B // f x.val = i} ≃ {x : X // f x = i} :=
        { toFun := fun x => ⟨x.val.val,x.prop⟩
          invFun := fun x => ⟨⟨x.val,hs i hi x.val x.prop⟩,x.prop⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact (Nat.card_congr e).trans (hd i)
    · let : IsEmpty {x : B // f x.val = i} := ⟨fun x => hi
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.val.val,x.val.prop,x.prop⟩)⟩
      simp
  refine ⟨T,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,ha,rfl⟩,?_,?_⟩
  · ext x
    constructor
    · intro hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx,rfl⟩
    · intro hx
      exact hs (f x) hx x rfl
  · rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (fun x : B => f x.val)),Nat.card_sigma]
    simp_rw [hf]
    simp
end Atlas.GroupTheory
