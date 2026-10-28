/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/FiniteSuborbitPrimitivity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# FiniteSuborbitPrimitivity

Finite point-stabilizer suborbits control possible block sizes.
Each block is a union of suborbits, and divisibility excludes intermediate sizes.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/FiniteSuborbitPrimitivity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory
open scoped Pointwise BigOperators
open MulAction

/-- A finite partition into transitive point-stabilizer classes determines every block size. -/
theorem block_card_suborbit_sum {G X I : Type*} [Group G] [MulAction G X]
    [Finite X] [Fintype I] [DecidableEq I] (a : X) (f : X → I)
    (htrans : ∀ x y, f x = f y → ∃ g : stabilizer G a, g • x = y)
    (d : I → ℕ) (hd : ∀ i, Nat.card {x : X // f x = i} = d i)
    (B : Set X) (ha : a ∈ B) (hB : IsBlock G B) :
    ∃ T : Finset I, f a ∈ T ∧ Nat.card B = ∑ i ∈ T, d i := by
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
    · have he : IsEmpty {x : B // f x.val = i} := ⟨fun x => hi
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.val.val,x.val.prop,x.prop⟩)⟩
      let := he
      simp
  refine ⟨T,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,ha,rfl⟩,?_⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (fun x : B => f x.val)),Nat.card_sigma]
  simp_rw [hf]
  simp

/-- Primitivity from a finite suborbit partition and its divisibility obstruction. -/
theorem primitive_of_suborbit_sums {G X I : Type*} [Group G] [MulAction G X]
    [Finite X] [IsPretransitive G X] [Fintype I] [DecidableEq I]
    (a : X) (f : X → I)
    (htrans : ∀ x y, f x = f y → ∃ g : stabilizer G a, g • x = y)
    (d : I → ℕ) (hd : ∀ i, Nat.card {x : X // f x = i} = d i)
    (harith : ∀ T : Finset I, f a ∈ T → (∑ i ∈ T, d i) ∣ Nat.card X →
      (∑ i ∈ T, d i) = 1 ∨ (∑ i ∈ T, d i) = Nat.card X) :
    IsPreprimitive G X := by
  apply IsPreprimitive.of_isTrivialBlock_base a
  intro B ha hB
  obtain ⟨T,haT,hc⟩ := block_card_suborbit_sum a f htrans d hd B ha hB
  have hh : (∑ i ∈ T, d i) ∣ Nat.card X := hc ▸ hB.ncard_dvd_card ⟨a,ha⟩
  rcases harith T haT hh with he | he
  · left
    exact B.ncard_le_one_iff_subsingleton.mp (by change Nat.card B ≤ 1; omega)
  · right
    exact B.eq_univ_iff_ncard.mpr (by change Nat.card B = Nat.card X; omega)

end Atlas.GroupTheory
