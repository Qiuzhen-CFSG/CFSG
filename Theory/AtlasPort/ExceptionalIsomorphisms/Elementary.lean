module

/-
Adapted from Atlas/LinearGroups/Elementary.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic.Abel
set_option warningAsError false

@[expose] public section


/-! # Elementary generation and perfectness -/

namespace Atlas
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups commutatorElement

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

theorem elementary_mul {i j : ι} (hij : i ≠ j) (a b : F) :
    transvection hij a * transvection hij b = transvection hij (a + b) :=
  (transvection_add hij a b).symm

theorem elementary_inv {i j : ι} (hij : i ≠ j) (a : F) :
    (transvection hij a)⁻¹ = transvection hij (-a) := transvection_inv hij a

theorem elementary_det {i j : ι} (hij : i ≠ j) (a : F) :
    Matrix.det (transvection hij a : Matrix ι ι F) = 1 := (transvection hij a).prop

theorem diagonal_elementary_decomposition {i j : ι} (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    diag2n hij a ha = transvection hij a * transvection hij.symm (-a⁻¹) *
      transvection hij a * transvection hij (-1) * transvection hij.symm 1 *
        transvection hij (-1) := by
  apply Subtype.ext
  simp only [coe_mul, transvection_coe]
  simp only [mul_add, add_mul, one_mul, mul_one, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hij, single_mul_single_of_ne _ _ _ _ hij.symm,
    add_zero]
  ext k l
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp [diag2n_coe, diagonal_apply, single_apply, one_apply, hki, hkj, hli, hlj,
      hij, hij.symm, ha, eq_comm]
  all_goals grind

theorem sl_elementary_induction [Nontrivial ι] (P : SpecialLinearGroup ι F → Prop)
    (ht : ∀ (i j : ι) (hij : i ≠ j) (a : F), P (transvection hij a))
    (hm : ∀ a b, P a → P b → P (a * b)) (g : SpecialLinearGroup ι F) : P g := by
  apply diagonal_transvection_induction' P g _ ht hm
  intro i j hij a ha
  rw [diagonal_elementary_decomposition hij a ha]
  repeat' apply hm
  all_goals exact ht _ _ _ _

def elementaryGenerators : Set (SpecialLinearGroup ι F) :=
  {g | ∃ (i j : ι) (hij : i ≠ j) (a : F), g = transvection hij a}

theorem sl_elementary_generation [Nontrivial ι] :
    Subgroup.closure (elementaryGenerators (ι := ι) (F := F)) = ⊤ := by
  apply top_unique
  intro g _
  exact sl_elementary_induction
    (fun g ↦ g ∈ Subgroup.closure (elementaryGenerators (ι := ι) (F := F)))
    (fun i j hij a ↦ Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩)
    (fun _ _ ↦ Subgroup.mul_mem _) g

def projectiveElementaryGenerators : Set (ProjectiveSpecialLinearGroup ι F) :=
  (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup ι F))) '' elementaryGenerators

theorem psl_elementary_generation [Nontrivial ι] :
    Subgroup.closure (projectiveElementaryGenerators (ι := ι) (F := F)) = ⊤ := by
  rw [projectiveElementaryGenerators, ← MonoidHom.map_closure, sl_elementary_generation]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem elementary_commutator {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (a b : F) : ⁅transvection hik a, transvection hkj b⁆ = transvection hij (a * b) := by
  rw [commutatorElement_def, transvection_inv, transvection_inv]
  apply Subtype.ext
  simp only [coe_mul, transvection_coe]
  simp [mul_add, add_mul, single_mul_single_of_ne _ _ _ _ hij.symm,
    single_mul_single_of_ne _ _ _ _ hik.symm, single_mul_single_of_ne _ _ _ _ hkj.symm,
    ← single_neg]
  abel

theorem sl_perfect (n : ℕ) (hn : 3 ≤ n) : Group.IsPerfect (SL(n, F)) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  constructor
  apply top_unique
  intro g _
  apply sl_elementary_induction (fun g ↦ g ∈ commutator SL(n, F)) _
    (fun _ _ ↦ Subgroup.mul_mem _) g
  intro i j hij a
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  rw [← mul_one a, ← elementary_commutator hij hki.symm hkj a 1]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem psl_perfect (n : ℕ) (hn : 3 ≤ n) : Group.IsPerfect (PSL(n, F)) := by
  let := sl_perfect (F := F) n hn
  infer_instance

end Atlas
