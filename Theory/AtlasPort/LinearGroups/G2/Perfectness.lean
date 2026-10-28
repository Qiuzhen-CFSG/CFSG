module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/Perfectness.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
public import Theory.AtlasPort.LinearGroups.G2.TorusNormalization
public import Mathlib.GroupTheory.IsPerfect

/-! Torus commutators and long-root normal generation prove perfectness for fields of size greater than two. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
open scoped commutatorElement
variable {F : Type*} [Field F]

theorem rootA_neg (a : F) : rootA (-a) = (rootA a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [rootA_add,neg_add_cancel,rootA_zero]

theorem rootA_mem_commutator (t : F) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a:F) :
    rootA a ∈ commutator (Model F) := by
  let u : Fˣ := Units.mk0 t ht0
  have he : ⁅torus u 1,rootA (a/(t-1))⁆ = rootA a := by
    rw [commutatorElement_def,torus_rootA,← rootA_neg,rootA_add]
    congr 1
    change (t*1)*(a/(t-1)) + -(a/(t-1)) = a
    field_simp
    ring
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem isPerfect [Finite F] (hq : 2 < Nat.card F) : Group.IsPerfect (Model F) := by
  classical
  let := Fintype.ofFinite F
  have hc : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have ht' : t ≠ 0 ∧ t ≠ 1 := by simpa using ht
  constructor
  apply normal_eq_top_of_unipotent
  exact unipotent_le_normal_of_rootA _ (rootA_mem_commutator t ht'.1 ht'.2)
    t ht'.1 ht'.2
end Atlas.G2
