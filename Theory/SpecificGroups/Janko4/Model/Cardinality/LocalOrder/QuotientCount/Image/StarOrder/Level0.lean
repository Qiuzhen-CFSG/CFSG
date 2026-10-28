module

import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarData

/-!
# Star-group stabilizer transversal, level 0

The explicit permutations and words were discovered by GAP stabilizers.
Every inverse table, word identity, fixed point and distinct orbit image is
checked by the Lean kernel. Only a lower bound is claimed; no external
stabilizer generation or order computation is trusted.
See `source/generate.py` for the certificate generator.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

@[expose] public section
namespace Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
open Theory.GroupTheory

def l0g0 : Equiv.Perm (Fin 24) where
  toFun := ![2, 3, 0, 1, 6, 7, 4, 5, 9, 8, 12, 13, 10, 11, 15, 14, 22, 23, 19, 18, 21, 20, 16, 17]
  invFun := ![2, 3, 0, 1, 6, 7, 4, 5, 9, 8, 12, 13, 10, 11, 15, 14, 22, 23, 19, 18, 21, 20, 16, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def l0g1 : Equiv.Perm (Fin 24) where
  toFun := ![3, 2, 4, 5, 1, 0, 10, 11, 6, 7, 8, 9, 22, 20, 23, 21, 12, 13, 14, 15, 17, 19, 16, 18]
  invFun := ![5, 4, 1, 0, 2, 3, 8, 9, 10, 11, 6, 7, 16, 17, 18, 19, 22, 20, 23, 21, 13, 15, 12, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def gen0 : Fin 4 → Equiv.Perm (Fin 24) :=
  ![l0g0, l0g1, (l0g0)⁻¹, (l0g1)⁻¹]

theorem gen0_eq : gen0 = ![starX, starY, starX⁻¹, starY⁻¹] := by
  decide +kernel

theorem level0_le : generated gen0 ≤ StarGroup := by
  have hx : starX ∈ StarGroup := Subgroup.subset_closure (by simp)
  have hy : starY ∈ StarGroup := Subgroup.subset_closure (by simp)
  apply generated_le
  intro i
  rw [gen0_eq]
  fin_cases i
  · exact hx
  · exact hy
  · exact StarGroup.inv_mem hx
  · exact StarGroup.inv_mem hy

def repWords0 : Fin 24 → List (Fin 4) :=
  ![[], [0], [1], [3], [1, 0], [3, 0], [0, 3], [0, 1, 0], [1, 0, 3], [3, 0, 3], [1, 0, 1, 0], [3, 0, 1, 0], [0, 1, 0, 3], [0, 1, 0, 1, 0], [1, 0, 1, 0, 3], [3, 0, 1, 0, 3], [1, 0, 1, 0, 1, 0], [3, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0, 3], [0, 3, 0, 1, 0, 3], [1, 0, 1, 0, 1, 0, 3], [3, 0, 1, 0, 1, 0, 3], [1, 0, 3, 0, 1, 0, 3], [3, 0, 3, 0, 1, 0, 3]]

def rep0 (i : Fin 24) : Equiv.Perm (Fin 24) := evalWord gen0 (repWords0 i)

theorem rep0_inj : Function.Injective (fun i => rep0 i (0 : Fin 24)) := by
  decide +kernel


end Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
