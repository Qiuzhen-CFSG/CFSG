module

import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Level4

/-!
# Star-group stabilizer transversal, level 5

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

def l5g0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 7, 20, 14, 16, 11, 23, 13, 21, 9, 5, 15, 17, 8, 6, 10, 18, 22, 12, 19]
  invFun := ![0, 1, 2, 3, 4, 14, 18, 5, 17, 13, 19, 9, 22, 11, 7, 15, 8, 16, 20, 23, 6, 12, 21, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def l5g1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 12, 15, 16, 19, 22, 21, 13, 6, 7, 14, 17, 8, 9, 18, 10, 23, 20, 11]
  invFun := ![0, 1, 2, 3, 4, 5, 13, 14, 17, 18, 20, 23, 6, 12, 15, 7, 8, 16, 19, 9, 22, 11, 10, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def l5g2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 11, 22, 12, 17, 6, 15, 21, 18, 14, 20, 19, 8, 16, 7, 10, 13, 5, 9, 23]
  invFun := ![0, 1, 2, 3, 4, 21, 9, 18, 16, 22, 19, 5, 7, 20, 13, 10, 17, 8, 12, 15, 14, 11, 6, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def gen5 : Fin 6 → Equiv.Perm (Fin 24) :=
  ![l5g0, l5g1, l5g2, (l5g0)⁻¹, (l5g1)⁻¹, (l5g2)⁻¹]

def genWords5 : Fin 6 → List (Fin 4) :=
  ![[0, 3, 3, 3, 3, 0, 1, 2, 1, 2], [2, 3, 2, 1, 0], [1, 0, 3, 3, 2, 3, 3], [0, 3, 0, 3, 2, 1, 1, 1, 1, 2], [2, 3, 0, 1, 0], [1, 1, 0, 1, 1, 2, 3]]

theorem gen5_eq_word : ∀ i, gen5 i = evalWord gen4 (genWords5 i) := by
  decide +kernel

theorem level5_le : generated gen5 ≤ generated gen4 := by
  apply generated_le
  intro i
  rw [gen5_eq_word]
  exact word_mem _ _ (gen_mem _) _

def repWords5 : Fin 16 → List (Fin 6) :=
  ![[], [0], [2], [3], [5], [1, 0], [2, 0], [5, 0], [0, 2], [3, 2], [4, 2], [2, 3], [0, 5], [2, 1, 0], [5, 1, 0], [4, 2, 0]]

def rep5 (i : Fin 16) : Equiv.Perm (Fin 24) := evalWord gen5 (repWords5 i)

theorem rep5_inj : Function.Injective (fun i => rep5 i (5 : Fin 24)) := by
  decide +kernel

theorem level5_fix : ∀ k : generated gen5, (k : Equiv.Perm (Fin 24)) 4 = 4 :=
  generated_fix gen5 4 (by decide +kernel)


end Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
