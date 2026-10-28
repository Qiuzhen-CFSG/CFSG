module

import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Level0

/-!
# Star-group stabilizer transversal, level 1

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

def l1g0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 10, 20, 9, 17, 8, 23, 12, 1, 22, 6, 7, 18, 11, 5, 19, 3, 15, 2, 13, 4, 21, 14, 16]
  invFun := ![0, 8, 18, 16, 20, 14, 10, 11, 5, 3, 1, 13, 7, 19, 22, 17, 23, 4, 12, 15, 2, 21, 9, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def l1g1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 18, 12, 15, 10, 11, 8, 21, 3, 17, 22, 20, 5, 16, 14, 2, 7, 19, 6, 13, 1, 23, 9, 4]
  invFun := ![0, 20, 15, 8, 23, 12, 18, 16, 6, 22, 4, 5, 2, 19, 14, 3, 13, 9, 1, 17, 11, 7, 10, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def gen1 : Fin 4 → Equiv.Perm (Fin 24) :=
  ![l1g0, l1g1, (l1g0)⁻¹, (l1g1)⁻¹]

def genWords1 : Fin 4 → List (Fin 4) :=
  ![[3, 2, 3, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3], [3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 3, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 0, 3, 0, 3, 0, 1, 0], [1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1], [2, 3, 2, 1, 2, 1, 2, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 0, 3, 0, 1, 0, 3, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1]]

theorem gen1_eq_word : ∀ i, gen1 i = evalWord gen0 (genWords1 i) := by
  decide +kernel

theorem level1_le : generated gen1 ≤ generated gen0 := by
  apply generated_le
  intro i
  rw [gen1_eq_word]
  exact word_mem _ _ (gen_mem _) _

def repWords1 : Fin 23 → List (Fin 4) :=
  ![[], [0], [1], [2], [3], [0, 0], [1, 0], [3, 0], [0, 1], [2, 1], [1, 2], [2, 2], [3, 3], [0, 0, 0], [0, 1, 0], [1, 1, 0], [0, 3, 0], [3, 0, 1], [2, 2, 1], [2, 1, 2], [2, 3, 3], [3, 0, 0, 0], [1, 0, 3, 0]]

def rep1 (i : Fin 23) : Equiv.Perm (Fin 24) := evalWord gen1 (repWords1 i)

theorem rep1_inj : Function.Injective (fun i => rep1 i (1 : Fin 24)) := by
  decide +kernel

theorem level1_fix : ∀ k : generated gen1, (k : Equiv.Perm (Fin 24)) 0 = 0 :=
  generated_fix gen1 0 (by decide +kernel)


end Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
