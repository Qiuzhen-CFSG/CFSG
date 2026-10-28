module

import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Level1

/-!
# Star-group stabilizer transversal, level 2

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

def l2g0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 19, 20, 11, 10, 4, 18, 2, 8, 21, 17, 14, 9, 23, 6, 12, 3, 13, 16, 5, 22, 15, 7]
  invFun := ![0, 1, 8, 17, 6, 20, 15, 23, 9, 13, 5, 4, 16, 18, 12, 22, 19, 11, 7, 2, 3, 10, 21, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def l2g1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 14, 7, 18, 16, 8, 15, 13, 23, 6, 21, 17, 9, 20, 5, 3, 11, 19, 4, 10, 12, 22]
  invFun := ![0, 1, 2, 17, 20, 16, 11, 4, 7, 14, 21, 18, 22, 9, 3, 8, 6, 13, 5, 19, 15, 12, 23, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def gen2 : Fin 4 → Equiv.Perm (Fin 24) :=
  ![l2g0, l2g1, (l2g0)⁻¹, (l2g1)⁻¹]

def genWords2 : Fin 4 → List (Fin 4) :=
  ![[0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 2, 1, 0, 0, 0, 1, 2, 3, 2, 1, 2, 1, 1, 1, 0, 0, 1, 2, 1, 2, 2, 1], [3, 0, 3, 2, 1, 0, 3, 0, 3, 2, 3, 0, 0, 0, 3, 3, 0, 0, 3, 0, 0, 0, 1, 0, 3, 3, 0, 0, 0, 1, 1, 0, 1, 1, 2, 2, 3, 3, 3, 0, 0, 3, 0, 3, 2, 2, 3], [3, 0, 0, 3, 0, 3, 2, 2, 3, 3, 3, 0, 3, 0, 1, 0, 3, 2, 2, 2, 3, 0, 3, 2, 3, 2, 2, 3, 3, 3, 2, 2], [1, 0, 0, 1, 2, 1, 2, 2, 1, 1, 1, 0, 0, 3, 3, 2, 3, 3, 2, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 1, 2, 2, 2, 1, 0, 1, 2, 1, 2, 3, 0, 1, 2, 1]]

theorem gen2_eq_word : ∀ i, gen2 i = evalWord gen1 (genWords2 i) := by
  decide +kernel

theorem level2_le : generated gen2 ≤ generated gen1 := by
  apply generated_le
  intro i
  rw [gen2_eq_word]
  exact word_mem _ _ (gen_mem _) _

def repWords2 : Fin 22 → List (Fin 4) :=
  ![[], [0], [2], [0, 0], [1, 2], [2, 2], [3, 2], [0, 0, 0], [1, 0, 0], [3, 0, 0], [1, 1, 2], [2, 1, 2], [1, 2, 2], [3, 2, 2], [0, 3, 2], [2, 3, 2], [3, 3, 2], [1, 0, 0, 0], [0, 1, 0, 0], [3, 3, 0, 0], [2, 1, 1, 2], [1, 1, 2, 2]]

def rep2 (i : Fin 22) : Equiv.Perm (Fin 24) := evalWord gen2 (repWords2 i)

theorem rep2_inj : Function.Injective (fun i => rep2 i (2 : Fin 24)) := by
  decide +kernel

theorem level2_fix : ∀ k : generated gen2, (k : Equiv.Perm (Fin 24)) 1 = 1 :=
  generated_fix gen2 1 (by decide +kernel)


end Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
