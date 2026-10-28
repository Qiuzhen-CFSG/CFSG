module

import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Level3

/-!
# Star-group stabilizer transversal, level 4

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

def l4g0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 16, 18, 9, 21, 4, 22, 11, 14, 15, 12, 10, 13, 8, 17, 20, 7, 5, 19, 6, 23]
  invFun := ![0, 1, 2, 3, 8, 20, 22, 19, 16, 6, 14, 10, 13, 15, 11, 12, 4, 17, 5, 21, 18, 7, 9, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def l4g1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 22, 11, 14, 19, 9, 5, 8, 10, 18, 4, 12, 20, 23, 6, 17, 13, 21, 16, 7, 15]
  invFun := ![0, 1, 2, 3, 13, 9, 17, 22, 10, 8, 11, 5, 14, 19, 6, 23, 21, 18, 12, 7, 15, 20, 4, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def gen4 : Fin 4 → Equiv.Perm (Fin 24) :=
  ![l4g0, l4g1, (l4g0)⁻¹, (l4g1)⁻¹]

def genWords4 : Fin 4 → List (Fin 4) :=
  ![[1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 0, 1, 2, 3, 0, 1, 0, 3], [1, 2, 3, 2, 1, 0, 0, 3, 2, 1, 0, 0, 3], [1, 2, 3, 2, 1, 0, 3, 2, 3, 3, 0, 0, 3, 3, 3, 0, 3, 0, 0, 3], [1, 2, 2, 3, 0, 1, 2, 2, 3, 0, 1, 0, 3]]

theorem gen4_eq_word : ∀ i, gen4 i = evalWord gen3 (genWords4 i) := by
  decide +kernel

theorem level4_le : generated gen4 ≤ generated gen3 := by
  apply generated_le
  intro i
  rw [gen4_eq_word]
  exact word_mem _ _ (gen_mem _) _

def repWords4 : Fin 20 → List (Fin 4) :=
  ![[], [0], [1], [2], [3], [1, 0], [3, 0], [0, 1], [1, 1], [2, 1], [3, 2], [0, 3], [2, 3], [3, 3], [3, 3, 0], [1, 0, 1], [3, 0, 1], [1, 2, 1], [0, 3, 2], [1, 0, 3]]

def rep4 (i : Fin 20) : Equiv.Perm (Fin 24) := evalWord gen4 (repWords4 i)

theorem rep4_inj : Function.Injective (fun i => rep4 i (4 : Fin 24)) := by
  decide +kernel

theorem level4_fix : ∀ k : generated gen4, (k : Equiv.Perm (Fin 24)) 3 = 3 :=
  generated_fix gen4 3 (by decide +kernel)


end Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
