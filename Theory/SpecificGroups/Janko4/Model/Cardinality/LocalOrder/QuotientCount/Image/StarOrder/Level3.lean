module

import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Level2

/-!
# Star-group stabilizer transversal, level 3

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

def l3g0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 14, 7, 18, 16, 8, 15, 13, 23, 6, 21, 17, 9, 20, 5, 3, 11, 19, 4, 10, 12, 22]
  invFun := ![0, 1, 2, 17, 20, 16, 11, 4, 7, 14, 21, 18, 22, 9, 3, 8, 6, 13, 5, 19, 15, 12, 23, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def l3g1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 15, 21, 4, 5, 11, 23, 3, 19, 10, 8, 18, 9, 13, 20, 16, 22, 12, 6, 17, 14, 7]
  invFun := ![0, 1, 2, 9, 5, 6, 20, 23, 12, 14, 11, 7, 19, 15, 22, 3, 17, 21, 13, 10, 16, 4, 18, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def gen3 : Fin 4 → Equiv.Perm (Fin 24) :=
  ![l3g0, l3g1, (l3g0)⁻¹, (l3g1)⁻¹]

def genWords3 : Fin 4 → List (Fin 4) :=
  ![[1], [2, 3, 2, 2, 1, 1, 0, 0, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 3, 0, 3, 3], [3], [1, 1, 2, 1, 0, 3, 2, 3, 0, 3, 0, 3, 2, 3, 2, 2, 2, 3, 3, 0, 0, 1, 0]]

theorem gen3_eq_word : ∀ i, gen3 i = evalWord gen2 (genWords3 i) := by
  decide +kernel

theorem level3_le : generated gen3 ≤ generated gen2 := by
  apply generated_le
  intro i
  rw [gen3_eq_word]
  exact word_mem _ _ (gen_mem _) _

def repWords3 : Fin 21 → List (Fin 4) :=
  ![[], [0], [1], [2], [3], [3, 0], [0, 1], [1, 1], [2, 1], [1, 2], [3, 2], [0, 3, 0], [2, 3, 0], [3, 3, 0], [0, 0, 1], [1, 0, 1], [2, 2, 1], [0, 1, 2], [0, 3, 2], [3, 0, 3, 0], [0, 3, 3, 0]]

def rep3 (i : Fin 21) : Equiv.Perm (Fin 24) := evalWord gen3 (repWords3 i)

theorem rep3_inj : Function.Injective (fun i => rep3 i (3 : Fin 24)) := by
  decide +kernel

theorem level3_fix : ∀ k : generated gen3, (k : Equiv.Perm (Fin 24)) 2 = 2 :=
  generated_fix gen3 2 (by decide +kernel)


end Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
