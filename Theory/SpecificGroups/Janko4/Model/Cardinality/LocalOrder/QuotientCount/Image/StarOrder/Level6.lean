module

import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Level5

/-!
# Star-group stabilizer transversal, level 6

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

def l6g0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 12, 15, 16, 19, 22, 21, 13, 6, 7, 14, 17, 8, 9, 18, 10, 23, 20, 11]
  invFun := ![0, 1, 2, 3, 4, 5, 13, 14, 17, 18, 20, 23, 6, 12, 15, 7, 8, 16, 19, 9, 22, 11, 10, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def gen6 : Fin 2 → Equiv.Perm (Fin 24) :=
  ![l6g0, (l6g0)⁻¹]

def genWords6 : Fin 2 → List (Fin 6) :=
  ![[1], [4]]

theorem gen6_eq_word : ∀ i, gen6 i = evalWord gen5 (genWords6 i) := by
  decide +kernel

theorem level6_le : generated gen6 ≤ generated gen5 := by
  apply generated_le
  intro i
  rw [gen6_eq_word]
  exact word_mem _ _ (gen_mem _) _

def repWords6 : Fin 3 → List (Fin 2) :=
  ![[], [0], [1]]

def rep6 (i : Fin 3) : Equiv.Perm (Fin 24) := evalWord gen6 (repWords6 i)

theorem rep6_inj : Function.Injective (fun i => rep6 i (6 : Fin 24)) := by
  decide +kernel

theorem level6_fix : ∀ k : generated gen6, (k : Equiv.Perm (Fin 24)) 5 = 5 :=
  generated_fix gen6 5 (by decide +kernel)

theorem level6_bound : 3 ≤ Nat.card (generated gen6) := by
  have h := card_mul_le (generated gen6) ⊥ bot_le rep6 6
    (fun i => word_mem _ _ (gen_mem _) _) rep6_inj
    (fun k => by have hk := k.property; simp only [Subgroup.mem_bot] at hk; simp [hk])
  simpa using h


end Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
