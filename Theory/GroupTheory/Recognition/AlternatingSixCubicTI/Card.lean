module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Numerical input for the cubic TI recognition

The source exercise starts with an actual `S₄` subgroup of index fifteen and
an elementary Sylow nine.  This file records the two order transfers used by
the later six-point construction.  No recognition by order is asserted here:
the final `A₆` identification uses the source rank-three graph.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2, printed p.249.
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI

open Subgroup

variable {G : Type*} [Group G]

/-- An actual `S₄` subgroup of index fifteen forces the ambient order 360. -/
theorem card_eq_360_of_s4_index15
    (H : Subgroup G) (eH : H ≃* Equiv.Perm (Fin 4))
    (hindex : H.index = 15) : Nat.card G = 360 := by
  have hH : Nat.card H = 24 := by
    rw [Nat.card_congr eH.toEquiv]
    simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have h := H.index_mul_card
  rw [hindex, hH] at h
  omega

/-- The quotient of a Sylow-nine normalizer has order four in the source model. -/
theorem normalizer_card_of_quotient_cyclic4
    (P : Sylow 3 G) (eN :
      (normalizer ((P : Subgroup G) : Set G) ⧸
        (P : Subgroup G).subgroupOf (normalizer ((P : Subgroup G) : Set G)))
        ≃* Multiplicative (ZMod 4)) :
    Nat.card (normalizer ((P : Subgroup G) : Set G) ⧸
      (P : Subgroup G).subgroupOf (normalizer ((P : Subgroup G) : Set G))) = 4 := by
  rw [Nat.card_congr eN.toEquiv]
  simp only [Nat.card_eq_fintype_card]
  decide

/-- The actual normalizer has order 36 when the Sylow subgroup has order nine. -/
theorem normalizer_card_eq_36_of_cyclic4
    (P : Sylow 3 G) (hP : Nat.card (P : Subgroup G) = 9)
    (eN :
      (normalizer ((P : Subgroup G) : Set G) ⧸
        (P : Subgroup G).subgroupOf (normalizer ((P : Subgroup G) : Set G)))
        ≃* Multiplicative (ZMod 4)) :
    Nat.card (normalizer ((P : Subgroup G) : Set G)) = 36 := by
  have hQ := normalizer_card_of_quotient_cyclic4 P eN
  -- The subgroup quotient has the same order as the Sylow subgroup.
  have hsub : Nat.card ((P : Subgroup G).subgroupOf
      (normalizer ((P : Subgroup G) : Set G))) = 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe P.le_normalizer).toEquiv]
    exact hP
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((P : Subgroup G).subgroupOf (normalizer ((P : Subgroup G) : Set G)))
  rw [hQ, hsub] at hcard
  norm_num at hcard ⊢
  exact hcard

end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
