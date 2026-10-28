/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Mathieu23

/-!
# Mathieu23Order

The degree-twenty-three action yields explicit index and tuple-stabilizer formulas.
Four-transitivity gives the point-stabilizer orders, and the obstruction to six-
transitivity of the ambient group excludes five-transitivity here.

Source: `Atlas/Mathieu/Mathieu23Order.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

/-- The actual orbit/coset identification, before taking cardinalities. -/
def mathieu23_orbitEquiv (a : Omega) :
    MulAction.orbit Mathieu24CodeModel a ≃ Mathieu24CodeModel ⧸ Mathieu23PointModel a :=
  MulAction.orbitEquivQuotientStabilizer Mathieu24CodeModel a

theorem mathieu23_index_product (a : Omega) :
    24 * Nat.card (Mathieu23PointModel a) = Nat.card Mathieu24CodeModel := by
  rw [mathieu23_order, mathieu24_order]

theorem mathieu23_order_factorization (a : Omega) :
    Nat.card (Mathieu23PointModel a) = 2^7 * 3^2 * 5 * 7 * 11 * 23 := by
  rw [mathieu23_order]
  norm_num

theorem mathieu23_not_five_transitive (a : Omega) :
    ¬ MulAction.IsMultiplyPretransitive (Mathieu23PointModel a) (Mathieu23Points a) 5 := by
  intro h
  have : MulAction.IsPretransitive Mathieu24CodeModel Omega :=
    ⟨golay_coordinate_transitive⟩
  exact mathieu24_not_six_transitive
    ((SubMulAction.ofStabilizer.isMultiplyPretransitive (a := a)).mpr h)

/-- Additional fixed tuples use the actual restricted action, not ambient setwise stabilizers. -/
def mathieu23TupleStabilizer (a : Omega) {k : ℕ} (e : Fin k ↪ Mathieu23Points a) :
    Subgroup (Mathieu23PointModel a) := fixingSubgroup _ (Set.range e)

theorem mathieu23TupleStabilizer_order_product (a : Omega) {k : ℕ}
    (e : Fin k ↪ Mathieu23Points a) (hk : k ≤ 4) :
    Nat.card (mathieu23TupleStabilizer a e) * ((23).choose k * k.factorial) = 10200960 := by
  have := mathieu23_four_transitive a
  have hn : (Set.range e).ncard = k := by
    rw [Set.ncard_range_of_injective e.injective]
    simp
  have ht : MulAction.IsMultiplyPretransitive (Mathieu23PointModel a) (Mathieu23Points a)
      (Set.range e).ncard := by
    rw [hn]
    apply MulAction.isMultiplyPretransitive_of_le hk
    rw [mathieu23_degree]
    omega
  have hi := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq (Set.range e) ht
  rw [hn, mathieu23_degree] at hi
  have he := (mathieu23TupleStabilizer a e).card_mul_index
  change (mathieu23TupleStabilizer a e).index = (23).choose k * k.factorial at hi
  rw [hi, mathieu23_order] at he
  exact he

theorem mathieu23_1_point_order (a : Omega) (e : Fin 1 ↪ Mathieu23Points a) :
    Nat.card (mathieu23TupleStabilizer a e) = 443520 := by
  have h := mathieu23TupleStabilizer_order_product a e (by decide)
  norm_num [Nat.choose, Nat.factorial] at h
  omega

theorem mathieu23_2_point_order (a : Omega) (e : Fin 2 ↪ Mathieu23Points a) :
    Nat.card (mathieu23TupleStabilizer a e) = 20160 := by
  have h := mathieu23TupleStabilizer_order_product a e (by decide)
  norm_num [Nat.choose, Nat.factorial] at h
  omega

theorem mathieu23_3_point_order (a : Omega) (e : Fin 3 ↪ Mathieu23Points a) :
    Nat.card (mathieu23TupleStabilizer a e) = 960 := by
  have h := mathieu23TupleStabilizer_order_product a e (by decide)
  norm_num [Nat.choose, Nat.factorial] at h
  omega

theorem mathieu23_4_point_order (a : Omega) (e : Fin 4 ↪ Mathieu23Points a) :
    Nat.card (mathieu23TupleStabilizer a e) = 48 := by
  have h := mathieu23TupleStabilizer_order_product a e (by decide)
  norm_num [Nat.choose, Nat.factorial] at h
  omega

end Atlas.Codes
