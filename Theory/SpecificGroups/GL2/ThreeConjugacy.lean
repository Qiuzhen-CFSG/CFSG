module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic

/-!
# The eight actual conjugacy classes of GL2 over the field with three elements

The representatives are 1,t,a²,r,rt,b,a,a⁻¹, where t is the scalar -I,
a is the companion matrix of X²-X-1, r is the upper unipotent, and b is
diagonal with entries 1,-1. Every element is conjugate to exactly one of
these representatives. Their element orders and centralizer cardinalities
are computed, and the five classes consisting of cyclic roots of t are
identified. The explicit representatives are public data for the ensuing
ordinary-character table; no abstract replacement group is introduced.

The finite calculations run on the 81 two-by-two matrices over ZMod3 and
are checked by Lean's kernel. Coverage supplies an actual invertible
conjugating matrix. Uniqueness tests the same matrix conjugation equation.
The centralizer calculation is transferred by an explicit equivalence from
its invertible matrices to the actual subgroup of GL2. Finite power checks
give the element orders, and the standard finite cyclic-subgroup API gives
the exact root support. These are intrinsic matrix facts, not a recognition
theorem inferred from group order or character data.

Source: W. J. Wong, On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2, J. Austral. Math. Soc.4 (1964),90–112, the GL2(3)
example at article94 and Table1 at article97. The representative b is chosen
as a diagonal involution in the same noncentral involution class. The same
column order is retained. DOI:10.1017/S1446788700022771.
-/

open Matrix
namespace Matrix.GeneralLinearGroup
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 3)
private abbrev G := GL (Fin 2) (ZMod 3)

/-- The companion matrix of X²-X-1, of order eight. -/
@[expose] public def threeRotation : GL (Fin 2) (ZMod 3) :=
  mkOfDetNeZero !![(0 : ZMod 3),1;1,1] (by decide)
/-- The upper unipotent representative of order three. -/
@[expose] public def threeUnipotent : GL (Fin 2) (ZMod 3) :=
  mkOfDetNeZero !![(1 : ZMod 3),1;0,1] (by decide)
/-- A noncentral diagonal involution. -/
@[expose] public def threeReflection : GL (Fin 2) (ZMod 3) :=
  mkOfDetNeZero !![(1 : ZMod 3),0;0,-1] (by decide)
/-- The scalar involution -I. -/
@[expose] public def threeCentral : GL (Fin 2) (ZMod 3) :=
  mkOfDetNeZero !![(-1 : ZMod 3),0;0,-1] (by decide)
/-- The eight representatives in Wong Table1 column order. -/
@[expose] public def threeClassRepr : Fin 8 → GL (Fin 2) (ZMod 3) :=
  ![1, threeCentral, threeRotation^2, threeUnipotent,
    threeUnipotent*threeCentral, threeReflection, threeRotation, threeRotation⁻¹]

private theorem matrix_class_coverage : ∀ A : M, A.det ≠ 0 →
    ∃ i : Fin 8, ∃ B : M, B.det ≠ 0 ∧ B * A = (threeClassRepr i).val * B := by
  decide +kernel

private theorem matrix_class_unique : ∀ i j : Fin 8, ∀ B : M, B.det ≠ 0 →
    B * (threeClassRepr i).val = (threeClassRepr j).val * B → i = j := by
  decide +kernel

private theorem matrix_centralizer_card : ∀ i : Fin 8,
    (Finset.univ.filter (fun B : M =>
      B.det ≠ 0 ∧ B * (threeClassRepr i).val = (threeClassRepr i).val * B)).card =
      ![48,48,8,6,6,4,8,8] i := by
  decide +kernel

private theorem matrix_orders : ∀ i : Fin 8,
    let n := ![1,2,4,3,6,2,8,8] i
    0 < n ∧ threeClassRepr i ^ n = 1 ∧
      ∀ m : Fin n, 0 < m.val → threeClassRepr i ^ m.val ≠ 1 := by
  decide +kernel

private theorem class_orders (i : Fin 8) :
    orderOf (threeClassRepr i) = ![1,2,4,3,6,2,8,8] i := by
  have h := matrix_orders i
  exact (orderOf_eq_iff h.1).mpr ⟨h.2.1, fun m hm hpos => h.2.2 ⟨m, hm⟩ hpos⟩

private def centralizerMatrixEquiv (i : Fin 8) :
    Subgroup.centralizer ({threeClassRepr i} : Set G) ≃
      {B : M // B.det ≠ 0 ∧ B * (threeClassRepr i).val = (threeClassRepr i).val * B} where
  toFun b := ⟨b.val.val, Units.ne_zero (det b.val),
    congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.mp b.property)⟩
  invFun B := ⟨mkOfDetNeZero B.val B.property.1,
    Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext B.property.2)⟩
  left_inv _b := Subtype.ext (Units.ext rfl)
  right_inv _B := Subtype.ext rfl

/-- Complete conjugacy, element-order, centralizer-cardinality, and root-support data. -/
public theorem three_conjugacy_data :
    (∀ x : GL (Fin 2) (ZMod 3), ∃! i : Fin 8, IsConj x (threeClassRepr i)) ∧
    (∀ i : Fin 8, orderOf (threeClassRepr i) = ![1,2,4,3,6,2,8,8] i) ∧
    (∀ i : Fin 8, Nat.card (Subgroup.centralizer ({threeClassRepr i} : Set (GL (Fin 2) (ZMod 3)))) =
      ![48,48,8,6,6,4,8,8] i) ∧
    (∀ i : Fin 8, threeCentral ∈ Subgroup.zpowers (threeClassRepr i) ↔
      i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 7) := by
  refine ⟨?_, class_orders, ?_, ?_⟩
  · intro x
    obtain ⟨i, B, hB, hBx⟩ := matrix_class_coverage x.val (Units.ne_zero (det x))
    have hi : IsConj x (threeClassRepr i) := by
      let b := mkOfDetNeZero B hB
      have hmul : b * x = threeClassRepr i * b := Units.ext hBx
      apply isConj_iff.mpr
      refine ⟨b, ?_⟩
      rw [hmul, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨i, hi, ?_⟩
    intro j hj
    obtain ⟨b, hb⟩ := isConj_iff.mp (hi.symm.trans hj)
    have hmul : b * threeClassRepr i = threeClassRepr j * b := by
      have h := congrArg (fun a => a * b) hb
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
    exact (matrix_class_unique i j b.val (Units.ne_zero (det b)) (congrArg Units.val hmul)).symm
  · intro i
    rw [Nat.card_congr (centralizerMatrixEquiv i), Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact matrix_centralizer_card i
  · intro i
    rw [mem_zpowers_iff_mem_range_orderOf, class_orders]
    fin_cases i <;> decide +kernel

end Matrix.GeneralLinearGroup
