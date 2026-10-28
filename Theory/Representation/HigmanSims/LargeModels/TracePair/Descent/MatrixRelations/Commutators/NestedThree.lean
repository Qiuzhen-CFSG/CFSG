module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.Data
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.DirectRow895
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.Shared
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.NumericalSample
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.ABFourthSquare
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.ABSquare
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.Inner
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.InnerSquare
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.NestedThree.InnerCube
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared

/-!
# The checked degree-896 nested HS commutator cube

The inner word `A B⁴ A B⁴ A B A B` is `(A B⁴)² (A B)²`, in every monoid.
Consequently nine ordinary matrix-product checks suffice for its cube.
`nested_commutator_three_of_products` records that general reduction on the
fixed intermediate matrices.

The unconditional `nested_commutator_three` proves the full 42-letter identity
on all 896 coordinates. It combines the checked shared circuit with the two
mixed squares and the three formation and cube products. Their bounded
certificates use kernel-checked arithmetic and the streaming matrix semantics.

The existing shared circuit already owns the products needed to identify
`A B⁴` and `A B`. Its four relevant gates are connected in `Shared`.
`nested_commutator_three_of_shared_products` combines them with the five
remaining products, all discharged in the final export. No other commutator,
power relator, or long-word identity is assumed.

Source: `(a,b*a*b)^3` in the unchanged `Descent/source/HSG1-P1.M` and the
retained HSG1-f4r896aB0 matrices. See `NestedThree/source/README.md` for the
certificate contracts, source attribution and bounded measurements.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
open Certificates Commutators.NestedThree

/-- Exact factorization; no order or invertibility premise is needed. -/
theorem nested_commutator_factorization {G : Type*} [Monoid G] (a b : G) :
    positiveRelation a b 5 = ((a * b ^ 4) ^ 2 * (a * b) ^ 2) ^ 3 := by
  change (a * (b ^ 4 * a * b ^ 4) * a * (b * a * b)) ^ 3 = _
  simp only [pow_two, mul_assoc]

/-- Assemble the nine independently checkable products on the retained matrices. -/
theorem nested_commutator_three_of_products
    (hB2 : Packed.eval 896 generatorRowsB * Packed.eval 896 generatorRowsB =
      Packed.eval 896 rowsB2)
    (hB4 : Packed.eval 896 rowsB2 * Packed.eval 896 rowsB2 = Packed.eval 896 rowsB4)
    (hAB4 : Packed.eval 896 generatorRowsA * Packed.eval 896 rowsB4 = Packed.eval 896 rowsAB4)
    (hAB : Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB = Packed.eval 896 rowsAB)
    (hX2 : Packed.eval 896 rowsAB4 * Packed.eval 896 rowsAB4 = Packed.eval 896 rowsAB4Sq)
    (hY2 : Packed.eval 896 rowsAB * Packed.eval 896 rowsAB = Packed.eval 896 rowsABSq)
    (hC : Packed.eval 896 rowsAB4Sq * Packed.eval 896 rowsABSq = Packed.eval 896 rowsInner)
    (hC2 : Packed.eval 896 rowsInner * Packed.eval 896 rowsInner = Packed.eval 896 rowsInnerSq)
    (hC3 : Packed.eval 896 rowsInnerSq * Packed.eval 896 rowsInner = 1) :
    positiveRelation (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 5 = 1 := by
  have hb4 : (Packed.eval 896 generatorRowsB) ^ 4 = Packed.eval 896 rowsB4 := by
    calc
      _ = (Packed.eval 896 generatorRowsB * Packed.eval 896 generatorRowsB) *
          (Packed.eval 896 generatorRowsB * Packed.eval 896 generatorRowsB) := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = _ := by rw [hB2, hB4]
  rw [nested_commutator_factorization, hb4, hAB4, hAB, pow_two, pow_two,
    hX2, hY2, hC, pow_succ, pow_two, hC2, hC3]

/-- Reuse the existing shared-gate producer; five further products remain explicit. -/
theorem nested_commutator_three_of_shared_products
    (hshared : ∀ i : Fin 46, i.val < 17 → LongWords.ProductCheck i)
    (hX2 : Packed.eval 896 rowsAB4 * Packed.eval 896 rowsAB4 = Packed.eval 896 rowsAB4Sq)
    (hY2 : Packed.eval 896 rowsAB * Packed.eval 896 rowsAB = Packed.eval 896 rowsABSq)
    (hC : Packed.eval 896 rowsAB4Sq * Packed.eval 896 rowsABSq = Packed.eval 896 rowsInner)
    (hC2 : Packed.eval 896 rowsInner * Packed.eval 896 rowsInner = Packed.eval 896 rowsInnerSq)
    (hC3 : Packed.eval 896 rowsInnerSq * Packed.eval 896 rowsInner = 1) :
    positiveRelation (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 5 = 1 := by
  obtain ⟨hx, hy⟩ := mixed_products_of_shared_gates
    (hshared 0 (by decide)) (hshared 1 (by decide))
    (hshared 2 (by decide)) (hshared 6 (by decide))
  rw [nested_commutator_factorization, hx, hy, pow_two, pow_two,
    hX2, hY2, hC, pow_succ, pow_two, hC2, hC3]

/-- The exact positive nested commutator cube on the retained degree-896 matrices. -/
theorem nested_commutator_three :
    positiveRelation (Packed.eval 896 generatorRowsA) (Packed.eval 896 generatorRowsB) 5 = 1 :=
  nested_commutator_three_of_shared_products LongWords.shared_products
    a_b_fourth_square a_b_square inner_product inner_square inner_cube

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
