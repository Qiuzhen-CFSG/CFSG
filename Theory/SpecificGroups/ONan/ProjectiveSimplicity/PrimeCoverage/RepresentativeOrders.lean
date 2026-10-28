module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.Words
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeNormalGeneration.NineteenRelation
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.RepresentativeOrders.Five
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.RepresentativeOrders.ThirtyOne
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Exact orders of three O'Nan prime representatives

The representatives at indices 2, 6 and 7 in the preserved `ONG1-cycW1`
program have orders five, nineteen and thirty-one. Explicit matrices certify
the scalar powers of their linear lifts; nonzero off-diagonal entries exclude
projective identity. No ambient cardinality or simplicity is assumed.

Source and attribution: `refs/original/onan/README.md` and
`ProjectiveSimplicity/Words.lean`.
-/

namespace ONan.Simplicity

open RepresentativeOrderData

private theorem projective_ne_one_of_entry
    (g : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7))
    (i j : Fin 45) (hij : i ≠ j)
    (hentry : (g : Matrix (Fin 45) (Fin 45) (ZMod 7)) i j ≠ 0) :
    Matrix.ProjGenLinGroup.mk g ≠ 1 := by
  intro h
  have h' : Matrix.ProjGenLinGroup.mk (1 : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)) =
      Matrix.ProjGenLinGroup.mk g := h.symm
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h'
  have he := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7) =>
    (x : Matrix (Fin 45) (Fin 45) (ZMod 7)) i j) hu
  simp only [one_mul] at he
  change Matrix.scalar (Fin 45) (u : ZMod 7) i j = _ at he
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at he
  exact hentry he.symm

private def liftFive : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7) :=
  ((linearA * linearB) * ((linearA * linearB) * linearB)) ^ 4

private def liftThirtyOne : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7) :=
  ((linearA * linearB) * ((linearA * linearB) * ((linearA * linearB) * linearB))) *
    ((linearA * linearB) * linearB)

private theorem coe_five :
    (Subtype.val (primeRepresentative 2)) =
      Matrix.ProjGenLinGroup.mk liftFive := by
  change ((projectiveA * projectiveB) * ((projectiveA * projectiveB) * projectiveB)) ^ 4 = _
  simp only [liftFive, projectiveA, projectiveB, map_pow, map_mul]

private theorem coe_thirtyone :
    (Subtype.val (primeRepresentative 7)) =
      Matrix.ProjGenLinGroup.mk liftThirtyOne := by
  change ((projectiveA * projectiveB) * ((projectiveA * projectiveB) *
    ((projectiveA * projectiveB) * projectiveB))) * ((projectiveA * projectiveB) * projectiveB) = _
  simp only [liftThirtyOne, projectiveA, projectiveB, map_mul]

/-- The representative labelled 5A has order exactly five in the actual model. -/
public theorem orderOf_primeRepresentative_five : orderOf (primeRepresentative 2) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let u : (ZMod 7)ˣ := ⟨2, 4, by decide, by decide⟩
  have hlin : liftFive ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 45) u := by
    apply Units.ext
    change (((matrixA * matrixB) * ((matrixA * matrixB) * matrixB)) ^ 4) ^ 5 = _
    rw [matrix_five]
    exact five_pow
  have hp : primeRepresentative 2 ^ 5 = 1 := by
    apply Subtype.ext
    change (Subtype.val (primeRepresentative 2)) ^ 5 = 1
    rw [coe_five, ← map_pow, hlin, Matrix.ProjGenLinGroup.mk_scalar]
  apply orderOf_eq_prime hp
  intro h
  have he := congrArg (fun x : Model => Subtype.val x) h
  rw [coe_five] at he
  apply projective_ne_one_of_entry liftFive 0 2 (by decide) _ he
  change (((matrixA * matrixB) * ((matrixA * matrixB) * matrixB)) ^ 4) 0 2 ≠ 0
  rw [matrix_five]
  decide +kernel

/-- The representative labelled 19ABC has order exactly nineteen. -/
public theorem orderOf_primeRepresentative_nineteen : orderOf (primeRepresentative 6) = 19 := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  have heq : primeRepresentative 6 = generatorA * generatorB ^ 2 := by
    change (generatorA * generatorB) * generatorB = _
    rw [pow_two, mul_assoc]
  rw [heq]
  apply orderOf_eq_prime generatorAB2_pow_nineteen
  intro h
  have ha : generatorA = (generatorB ^ 2)⁻¹ := (eq_inv_iff_mul_eq_one).mpr h
  apply generatorA_mul_generatorB_ne
  rw [ha]
  exact ((Commute.refl generatorB).pow_left 2).inv_left.eq

/-- The representative labelled 31AB has order exactly thirty-one. -/
public theorem orderOf_primeRepresentative_thirtyone : orderOf (primeRepresentative 7) = 31 := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  have hlin : liftThirtyOne ^ 31 = 1 := by
    apply Units.ext
    change (((matrixA * matrixB) * ((matrixA * matrixB) * ((matrixA * matrixB) * matrixB))) *
      ((matrixA * matrixB) * matrixB)) ^ 31 = 1
    rw [matrix_thirtyone]
    exact thirtyone_pow
  have hp : primeRepresentative 7 ^ 31 = 1 := by
    apply Subtype.ext
    change (Subtype.val (primeRepresentative 7)) ^ 31 = 1
    rw [coe_thirtyone, ← map_pow, hlin, map_one]
  apply orderOf_eq_prime hp
  intro h
  have he := congrArg (fun x : Model => Subtype.val x) h
  rw [coe_thirtyone] at he
  apply projective_ne_one_of_entry liftThirtyOne 0 1 (by decide) _ he
  change (((matrixA * matrixB) * ((matrixA * matrixB) * ((matrixA * matrixB) * matrixB))) *
      ((matrixA * matrixB) * matrixB)) 0 1 ≠ 0
  rw [matrix_thirtyone]
  decide +kernel

end ONan.Simplicity
