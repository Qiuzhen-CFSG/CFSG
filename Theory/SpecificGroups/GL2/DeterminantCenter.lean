module
public import Theory.SpecificGroups.GL2.SubgroupCenter
public import Theory.SpecificGroups.GL2.DeterminantTwoPower
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Exact scalar-root centers of determinant levels

For any field F and natural m, the center of the actual determinant
level m, mapped into GL2(F), is exactly the scalar image of the
2^(m+1)-st roots of unity. This subgroup identity requires no finite-field,
oddness, or cardinal-divisibility hypothesis.

Every level contains the two elementary determinant-one transvections
with off-diagonal coefficient one. Their products have different upper
left entries, so the level is noncommutative in every characteristic.
The proved subgroup-center theorem therefore identifies its center with
the scalar matrices it contains. Since the determinant of scalar c is
c squared, the level condition is precisely c^(2^(m+1))=1.

The noncommutativity helper is public for the actual unitary-center
consumer via the proved SU2--SL2 equivalence. Source: ABG II.2 Lemma 1(v)
and II.3 Proposition 3, article page 26; this equality identifies the
exact central scalar kernel in the source model comparison. Cardinalities
under the source divisibility bounds are proved separately.
-/

namespace Matrix.GeneralLinearGroup

public theorem determinantTwoPower_not_isMulCommutative
    (F : Type*) [Field F] (m : ℕ) : ¬ IsMulCommutative (determinantTwoPower F m) := by
  intro h
  let A : determinantTwoPower F m :=
    ⟨Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : F)), by
      simp only [mem_determinantTwoPower, Matrix.SpecialLinearGroup.coeToGL_det, one_pow]⟩
  let B : determinantTwoPower F m :=
    ⟨Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (1 : F)), by
      simp only [mem_determinantTwoPower, Matrix.SpecialLinearGroup.coeToGL_det, one_pow]⟩
  have hx := congrArg (fun g : determinantTwoPower F m => g.val.val 0 0)
    ((isMulCommutative_iff.mp h) A B)
  change (Matrix.transvection (0 : Fin 2) 1 (1 : F) *
    Matrix.transvection (1 : Fin 2) 0 (1 : F)) 0 0 =
    (Matrix.transvection (1 : Fin 2) 0 (1 : F) *
    Matrix.transvection (0 : Fin 2) 1 (1 : F)) 0 0 at hx
  simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at hx

public theorem center_determinantTwoPower_map
    (F : Type*) [Field F] (m : ℕ) :
    (Subgroup.center (determinantTwoPower F m)).map (determinantTwoPower F m).subtype =
      (rootsOfUnity (2 ^ (m + 1)) F).map (scalar (Fin 2)) := by
  rw [center_map_eq_inf_scalar_of_noncommutative _
    (determinantTwoPower_not_isMulCommutative F m)]
  ext A
  constructor
  · rintro ⟨hA, u, rfl⟩
    refine ⟨u, ?_, rfl⟩
    change u ^ (2 ^ (m + 1)) = 1
    have h := (mem_determinantTwoPower m _).mp hA
    rw [det_scalar, Fintype.card_fin] at h
    rw [pow_succ', pow_mul]
    exact h
  · rintro ⟨u, hu, rfl⟩
    refine ⟨?_, ⟨u, rfl⟩⟩
    change det (scalar (Fin 2) u) ^ (2 ^ m) = 1
    rw [det_scalar, Fintype.card_fin, ← pow_mul, ← pow_succ']
    exact hu

end Matrix.GeneralLinearGroup

