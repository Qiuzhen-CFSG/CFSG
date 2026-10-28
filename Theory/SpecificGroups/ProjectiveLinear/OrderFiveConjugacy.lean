module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# The order-five squaring obstruction in PGL₂

In characteristic different from five, an element of order five in PGL₂
cannot be conjugate to its square. For a matrix lift with trace t and
nonzero determinant d, its scalar fifth power forces
`t⁴ - 3t²d + d² = 0`. Projective conjugacy to its square forces
`t⁴ - 5t²d + 4d² = 0`. Together these imply `5d² = 0`.

This elementary matrix calculation supplies the order-five normalizer
obstruction in the exceptional PGL₂ overgroups used for Aschbacher--Smith,
E.1.14(6), printed p.214. It uses no subgroup classification.
-/

open Matrix
open scoped MatrixGroups
namespace Matrix.ProjGenLinGroup
variable {F : Type*} [Field F]

private theorem fifth_power_formula (A : Matrix (Fin 2) (Fin 2) F) :
    A ^ 5 = (A.trace ^ 4 - 3 * A.trace ^ 2 * A.det + A.det ^ 2) • A +
      (-A.trace ^ 3 * A.det + 2 * A.trace * A.det ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;> ring

private theorem trace_sq (A : Matrix (Fin 2) (Fin 2) F) :
    (A ^ 2).trace = A.trace ^ 2 - 2 * A.det := by
  simp [pow_two, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two]
  ring

private theorem fifth_coefficient_zero (A : GL (Fin 2) F)
    (hA : mk A ≠ 1) (hfive : mk A ^ 5 = 1) :
    (A : Matrix (Fin 2) (Fin 2) F).trace ^ 4 -
      3 * (A : Matrix (Fin 2) (Fin 2) F).trace ^ 2 * (A : Matrix (Fin 2) (Fin 2) F).det +
      (A : Matrix (Fin 2) (Fin 2) F).det ^ 2 = 0 := by
  let X : Matrix (Fin 2) (Fin 2) F := A
  let c := X.trace ^ 4 - 3 * X.trace ^ 2 * X.det + X.det ^ 2
  let b := -X.trace ^ 3 * X.det + 2 * X.trace * X.det ^ 2
  change c = 0
  by_contra hc
  have hm : mk (A ^ 5) = mk (1 : GL (Fin 2) F) := by simpa using hfive
  obtain ⟨u, hu⟩ := mk_eq_mk_iff.mp hm
  have hp : A ^ 5 = (GeneralLinearGroup.scalar (Fin 2) u)⁻¹ :=
    (mul_eq_one_iff_eq_inv).mp hu
  have hmat : X ^ 5 = (↑u⁻¹ : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have he := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hp
    simpa only [← map_inv, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using he
  rw [fifth_power_formula] at hmat
  have h01 : c * X 0 1 = 0 := by
    simpa [c, b] using congrArg (fun Y : Matrix (Fin 2) (Fin 2) F => Y 0 1) hmat
  have h10 : c * X 1 0 = 0 := by
    simpa [c, b] using congrArg (fun Y : Matrix (Fin 2) (Fin 2) F => Y 1 0) hmat
  have h00 : c * X 0 0 + b = ↑u⁻¹ := by
    simpa [c, b] using congrArg (fun Y : Matrix (Fin 2) (Fin 2) F => Y 0 0) hmat
  have h11 : c * X 1 1 + b = ↑u⁻¹ := by
    simpa [c, b] using congrArg (fun Y : Matrix (Fin 2) (Fin 2) F => Y 1 1) hmat
  have hx01 := (mul_eq_zero.mp h01).resolve_left hc
  have hx10 := (mul_eq_zero.mp h10).resolve_left hc
  have hxdiag : X 0 0 = X 1 1 := mul_left_cancel₀ hc (add_right_cancel (h00.trans h11.symm))
  apply hA
  rw [mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨X 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X, ← hxdiag, hx01, hx10]

/-- Projective conjugation cannot induce squaring on an order-five subgroup
in characteristic different from five. -/
public theorem not_conjugate_square_of_order_five (hfive : (5 : F) ≠ 0)
    (x y : PGL(Fin 2, F)) (hx : orderOf x = 5) :
    y * x * y⁻¹ ≠ x ^ 2 := by
  intro hxy
  obtain ⟨A, rfl⟩ := mk_surjective x
  obtain ⟨B, rfl⟩ := mk_surjective y
  have hA : mk A ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hx
    norm_num at hx
  have hA5 : mk A ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
  have hpoly5 := fifth_coefficient_zero A hA hA5
  have hm : mk (B * A * B⁻¹) = mk (A ^ 2) := by simpa using hxy
  obtain ⟨u, hu⟩ := mk_eq_mk_iff.mp hm
  let X : Matrix (Fin 2) (Fin 2) F := A
  let t := X.trace
  let d := X.det
  have hd : d ≠ 0 := A.det_ne_zero
  have hdet : d * (u : F) ^ 2 = d ^ 2 := by
    have he := congrArg (fun g : GL (Fin 2) F => (g.det : F)) hu
    simpa [map_mul, map_inv, map_pow, GeneralLinearGroup.det_scalar,
      mul_assoc, mul_left_comm, mul_comm, B.det_ne_zero, d, X] using he
  have hu2 : (u : F) ^ 2 = d := by
    apply mul_left_cancel₀ hd
    simpa [pow_two] using hdet
  have hmat : (u : F) • ((B : Matrix (Fin 2) (Fin 2) F) * X *
      ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) = X ^ 2 := by
    have he := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hu
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal] using he
  have htrace : (u : F) * t = t ^ 2 - 2 * d := by
    have he := congrArg Matrix.trace hmat
    simpa only [Matrix.trace_smul, Matrix.trace_units_conj, trace_sq, smul_eq_mul] using he
  have hpolySq : t ^ 4 - 5 * t ^ 2 * d + 4 * d ^ 2 = 0 := by
    have he := congrArg (fun z : F => z ^ 2) htrace
    rw [mul_pow, hu2] at he
    linear_combination -he
  change t ^ 4 - 3 * t ^ 2 * d + d ^ 2 = 0 at hpoly5
  have h2 : d * (2 * t ^ 2 - 3 * d) = 0 := by
    linear_combination hpoly5 - hpolySq
  have h2' : 2 * t ^ 2 - 3 * d = 0 := (mul_eq_zero.mp h2).resolve_left hd
  have he : (5 : F) * d ^ 2 = 0 := by
    linear_combination (2 * t ^ 2 - 3 * d) * h2' - 4 * hpoly5
  exact (mul_ne_zero hfive (pow_ne_zero 2 hd)) he
end Matrix.ProjGenLinGroup
