module

public import Theory.FieldTheory.CubicQuadraticUnitAction
public import Theory.SpecificGroups.SU3.BorelTorus.Basic

/-!
# Quadratic coefficient action on the projective unitary torus

A coefficient automorphism acting quadratically on the standard projective
Hermitian torus is identity when the matrix field has order `2^(2*n)`,
`n ≥ 2`. The literal torus kernel consists of norm-one cube roots of unity;
thus its double multiplicative displacement has cube one, exactly the
hypothesis of the finite-field rigidity theorem.

Source: Aschbacher–Smith, F.1.3(5), printed p.260. The small field of order
four and transport to arbitrary Cartan pairs belong to the source assembly.
-/

public section

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus

/-- Quadratic action on the actual projective torus forces a trivial field
coefficient, with the cubic scalar kernel retained in the proof. -/
theorem field_eq_one_of_projective_quadratic {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2) (σ : E ≃+* E)
    (h : ∀ k : Eˣ,
      hermitianTorusPSU J hJ (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom k * k⁻¹)) =
        hermitianTorusPSU J hJ (Units.map σ.toMonoidHom k * k⁻¹)) : σ = 1 := by
  apply RingEquiv.eq_one_of_cubic_quadratic_units hn hcard σ
  intro k
  apply ((projective_eq_one_iff J hJ _).mp ?_).2
  rw [map_mul, map_inv, h, mul_inv_cancel]

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
