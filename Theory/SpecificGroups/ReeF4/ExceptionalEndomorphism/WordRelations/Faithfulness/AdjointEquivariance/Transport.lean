module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.LinearExtension

/-!
# Transport of adjoint equivariance

An equivariant operator family stays equivariant under products, inverses, and
conjugation. If a matrix carries one coordinate vector to another, equivariance
identifies the corresponding operators by conjugation. In characteristic two,
the same conclusion holds for an integral signed coordinate transport.

These are the linear-algebra steps needed to pass from simple F4 root curves
to their Tits-word conjugates and to identify the actual routed root operators.
The concrete simple-curve identities are separate mathematical obligations.
The intended application is the integral Tits construction described in
`IntegralAllRootOperators`, following Geck's construction and Steinberg's
*Lectures on Chevalley Groups*.
-/

@[expose] public section

open scoped Matrix

namespace ReeF4.WordRelations.Faithfulness.Adjoint

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]

/-- Equivariance is closed under multiplication of acting matrices. -/
theorem equivariant_mul (D : (n → K) → Matrix n n K)
    (g h : (Matrix n n K)ˣ) (hg : Equivariant D g) (hh : Equivariant D h) :
    Equivariant D (g * h) := by
  intro v
  change D (((g : Matrix n n K) * (h : Matrix n n K)) *ᵥ v) *
    ((g : Matrix n n K) * (h : Matrix n n K)) =
    ((g : Matrix n n K) * (h : Matrix n n K)) * D v
  rw [← Matrix.mulVec_mulVec, ← mul_assoc, hg, mul_assoc, hh, ← mul_assoc]

/-- Equivariance is closed under inversion of acting matrices. -/
theorem equivariant_inv (D : (n → K) → Matrix n n K)
    (g : (Matrix n n K)ˣ) (hg : Equivariant D g) : Equivariant D g⁻¹ := by
  intro v
  have h := hg ((↑g⁻¹ : Matrix n n K) *ᵥ v)
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
  apply (Units.mul_right_inj g).mp
  simp only [← mul_assoc, ← h, Units.mul_inv_cancel_right,
    Units.mul_inv, one_mul]

/-- Equivariance passes from two matrices to their conjugate. -/
theorem equivariant_conjugate (D : (n → K) → Matrix n n K)
    (g h : (Matrix n n K)ˣ) (hg : Equivariant D g) (hh : Equivariant D h) :
    Equivariant D (g * h * g⁻¹) :=
  equivariant_mul D (g * h) g⁻¹ (equivariant_mul D g h hg hh)
    (equivariant_inv D g hg)

/-- Transporting a vector conjugates its operator. -/
theorem map_of_equivariant_transport (D : (n → K) → Matrix n n K)
    (g : (Matrix n n K)ˣ) (hg : Equivariant D g)
    {v w : n → K} (hw : (g : Matrix n n K) *ᵥ v = w) :
    D w = (g : Matrix n n K) * D v * (↑g⁻¹ : Matrix n n K) := by
  rw [← hw, ← hg v]
  simp only [mul_assoc, Units.mul_inv, mul_one]

/-- Coordinate transport determines the operator on the target coordinate. -/
theorem map_single_of_equivariant_transport
    (D : (n → K) → Matrix n n K) (g : (Matrix n n K)ˣ)
    (hg : Equivariant D g) {i j : n}
    (hij : (g : Matrix n n K) *ᵥ Pi.single i 1 = Pi.single j 1) :
    D (Pi.single j 1) =
      (g : Matrix n n K) * D (Pi.single i 1) * (↑g⁻¹ : Matrix n n K) :=
  map_of_equivariant_transport D g hg hij

/-- Integral signs become one in characteristic two. -/
theorem intCast_sign_eq_one [CharP K 2] {ε : ℤ} (hε : ε * ε = 1) :
    (ε : K) = 1 := by
  rcases mul_self_eq_one_iff.mp hε with h | h
  · simp [h]
  · simp [h, CharTwo.neg_eq]

/-- In characteristic two, signed coordinate transport suffices. -/
theorem map_single_of_equivariant_signed_transport [CharP K 2]
    (D : (n → K) → Matrix n n K) (g : (Matrix n n K)ˣ)
    (hg : Equivariant D g) {i j : n} {ε : ℤ} (hε : ε * ε = 1)
    (hij : (g : Matrix n n K) *ᵥ Pi.single i 1 = (ε : K) • Pi.single j 1) :
    D (Pi.single j 1) =
      (g : Matrix n n K) * D (Pi.single i 1) * (↑g⁻¹ : Matrix n n K) := by
  apply map_single_of_equivariant_transport D g hg
  simpa only [intCast_sign_eq_one (K := K) hε, one_smul] using hij

end ReeF4.WordRelations.Faithfulness.Adjoint
