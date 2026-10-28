module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.SingerParameters
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Model
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The faithful cubic field action for the unitary Singer torus

The divisibility 2(2m+1) ∣ 6(2m+1) gives an actual embedding of the specified
GF(q²) into the specified GF(q⁶), where q = 2^(2m+1). Cardinalities show that
this extension has dimension three. Its regular multiplication action embeds
the full group of (q²−q+1)-st roots of unity in SL₃(GF(q²)); the determinant
is the field norm. It preserves the nondegenerate pairing Tr(conj(x)y),
where conj(x) = x^(q³). This conjugate-first convention is the one used by
the matrix Hermitian API, and is the transpose of Tr(x conj(y)).

The matrix and trace arguments adapt the existing project construction in
G2/MultiplierOrdinary/OddCyclotomicSylow/TwistedCubicTorus/FieldUnits.lean.
Here the parameter is a prime power, and both fields are the literal Ree
consumer fields. No projective quotient or division by three occurs.

Sources: GLS3 §4.10 and §6.5, refs/KGroup/GLS3/chapter4.tex and chapter6.tex.
Theorem 6.5.3 lists possibilities; the construction here proves existence.
-/

@[expose] public noncomputable section

namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Singer
open Matrix
open scoped MatrixGroups

/-- A chosen embedding of the literal quadratic field in the parameter field. -/
def coefficientEmbedding (m : ℕ) : Three.QuadraticField m →ₐ[ZMod 2] SingerParameters.Field m :=
  Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd (by
    rw [GaloisField.finrank 2 (by omega : (2 * m + 1) * 2 ≠ 0),
      GaloisField.finrank 2 (by omega : (2 * m + 1) * 6 ≠ 0)]
    exact ⟨3, by omega⟩))

/-- Scalars act through the specified finite-field embedding. -/
instance coefficientAlgebra (m : ℕ) : Algebra (Three.QuadraticField m) (SingerParameters.Field m) :=
  (coefficientEmbedding m).toRingHom.toAlgebra

theorem algebraMap_eq (m : ℕ) (a : Three.QuadraticField m) :
    algebraMap (Three.QuadraticField m) (SingerParameters.Field m) a =
      coefficientEmbedding m a := rfl

/-- The literal sextic field has dimension three over the literal quadratic field. -/
theorem finrank (m : ℕ) :
    Module.finrank (Three.QuadraticField m) (SingerParameters.Field m) = 3 := by
  have hc := Module.natCard_eq_pow_finrank (K := Three.QuadraticField m)
    (V := SingerParameters.Field m)
  rw [SingerParameters.field_card, Three.quadraticField_card] at hc
  simp only [← pow_mul] at hc
  have h := Nat.pow_right_injective (by decide : 1 < 2) hc
  have hd := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * m + 1)
    (by simpa only [Nat.mul_assoc] using h)
  omega

/-- Norm one to the quadratic coefficient field. -/
theorem parameter_norm (m : ℕ) (u : SingerParameters.Group m) :
    Algebra.norm (Three.QuadraticField m) (u.val : SingerParameters.Field m) = 1 := by
  apply (algebraMap (Three.QuadraticField m) (SingerParameters.Field m)).injective
  rw [map_one, FiniteField.algebraMap_norm_eq_pow_sum, finrank, Three.quadraticField_card]
  have hs : ∑ i ∈ Finset.range 3, ((2 ^ (2 * m + 1)) ^ 2) ^ i =
      (2 ^ (2 * m + 1)) ^ 4 + (2 ^ (2 * m + 1)) ^ 2 + 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    ring
  rw [hs]
  exact SingerParameters.determinant_norm m u

/-- Coordinates on GF(q⁶) as a three-dimensional GF(q²)-space. -/
def regularBasis (m : ℕ) : Module.Basis (Fin 3) (Three.QuadraticField m) (SingerParameters.Field m) :=
  Module.finBasisOfFinrankEq _ _ (finrank m)

/-- The faithful determinant-one regular multiplication representation. -/
def regularHom (m : ℕ) : SingerParameters.Group m →* SL(3, Three.QuadraticField m) where
  toFun u := ⟨Algebra.leftMulMatrix (regularBasis m) (u.val : SingerParameters.Field m), by
    rw [← Algebra.norm_eq_matrix_det]
    exact parameter_norm m u⟩
  map_one' := by apply Subtype.ext; exact map_one (Algebra.leftMulMatrix (regularBasis m))
  map_mul' u v := by
    apply Subtype.ext
    exact map_mul (Algebra.leftMulMatrix (regularBasis m)) _ _

theorem regularHom_injective (m : ℕ) : Function.Injective (regularHom m) := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  exact Algebra.leftMulMatrix_injective (regularBasis m) (congrArg Subtype.val h)

/-- The matrices act by actual field multiplication in the chosen coordinates. -/
theorem regularHom_mulVec_repr (m : ℕ) (u : SingerParameters.Group m)
    (x : SingerParameters.Field m) :
    (regularHom m u).val *ᵥ (regularBasis m).repr x =
      (regularBasis m).repr ((u.val : SingerParameters.Field m) * x) :=
  Algebra.leftMulMatrix_mulVec_repr (regularBasis m) _ _

/-- The q³-Frobenius involution on GF(q⁶). -/
def sexticConj (m : ℕ) : SingerParameters.Field m ≃+* SingerParameters.Field m :=
  iterateFrobeniusEquiv (SingerParameters.Field m) 2 ((2 * m + 1) * 3)

theorem sexticConj_apply (m : ℕ) (x : SingerParameters.Field m) :
    sexticConj m x = x ^ ((2 ^ (2 * m + 1)) ^ 3) := by
  change x ^ (2 ^ ((2 * m + 1) * 3)) = _
  rw [pow_mul]

theorem sexticConj_involutive (m : ℕ) : Function.Involutive (sexticConj m) := by
  intro x
  rw [sexticConj_apply, sexticConj_apply, ← pow_mul, ← pow_add]
  change x ^ ((2 ^ (2 * m + 1)) ^ 6) = x
  rw [← SingerParameters.field_card m]
  let := Fintype.ofFinite (SingerParameters.Field m)
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

/-- The extension involution restricts to the target's stored conjugation. -/
theorem sexticConj_algebraMap (m : ℕ) (a : Three.QuadraticField m) :
    sexticConj m (algebraMap (Three.QuadraticField m) (SingerParameters.Field m) a) =
      algebraMap (Three.QuadraticField m) (SingerParameters.Field m) ((Three.form m).conj a) := by
  rw [sexticConj_apply, Three.form_conj, ← map_pow]
  congr 1
  have ha : a ^ ((2 ^ (2 * m + 1)) ^ 2) = a := by
    rw [← Three.quadraticField_card m, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  rw [show (2 ^ (2 * m + 1)) ^ 3 = (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1)) by ring,
    pow_mul, ha]

/-- The trace pairing, with the conjugate-first matrix convention. -/
def tracePairing (m : ℕ) (x y : SingerParameters.Field m) : Three.QuadraticField m :=
  Algebra.trace (Three.QuadraticField m) (SingerParameters.Field m) (sexticConj m x * y)

/-- Every parameter preserves the literal trace pairing. -/
theorem tracePairing_preserved (m : ℕ) (u : SingerParameters.Group m)
    (x y : SingerParameters.Field m) :
    tracePairing m ((u.val : SingerParameters.Field m) * x) ((u.val : SingerParameters.Field m) * y) =
      tracePairing m x y := by
  unfold tracePairing
  rw [(sexticConj m).map_mul]
  have h : sexticConj m (u.val : SingerParameters.Field m) *
      (u.val : SingerParameters.Field m) = 1 := by
    rw [sexticConj_apply, ← pow_succ]
    exact SingerParameters.unitary_norm m u
  congr 1
  calc
    _ = (sexticConj m (u.val : SingerParameters.Field m) * (u.val : SingerParameters.Field m)) *
      (sexticConj m x * y) := by ring
    _ = _ := by rw [h, one_mul]

/-- Nondegeneracy follows from separability of the finite-field extension. -/
theorem tracePairing_nondegenerate_left (m : ℕ) (x : SingerParameters.Field m)
    (hx : ∀ y, tracePairing m x y = 0) : x = 0 := by
  have h := (traceForm_nondegenerate (Three.QuadraticField m) (SingerParameters.Field m)).1
    (sexticConj m x) hx
  exact (sexticConj m).injective (h.trans (map_zero _).symm)

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Singer
