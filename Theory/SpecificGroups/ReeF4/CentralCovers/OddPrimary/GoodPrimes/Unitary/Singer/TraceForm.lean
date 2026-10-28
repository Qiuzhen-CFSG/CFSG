module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Singer.FieldAction
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Hermitian matrices for the full unitary Singer torus

The relative trace commutes with the q³-involution and the stored
q-Frobenius on the quadratic field. Thus Tr(conj(x)y) is a nondegenerate
Hermitian form on the cubic extension. Its Gram matrix in `regularBasis`
is preserved by the literal regular multiplication matrices. Restricting
those matrices gives a faithful map to the determinant-one isometry group.
The final Singer module changes basis to the literal identity form.

The coordinate arguments adapt the existing project proof in
G2/MultiplierOrdinary/OddCyclotomicSylow/TwistedCubicTorus/UnitaryRealization.lean,
using the prime-power fields and embedding proved in `FieldAction`.
Sources: GLS3 §4.10 and §6.5, refs/KGroup/GLS3/chapter4.tex and chapter6.tex.
-/

@[expose] public noncomputable section

open Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Singer

/-- The relative trace commutes with the two compatible field involutions. -/
theorem trace_sexticConj (m : ℕ) (x : SingerParameters.Field m) :
    Algebra.trace (Three.QuadraticField m) (SingerParameters.Field m) (sexticConj m x) =
      (Three.form m).conj (Algebra.trace (Three.QuadraticField m) (SingerParameters.Field m) x) := by
  have he : (algebraMap (Three.QuadraticField m) (SingerParameters.Field m)).comp ((Three.form m).conj).toRingHom =
      (sexticConj m).toRingHom.comp (algebraMap (Three.QuadraticField m) (SingerParameters.Field m)) := by
    ext a
    exact (sexticConj_algebraMap m a).symm
  have ht := Algebra.trace_eq_of_equiv_equiv ((Three.form m).conj) (sexticConj m) he x
  exact (((Three.form m).conj).symm_apply_eq.mp ht.symm)

/-- Hermitian symmetry for the actual trace pairing. -/
theorem tracePairing_hermitian (m : ℕ) (x y : SingerParameters.Field m) :
    (Three.form m).conj (tracePairing m y x) = tracePairing m x y := by
  unfold tracePairing
  rw [← trace_sexticConj m, map_mul, sexticConj_involutive m, mul_comm y (sexticConj m x)]

/-- Transposition recovers the source convention Tr(x y^(q³)) exactly. -/
theorem tracePairing_transpose (m : ℕ) (x y : SingerParameters.Field m) :
    tracePairing m y x = Algebra.trace (Three.QuadraticField m) (SingerParameters.Field m)
      (x * y ^ ((2 ^ (2 * m + 1)) ^ 3)) := by
  rw [tracePairing, sexticConj_apply]
  exact congrArg (Algebra.trace (Three.QuadraticField m) (SingerParameters.Field m)) (mul_comm _ _)

/-- The trace pairing is conjugate-linear in its first argument. -/
theorem tracePairing_smul_left (m : ℕ) (a : Three.QuadraticField m)
    (x y : SingerParameters.Field m) :
    tracePairing m (a • x) y = (Three.form m).conj a * tracePairing m x y := by
  unfold tracePairing
  rw [Algebra.smul_def, (sexticConj m).map_mul, sexticConj_algebraMap m, mul_assoc,
    ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- The trace pairing is linear in its second argument. -/
theorem tracePairing_smul_right (m : ℕ) (a : Three.QuadraticField m) (x y : SingerParameters.Field m) :
    tracePairing m x (a • y) = a * tracePairing m x y := by
  unfold tracePairing
  rw [mul_smul_comm, map_smul, smul_eq_mul]

/-- Additivity in the first argument of the trace pairing. -/
theorem tracePairing_add_left (m : ℕ) (x y z : SingerParameters.Field m) :
    tracePairing m (x + y) z = tracePairing m x z + tracePairing m y z := by
  simp [tracePairing, add_mul]

/-- Additivity in the second argument of the trace pairing. -/
theorem tracePairing_add_right (m : ℕ) (x y z : SingerParameters.Field m) :
    tracePairing m x (y + z) = tracePairing m x y + tracePairing m x z := by
  simp [tracePairing, mul_add]

private def traceSesq (m : ℕ) :
    SingerParameters.Field m →ₛₗ[((Three.form m).conj).toRingHom]
      SingerParameters.Field m →ₗ[Three.QuadraticField m] Three.QuadraticField m where
  toFun x :=
    { toFun := tracePairing m x
      map_add' := tracePairing_add_right m x
      map_smul' := by intros; exact tracePairing_smul_right m _ _ _ }
  map_add' := by
    intro x y
    ext z
    exact tracePairing_add_left m x y z
  map_smul' := by intros; ext; exact tracePairing_smul_left m _ _ _

/-- The Gram matrix in the published regular basis of the cubic extension. -/
def traceGram (m : ℕ) : Matrix (Fin 3) (Fin 3) (Three.QuadraticField m) :=
  fun i j => tracePairing m (regularBasis m i) (regularBasis m j)

/-- The Gram matrix represents the literal field trace pairing. -/
theorem tracePairing_coordinates (m : ℕ) (x y : SingerParameters.Field m) :
    tracePairing m x y = ((Three.form m).conj ∘ (regularBasis m).repr x) ⬝ᵥ
      traceGram m *ᵥ (regularBasis m).repr y := by
  have hg : LinearMap.toMatrix₂ (regularBasis m) (regularBasis m)
      (traceSesq m) = traceGram m := by
    ext i j
    exact LinearMap.toMatrix₂_apply _ _ _ i j
  have ht := apply_eq_dotProduct_toMatrix₂_mulVec (regularBasis m)
    (regularBasis m) (traceSesq m) x y
  rw [hg] at ht
  exact ht

/-- Nondegeneracy of the trace pairing gives an invertible Gram matrix. -/
theorem traceGram_nondegenerate (m : ℕ) : (traceGram m).det ≠ 0 := by
  apply Matrix.separatingRight_iff_det_ne_zero.mp
  rw [Matrix.separatingRight_def]
  intro w hw
  let y := (regularBasis m).equivFun.symm w
  have hy : y = 0 := by
    apply tracePairing_nondegenerate_left m
    intro x
    rw [← tracePairing_hermitian m y x]
    have hxy : tracePairing m x y = 0 := by
      rw [tracePairing_coordinates m]
      change ((Three.form m).conj ∘ (regularBasis m).repr x) ⬝ᵥ
        traceGram m *ᵥ (regularBasis m).equivFun y = 0
      rw [LinearEquiv.apply_symm_apply]
      exact hw _
    rw [hxy, map_zero]
  have hh := congrArg (regularBasis m).equivFun hy
  change (regularBasis m).equivFun ((regularBasis m).equivFun.symm w) =
    (regularBasis m).equivFun 0 at hh
  rw [LinearEquiv.apply_symm_apply, map_zero] at hh
  exact hh

/-- The nondegenerate Hermitian form preserved by regular multiplication. -/
def traceHermitianForm (m : ℕ) : HermitianForm 3 (Three.QuadraticField m) where
  conj := (Three.form m).conj
  conj_involutive := (Three.form m).conj_involutive
  form := traceGram m
  form_hermitian _ _ := tracePairing_hermitian m _ _
  form_nondegenerate := traceGram_nondegenerate m

/-- The regular matrices satisfy the unitary equation for the trace Gram matrix. -/
theorem regularHom_unitary (m : ℕ) (u : SingerParameters.Group m) :
    (traceHermitianForm m).conjTranspose (regularHom m u).val *
      traceGram m * (regularHom m u).val = traceGram m := by
  have hcol (i : Fin 3) :
      (regularBasis m).repr ((u.val : SingerParameters.Field m) * regularBasis m i) =
        fun j => (regularHom m u).val j i := by
    rw [← regularHom_mulVec_repr m]
    ext j
    simp [Module.Basis.repr_self, Matrix.mulVec, dotProduct, Finsupp.single_apply]
  ext i j
  have ht := tracePairing_preserved m u (regularBasis m i) (regularBasis m j)
  rw [tracePairing_coordinates m, hcol, hcol] at ht
  change _ = tracePairing m (regularBasis m i) (regularBasis m j)
  rw [← ht]
  simp only [HermitianForm.conjTranspose, traceHermitianForm, Matrix.mul_apply,
    dotProduct, Matrix.mulVec, Function.comp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The regular multiplication matrices lie in the special unitary group
of the trace pairing, before changing basis. -/
def regularUnitaryHom (m : ℕ) :
    SingerParameters.Group m →* (traceHermitianForm m).specialSubgroup :=
  (Matrix.SpecialLinearGroup.toGL.comp (regularHom m)).codRestrict _ (fun u => by
    apply ((traceHermitianForm m).mem_specialSubgroup_iff _).mpr
    exact ⟨regularHom_unitary m u, Matrix.SpecialLinearGroup.coeToGL_det _⟩)

/-- Restriction to the exact special unitary subgroup preserves faithfulness. -/
theorem regularUnitaryHom_injective (m : ℕ) :
    Function.Injective (regularUnitaryHom m) := by
  intro u v huv
  apply regularHom_injective m
  apply Matrix.SpecialLinearGroup.toGL_injective
  exact congrArg Subtype.val huv

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Singer
