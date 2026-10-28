module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryModel
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Realization of the twisted cubic field units in SU₃

For K = F_{p²} and its cubic extension E, the involution x ↦ x^{p³}
restricts to the stored quadratic Frobenius. Compatibility of trace with
these involutions makes Tr(E/K)(conj(x)y) a nondegenerate Hermitian form.
Its Gram matrix in `regularBasis` is preserved by the actual regular
multiplication matrices of `fieldUnits`, whose determinant is already one.

An orthonormal basis for this form conjugates these matrices into
`standardForm.specialSubgroup`. The resulting homomorphism is injective,
so it retains the full cyclotomic order, including central factors. The
construction works for every prime p; the later G₂ application imposes
3 < p. `exists_unitary_embedding` supplies the first map consumed by
`exists_twisted_cubic_torus_of_unitary_embeddings`; the independent embedding
of this SU₃ into the split-octonion model is left to the parent assembly.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, I.1.2–I.1.4, printed pp.407–408, and GLS III §6.1. The
orthonormalization input is the checked Huppert II.10.4 theorem.
-/

@[expose] public section

open Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
noncomputable section
namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus
variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- The sextic involution restricts to the specified quadratic conjugation. -/
theorem sexticConj_algebraMap (hF : Nat.card F = p) (a : Quadratic F p) :
    sexticConj F p (algebraMap (Quadratic F p) (Sextic F p) a) =
      algebraMap (Quadratic F p) (Sextic F p) (quadraticConj F p a) := by
  rw [sexticConj_apply, quadraticConj_apply F p hF, ← map_pow]
  congr 1
  have ha : a ^ (p ^ 2) = a := by
    rw [← card_quadratic F p hF]
    let := Fintype.ofFinite (Quadratic F p)
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  rw [show p ^ 3 = p ^ 2 * p by ring, pow_mul, ha]

/-- The relative trace commutes with the two compatible field involutions. -/
theorem trace_sexticConj (hF : Nat.card F = p) (x : Sextic F p) :
    Algebra.trace (Quadratic F p) (Sextic F p) (sexticConj F p x) =
      quadraticConj F p (Algebra.trace (Quadratic F p) (Sextic F p) x) := by
  have he : (algebraMap (Quadratic F p) (Sextic F p)).comp (quadraticConj F p).toRingHom =
      (sexticConj F p).toRingHom.comp (algebraMap (Quadratic F p) (Sextic F p)) := by
    ext a
    exact (sexticConj_algebraMap F p hF a).symm
  have ht := Algebra.trace_eq_of_equiv_equiv (quadraticConj F p) (sexticConj F p) he x
  exact ((quadraticConj F p).symm_apply_eq.mp ht.symm)

/-- Hermitian symmetry for the actual trace pairing. -/
theorem tracePairing_hermitian (hF : Nat.card F = p) (x y : Sextic F p) :
    quadraticConj F p (tracePairing F p y x) = tracePairing F p x y := by
  unfold tracePairing
  rw [← trace_sexticConj F p hF, map_mul, sexticConj_involutive F p hF, mul_comm]

/-- The trace pairing is conjugate-linear in its first argument. -/
theorem tracePairing_smul_left (hF : Nat.card F = p) (a : Quadratic F p)
    (x y : Sextic F p) :
    tracePairing F p (a • x) y = quadraticConj F p a * tracePairing F p x y := by
  unfold tracePairing
  rw [Algebra.smul_def, (sexticConj F p).map_mul, sexticConj_algebraMap F p hF, mul_assoc,
    ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- The trace pairing is linear in its second argument. -/
theorem tracePairing_smul_right (a : Quadratic F p) (x y : Sextic F p) :
    tracePairing F p x (a • y) = a * tracePairing F p x y := by
  unfold tracePairing
  rw [mul_smul_comm, map_smul, smul_eq_mul]

/-- Additivity in the first argument of the trace pairing. -/
theorem tracePairing_add_left (x y z : Sextic F p) :
    tracePairing F p (x + y) z = tracePairing F p x z + tracePairing F p y z := by
  simp [tracePairing, add_mul]

/-- Additivity in the second argument of the trace pairing. -/
theorem tracePairing_add_right (x y z : Sextic F p) :
    tracePairing F p x (y + z) = tracePairing F p x y + tracePairing F p x z := by
  simp [tracePairing, mul_add]

private def traceSesq (hF : Nat.card F = p) :
    Sextic F p →ₛₗ[(quadraticConj F p).toRingHom]
      Sextic F p →ₗ[Quadratic F p] Quadratic F p where
  toFun x :=
    { toFun := tracePairing F p x
      map_add' := tracePairing_add_right F p x
      map_smul' := by intros; exact tracePairing_smul_right F p _ _ _ }
  map_add' := by
    intro x y
    ext z
    exact tracePairing_add_left F p x y z
  map_smul' := by intros; ext; exact tracePairing_smul_left F p hF _ _ _

/-- The Gram matrix in the published regular basis of the cubic extension. -/
def traceGram : Matrix (Fin 3) (Fin 3) (Quadratic F p) :=
  fun i j => tracePairing F p (regularBasis F p i) (regularBasis F p j)

/-- The Gram matrix represents the literal field trace pairing. -/
theorem tracePairing_coordinates (hF : Nat.card F = p) (x y : Sextic F p) :
    tracePairing F p x y = (quadraticConj F p ∘ (regularBasis F p).repr x) ⬝ᵥ
      traceGram F p *ᵥ (regularBasis F p).repr y := by
  have hg : LinearMap.toMatrix₂ (regularBasis F p) (regularBasis F p)
      (traceSesq F p hF) = traceGram F p := by
    ext i j
    exact LinearMap.toMatrix₂_apply _ _ _ i j
  have ht := apply_eq_dotProduct_toMatrix₂_mulVec (regularBasis F p)
    (regularBasis F p) (traceSesq F p hF) x y
  rw [hg] at ht
  exact ht

/-- Nondegeneracy of the trace pairing gives an invertible Gram matrix. -/
theorem traceGram_nondegenerate (hF : Nat.card F = p) : (traceGram F p).det ≠ 0 := by
  apply Matrix.separatingRight_iff_det_ne_zero.mp
  rw [Matrix.separatingRight_def]
  intro w hw
  let y := (regularBasis F p).equivFun.symm w
  have hy : y = 0 := by
    apply tracePairing_nondegenerate_left F p
    intro x
    rw [← tracePairing_hermitian F p hF y x]
    have hxy : tracePairing F p x y = 0 := by
      rw [tracePairing_coordinates F p hF]
      change (quadraticConj F p ∘ (regularBasis F p).repr x) ⬝ᵥ
        traceGram F p *ᵥ (regularBasis F p).equivFun y = 0
      rw [LinearEquiv.apply_symm_apply]
      exact hw _
    rw [hxy, map_zero]
  have hh := congrArg (regularBasis F p).equivFun hy
  change (regularBasis F p).equivFun ((regularBasis F p).equivFun.symm w) =
    (regularBasis F p).equivFun 0 at hh
  rw [LinearEquiv.apply_symm_apply, map_zero] at hh
  exact hh

/-- The nondegenerate Hermitian form preserved by regular multiplication. -/
def traceHermitianForm (hF : Nat.card F = p) : HermitianForm 3 (Quadratic F p) where
  conj := quadraticConj F p
  conj_involutive := quadraticConj_involutive F p
  form := traceGram F p
  form_hermitian _ _ := tracePairing_hermitian F p hF _ _
  form_nondegenerate := traceGram_nondegenerate F p hF

/-- The regular matrices satisfy the unitary equation for the trace Gram matrix. -/
theorem regularHom_unitary (hF : Nat.card F = p) (u : fieldUnits F p) :
    (traceHermitianForm F p hF).conjTranspose (regularHom F p hF u).val *
      traceGram F p * (regularHom F p hF u).val = traceGram F p := by
  have hcol (i : Fin 3) :
      (regularBasis F p).repr ((u.val : Sextic F p) * regularBasis F p i) =
        fun j => (regularHom F p hF u).val j i := by
    rw [← regularHom_mulVec_repr F p hF]
    ext j
    simp [Module.Basis.repr_self, Matrix.mulVec, dotProduct, Finsupp.single_apply]
  ext i j
  have ht := tracePairing_preserved F p u (regularBasis F p i) (regularBasis F p j)
  rw [tracePairing_coordinates F p hF, hcol, hcol] at ht
  change _ = tracePairing F p (regularBasis F p i) (regularBasis F p j)
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
def regularUnitaryHom (hF : Nat.card F = p) :
    fieldUnits F p →* (traceHermitianForm F p hF).specialSubgroup :=
  (Matrix.SpecialLinearGroup.toGL.comp (regularHom F p hF)).codRestrict _ (fun u => by
    apply ((traceHermitianForm F p hF).mem_specialSubgroup_iff _).mpr
    exact ⟨regularHom_unitary F p hF u, Matrix.SpecialLinearGroup.coeToGL_det _⟩)

/-- Restriction to the exact special unitary subgroup preserves faithfulness. -/
theorem regularUnitaryHom_injective (hF : Nat.card F = p) :
    Function.Injective (regularUnitaryHom F p hF) := by
  intro u v huv
  apply regularHom_injective F p hF
  apply Matrix.SpecialLinearGroup.toGL_injective
  exact congrArg Subtype.val huv

/-- Orthonormalization embeds the full cyclotomic unit group in the actual
identity-form SU₃, retaining the determinant and all central elements. -/
theorem exists_unitary_embedding (hF : Nat.card F = p) :
    ∃ ρ : fieldUnits F p →* (standardForm F p).specialSubgroup,
      Function.Injective ρ := by
  obtain ⟨C, hC⟩ := (traceHermitianForm F p hF).exists_orthonormal_basis_of_prime_frobenius
    (quadraticConj_apply F p hF) (card_quadratic F p hF)
  let e := HermitianForm.IdentityGram.specialEquiv (traceHermitianForm F p hF) C hC
  have he : HermitianForm.IdentityGram.identityGram (traceHermitianForm F p hF) =
      standardForm F p := rfl
  rw [← he]
  exact ⟨e.toMonoidHom.comp (regularUnitaryHom F p hF),
    e.injective.comp (regularUnitaryHom_injective F p hF)⟩

end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus

end
