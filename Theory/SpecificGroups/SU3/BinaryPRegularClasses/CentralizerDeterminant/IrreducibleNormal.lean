module

public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant.NormalCorrection
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.TraceParameters
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.PowerBasis

/-!
# Normal determinant witnesses for irreducible unitary cubics

An irreducible cubic characteristic polynomial makes the natural three-space
one-dimensional over its cubic root field. Finite-field norm surjectivity
therefore gives every prescribed determinant as a polynomial in the original
matrix. Its adjoint centralizes the same unitary matrix, and hence commutes
with that polynomial. This supplies normal linear witnesses for arbitrary
nonzero determinants and, by adjoint correction, unitary witnesses for every
norm-one determinant over the binary square field.

The root-field construction refines the argument in
`SL3/PRegularClasses/CentralizerDeterminant.lean` by retaining a polynomial
representative of the norm witness. No odd-order assumption is needed in this
irreducible branch. This is the centralizer step in the SU₃ class argument
associated with GLS III 2.8.2, 2.8.6(a), and 2.8.10(c),
`refs/KGroup/GLS3/chapter2.tex`; the exhaustive source assembly is separate.
-/

open Polynomial Module.End Matrix BenderSuzuki.MatrixGroups
noncomputable section
namespace Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant
variable {F : Type*} [Field F]

private theorem exists_polynomial_det_of_irreducible_cubic [Finite F]
    (f : Module.End F (Fin 3 → F)) (p : Polynomial F)
    (hp : Irreducible p) (hroot : Polynomial.aeval f p = 0)
    (hdim : p.natDegree = 3) (d : F) :
    ∃ q : Polynomial F, LinearMap.det (Polynomial.aeval f q) = d := by
  let : Fact (Irreducible p) := ⟨hp⟩
  let φ : AdjoinRoot p →ₐ[F] Module.End F (Fin 3 → F) :=
    Ideal.Quotient.liftₐ (Ideal.span {p}) (Polynomial.aeval f) (by
      intro q hq
      rcases Ideal.mem_span_singleton.mp hq with ⟨r, rfl⟩
      rw [map_mul, hroot, zero_mul])
  let : Module (AdjoinRoot p) (Fin 3 → F) := Module.compHom (Fin 3 → F) φ.toRingHom
  let : IsScalarTower F (AdjoinRoot p) (Fin 3 → F) :=
    IsScalarTower.of_algebraMap_smul (fun r x => by
      change φ (algebraMap F (AdjoinRoot p) r) x = r • x
      rw [φ.commutes]
      rfl)
  let : Module.Finite F (AdjoinRoot p) := (AdjoinRoot.powerBasis hp.ne_zero).finite
  let : Finite (AdjoinRoot p) := Module.finite_of_finite F
  let : Module.Free (AdjoinRoot p) (Fin 3 → F) := Module.Free.of_divisionRing _ _
  let : Module.Finite (AdjoinRoot p) (Fin 3 → F) := Module.Finite.of_finite
  have hfinS : Module.finrank F (AdjoinRoot p) = 3 := by
    rw [(AdjoinRoot.powerBasis hp.ne_zero).finrank]
    simp [hdim]
  have hfinV : Module.finrank F (Fin 3 → F) = 3 := by simp
  have hfinrank : Module.finrank (AdjoinRoot p) (Fin 3 → F) = 1 := by
    have hmul := Module.finrank_mul_finrank F (AdjoinRoot p) (Fin 3 → F)
    rw [hfinS, hfinV] at hmul
    omega
  obtain ⟨s, hs⟩ := (FiniteField.norm_surjective F (AdjoinRoot p)) d
  let g : (Fin 3 → F) →ₗ[AdjoinRoot p] (Fin 3 → F) :=
    LinearMap.lsmul (AdjoinRoot p) _ s
  have hdetS : LinearMap.det g = s := by
    change LinearMap.det (s • (LinearMap.id : (Fin 3 → F) →ₗ[AdjoinRoot p] (Fin 3 → F))) = s
    rw [LinearMap.det_smul, LinearMap.det_id, hfinrank, pow_one, mul_one]
  have hdetF : LinearMap.det (g.restrictScalars F) = d := by
    rw [LinearMap.det_restrictScalars, hdetS, hs]
  let c : Module.End F (Fin 3 → F) := g.restrictScalars F
  have hcφ : c = φ s := by
    ext x
    rfl
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective s
  refine ⟨q, ?_⟩
  have hφq : φ (AdjoinRoot.mk p q) = Polynomial.aeval f q := rfl
  rw [← hφq, hq, ← hcφ]
  exact hdetF

private theorem polynomial_commute {R : Type*} [Ring R] [Algebra F R]
    {a b : R} (h : Commute a b) (q : Polynomial F) :
    Commute (Polynomial.aeval a q) b := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simpa only [map_add] using hq.add_left hr
  | monomial n r =>
    rw [Polynomial.aeval_monomial]
    exact Commute.mul_left (Algebra.commutes r b) (h.pow_left n)

private theorem exists_matrix_polynomial_det [Finite F]
    (G : Matrix (Fin 3) (Fin 3) F) (hG : Irreducible G.charpoly) (d : F) :
    ∃ q : Polynomial F, (Polynomial.aeval G q).det = d := by
  obtain ⟨q, hq⟩ := exists_polynomial_det_of_irreducible_cubic
    (Matrix.toLin' G) G.charpoly hG
    (by rw [← Matrix.charpoly_toLin']; exact LinearMap.aeval_self_charpoly _)
    (by simp) d
  refine ⟨q, ?_⟩
  rw [← LinearMap.det_toLin']
  have he : Matrix.toLin' (Polynomial.aeval G q) =
      Polynomial.aeval (Matrix.toLin' G) q :=
    (Polynomial.aeval_algHom_apply Matrix.toLinAlgEquiv' G q).symm
  rw [he]
  exact hq

/-- Irreducibility supplies a normal linear centralizer witness for every
nonzero determinant, for the original Hermitian form. -/
public theorem exists_normal_centralizer_det_of_irreducible [Finite F]
    (J : HermitianForm 3 F) (g : J.specialSubgroup)
    (hg : Irreducible g.val.val.charpoly) (d : Fˣ) :
    ∃ A : GL (Fin 3) F, Commute A g.val ∧ Commute A (adjoint J A) ∧
      GeneralLinearGroup.det A = d := by
  obtain ⟨q, hq⟩ := exists_matrix_polynomial_det g.val.val hg (d : F)
  let A : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero
    (Polynomial.aeval g.val.val q) (hq ▸ d.ne_zero)
  have hAg : Commute A g.val :=
    Units.ext (polynomial_commute (Commute.refl g.val.val) q).eq
  have hAn : Commute A (adjoint J A) := by
    have ha := commute_adjoint J
      ⟨g.val, J.specialSubgroup_le_unitarySubgroup g.property⟩ A hAg
    have hav : Commute g.val.val (adjoint J A).val :=
      congrArg Units.val ha.symm.eq
    exact Units.ext (polynomial_commute hav q).eq
  refine ⟨A, hAg, hAn, ?_⟩
  apply Units.ext
  exact hq

/-- The irreducible cubic branch of unitary centralizer determinant surjectivity,
using the literal unitary image of the given special unitary element. -/
public theorem exists_unitary_centralizer_det_of_irreducible [Finite F]
    (J : HermitianForm 3 F) (g : J.specialSubgroup)
    (hg : Irreducible g.val.val.charpoly) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (d : Fˣ)
    (hd : J.conj (d : F) * (d : F) = 1) :
    ∃ C : J.unitarySubgroup, Commute C.val g.val ∧ GeneralLinearGroup.det C.val = d := by
  obtain ⟨A, hAg, hAn, hAd⟩ := exists_normal_centralizer_det_of_irreducible J g hg d
  exact exists_unitary_commuting_det_of_normal J
    ⟨g.val, J.specialSubgroup_le_unitarySubgroup g.property⟩ s (by omega)
    hcard d hd A hAg hAn hAd

end Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant
