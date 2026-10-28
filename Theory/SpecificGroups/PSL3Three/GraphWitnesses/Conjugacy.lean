module

public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Graph
public import Theory.SpecificGroups.PSL3Three.Simplicity
public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.Thirteen
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.SymmetricSimilarity.FiniteForms
import Mathlib.Tactic

/-!
# Conjugacy of outer involutions of the native PSL₃(3)

Every outer involution of the actual projective matrix group is conjugate to
inverse transpose. Odd-prime automorphism coverage gives a linear-times-graph
expression; its square forces the conjugating matrix to be symmetric.

For an invertible symmetric ternary matrix S, discriminant classification
identifies its quadratic form with det(S) times the identity form: their
discriminant ratio is det(S)². The resulting congruence writes S as a scalar
multiple of h hᵀ. Scalars act trivially on the projective group, so this Gram
factorization gives the required automorphism conjugacy. The published
order-thirteen calculation then supplies a witness for every outer involution.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10, the PSL₃(3) outer-involution argument. The automorphism
coverage is the odd-prime A₂ case of GLS3, Theorem 2.5.12(a). The finite-form
classification and its ATLAS attribution and license remain in the imported
`SymmetricSimilarity.FiniteForms` module. Simplicity and nonsolvability are
proved for the literal native model by `PSL3Three.Simplicity`.
-/

open Matrix
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OddInvolutionFixed

namespace Matrix.PSL3Three.GraphWitnesses

local instance : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)

private theorem matrix_form_matrix (S : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hs : S.transpose = S) : S.toQuadraticForm'.toMatrix' = S := by
  have hB := Matrix.isSymm_toBilin'_iff_isSymm.mpr hs
  change LinearMap.toMatrix₂' (ZMod 3) (QuadraticMap.associated S.toBilin'.toQuadraticMap) = S
  rw [QuadraticMap.associated_left_inverse (ZMod 3) (fun x y => hB.eq x y)]
  exact LinearMap.toMatrix'_toLinearMap₂' S

private theorem polar_nondegenerate (Q : QuadraticForm (ZMod 3) (Fin 3 → ZMod 3))
    (hQ : Q.toMatrix'.det ≠ 0) : Q.polarBilin.Nondegenerate := by
  have ha : Q.associated.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toMatrix'_iff.mp
      (Matrix.nondegenerate_iff_det_ne_zero.mpr hQ)
  constructor
  · intro x hx
    apply ha.1
    intro y
    have h := congrArg (fun B => B x y) (QuadraticMap.two_nsmul_associated (S := ZMod 3) Q)
    simp only [LinearMap.smul_apply, nsmul_eq_mul, hx] at h
    exact (mul_eq_zero.mp h).resolve_left (by decide)
  · intro x hx
    apply ha.2
    intro y
    have h := congrArg (fun B => B y x) (QuadraticMap.two_nsmul_associated (S := ZMod 3) Q)
    simp only [LinearMap.smul_apply, nsmul_eq_mul, hx] at h
    exact (mul_eq_zero.mp h).resolve_left (by decide)

private theorem symmetric_congruence (S : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hs : S.transpose = S) (hd : S.det ≠ 0) :
    ∃ (a : ZMod 3) (C : GL (Fin 3) (ZMod 3)), a ≠ 0 ∧
      C.val.transpose * S * C.val = a • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
  let Q := S.toQuadraticForm'
  let R := S.det • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)).toQuadraticForm'
  have hQ : Q.toMatrix' = S := matrix_form_matrix S hs
  have hR : R.toMatrix' = S.det • (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    rw [QuadraticForm.toMatrix'_smul, matrix_form_matrix 1 Matrix.transpose_one]
  have hRd : R.discr' = S.det ^ 3 := by
    rw [QuadraticForm.discr', hR, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, mul_one]
  have hQd : Q.discr' = S.det := congrArg Matrix.det hQ
  obtain ⟨e⟩ :=
    (BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Descent.SymmetricSimilarity.finite_nondegenerate_isometry_iff_discr_square
      (by decide : (2 : ZMod 3) ≠ 0) 2 R Q
      (polar_nondegenerate R (by change R.discr' ≠ 0; rw [hRd]; exact pow_ne_zero _ hd))
      (polar_nondegenerate Q (by rwa [hQ]))).mpr (by
        rw [hRd, hQd]
        refine ⟨S.det, ?_⟩
        field_simp)
  let M := LinearMap.toMatrix' e.toLinearEquiv.toLinearMap
  have hM : M.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact e.toLinearEquiv.isUnit_det'.ne_zero
  refine ⟨S.det, GeneralLinearGroup.mkOfDetNeZero M hM, hd, ?_⟩
  have he : Q.comp e.toLinearEquiv.toLinearMap = R := by
    ext v
    exact e.map_app v
  have h := congrArg QuadraticForm.toMatrix' he
  rw [QuadraticForm.toMatrix'_comp, hQ, hR] at h
  exact h

private theorem symmetric_scalar_gram (g : GL (Fin 3) (ZMod 3))
    (hs : g.val.transpose = g.val) :
    ∃ (a : (ZMod 3)ˣ) (h : GL (Fin 3) (ZMod 3)),
      g = GeneralLinearGroup.scalar (Fin 3) a * (h * inverseTransposeGL h⁻¹) := by
  obtain ⟨a, C, ha, hC⟩ := symmetric_congruence g.val hs (GeneralLinearGroup.det_ne_zero g)
  let z := Units.mk0 a ha
  have hcg : (inverseTransposeGL C)⁻¹ * g * C = GeneralLinearGroup.scalar (Fin 3) z := by
    apply Units.ext
    change C.val.transpose * g.val * C.val = Matrix.scalar (Fin 3) a
    simpa only [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply] using hC
  have hi : inverseTransposeGL (inverseTransposeGL C)⁻¹ = C⁻¹ := by
    rw [map_inv]
    rfl
  refine ⟨z, inverseTransposeGL C, ?_⟩
  rw [hi]
  calc
    g = inverseTransposeGL C * GeneralLinearGroup.scalar (Fin 3) z * C⁻¹ := by
      rw [← hcg]
      group
    _ = _ := by rw [← GeneralLinearGroup.scalar_commute, mul_assoc]

/-- Every outer involution of the native PSL₃(3) model is conjugate to inverse transpose. -/
public theorem outer_involution_graph_conjugate (b : MulAut PSL) (hb : orderOf b = 2)
    (hout : b ∉ MulAut.innerSubgroup PSL) :
    ∃ u : MulAut PSL, b = u * graph (ZMod 3) * u⁻¹ := by
  let : IsSimpleGroup PSL := isSimpleGroup_psl3_three
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  obtain ⟨g, rfl | rfl⟩ := automorphism_normal_form not_isSolvable_psl3_three
    (by decide : Nat.Prime 3) (by decide : Odd 3) (Nat.card_zmod 3) b
  · exact (hout (linearConj_involution_inner g hb2)).elim
  · obtain ⟨a, h, hg⟩ := symmetric_scalar_gram g (graph_involution_symmetric g hb2)
    refine ⟨linearConj (ZMod 3) h, ?_⟩
    rw [hg, map_mul, linearConj_scalar, one_mul, map_mul]
    rw [mul_assoc, ← graph_linearConj, ← mul_assoc, map_inv]

/-- The native outer-involution calculation supplies the order-thirteen source witness. -/
public theorem outer_involution_inverts_thirteen (b : MulAut PSL) (hb : orderOf b = 2)
    (hout : b ∉ MulAut.innerSubgroup PSL) :
    ∃ x : PSL, orderOf x = 13 ∧ b x = x⁻¹ :=
  inverts_thirteen_of_graph_conjugate b (outer_involution_graph_conjugate b hb hout)

end Matrix.PSL3Three.GraphWitnesses
