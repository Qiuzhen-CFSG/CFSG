module

public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Defs
public import Theory.Representation.OrthogonalFourPlusMatrix.Commutant
public import Theory.SpecificGroups.SL2.CubicFixedVectors

/-!
# The scalar and cubic alternatives in the determinant module

The scalar commutant of the full binary matrix group has no nonidentity
involutions: squaring the scalar gives one in characteristic two. A subgroup
containing either whole SL₂(4) coordinate factor contains an explicit element
of order three fixing only zero in the determinant module. The latter claim
uses the natural-plane cubic fixed-vector theorem on each column or row.

These are the linear-algebra steps in the normalizer dichotomy used by
Aschbacher–Smith, Lemma 14.4.9, printed p.1010. The literal factor reduction
is separate, in `Preserving.Factors`.
-/

public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual
open Matrix Subgroup

/-- The binary centralizer of the whole determinant group has no involutions. -/
theorem centralizing_involution_eq_one (t : V ≃ₗ[ZMod 2] V)
    (h2 : t ^ 2 = 1) (hc : ∀ g : G, Commute t (linearAction g)) : t = 1 := by
  obtain ⟨c, hc⟩ := centralizer_scalar t.toAddMonoidHom (by
    intro g M
    exact LinearEquiv.congr_fun (hc g).eq M)
  change ∀ M, t M = c • M at hc
  have hsq : c ^ 2 = 1 := by
    have ht := LinearEquiv.congr_fun h2 (1 : V)
    change t (t 1) = (1 : V) at ht
    rw [hc, hc, smul_smul] at ht
    have he := congrArg (fun M : V => M 0 0) ht
    simpa [pow_two] using he
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hsq)
  apply LinearEquiv.ext
  intro M
  simpa [hc1] using hc M

private def cubic : SL := ⟨!![0, 1; 1, 1], by
  simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private theorem cubic_order : orderOf cubic = 3 := by
  apply orderOf_eq_prime
  · decide +kernel
  · intro he
    have hh := congrArg (fun A : SL => A 0 0) he
    simp [cubic] at hh

private theorem left_cubic_fixed (M : V) (h : action (cubic, 1) M = M) : M = 0 := by
  have hh : cubic.val * M = M := by simpa [action_apply] using h
  funext i j
  have hv : cubic.val *ᵥ (fun i => M i j) = (fun i => M i j) := by
    funext i
    exact congrArg (fun N : V => N i j) hh
  exact congrFun (Matrix.SL2.cubic_fixed_eq_zero cubic cubic_order _ hv) i

private theorem right_cubic_fixed (M : V) (h : action (1, cubic) M = M) : M = 0 := by
  have hh : M * cubic.val = M := by
    have hi : M * cubic⁻¹.val = M := by simpa [action_apply] using h
    have he := congrArg (fun N : V => N * cubic.val) hi
    simpa only [mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, mul_one] using he.symm
  funext i j
  have hv : cubic.val *ᵥ (fun j => M i j) = (fun j => M i j) := by
    funext j
    have he := congrArg (fun N : V => N i j) hh
    fin_cases j <;>
      simpa [cubic, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using he
  exact congrFun (Matrix.SL2.cubic_fixed_eq_zero cubic cubic_order _ hv) j

/-- Either full coordinate factor supplies the cubic actor in the literal subgroup. -/
theorem exists_cubic_of_factor_le (R : Subgroup G)
    (hR : (MonoidHom.inl SL SL).range ≤ R ∨ (MonoidHom.inr SL SL).range ≤ R) :
    ∃ r : R, orderOf r = 3 ∧ ∀ v : V, action (r : G) v = v → v = 0 := by
  rcases hR with hR | hR
  · let r : R := ⟨(cubic, 1), hR ⟨cubic, rfl⟩⟩
    refine ⟨r, ?_, left_cubic_fixed⟩
    rw [← Subgroup.orderOf_coe]
    change orderOf (cubic, (1 : SL)) = 3
    simp [Prod.orderOf_mk, cubic_order]
  · let r : R := ⟨(1, cubic), hR ⟨cubic, rfl⟩⟩
    refine ⟨r, ?_, right_cubic_fixed⟩
    rw [← Subgroup.orderOf_coe]
    change orderOf ((1 : SL), cubic) = 3
    simp [Prod.orderOf_mk, cubic_order]

end ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual
