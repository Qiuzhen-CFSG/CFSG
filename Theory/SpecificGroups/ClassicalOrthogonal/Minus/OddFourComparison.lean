module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.LowRanks
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.Projective
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.CommutatorImage
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport

/-!
# The minus-four comparison with PSL₂ over the quadratic field

The chosen minus form is transported, with its exact quadratic values, to
negative determinant on Hermitian matrices over a quadratic extension. The
SL₂ congruence image is the commutator of the full isometry group, and its
projective kernel is exactly the SL₂ center. Composing these two comparisons
gives an actual equivalence from the original commutator/scalar quotient to
PSL₂, with a formula on the literal quotient maps.

`exists_projectiveEquivPSL` constructs the extension with cardinality q² and
discharges every field, transport and image premise. This comparison works
over every finite field, in particular the odd fields required by the source.
The reexported low-rank results show that the two truncated minus ranks are
abelian in odd characteristic.
Source: Aschbacher–Smith A.2.17, printed pp.38–39; GLS3 §2.7.
-/

public noncomputable section

namespace ClassicalOrthogonal.Minus.OddFourComparison
universe u
variable {F E : Type u} [Field F] [Finite F] [Field E] [Finite E]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
  (s : F ≃+* HermitianModel.fixedField σ)
  (hdim : Module.finrank (HermitianModel.fixedField σ) E = 2)

/-- The chosen minus-four scalar quotient is PSL₂ over the quadratic extension. -/
def projectiveEquivPSL : ClassicalGroup.POmegaMinus 2 F ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) E :=
  (QuadraticTransport.minusProjectiveEquiv σ hσ s hdim).trans
    (HermitianModel.projectiveEquivPSL σ hσ hdim
      (QuadraticTransport.exists_nonfixed σ s hdim))

/-- On the original scalar quotient, a transported congruence maps to its PSL₂ class. -/
@[simp] theorem projectiveEquivPSL_apply (A : Matrix.SpecialLinearGroup (Fin 2) E) :
    projectiveEquivPSL σ hσ s hdim
      (QuotientGroup.mk' (scalarSubgroup F (Space F 1) (quadraticForm F 2))
        ((QuadraticTransport.minusOmegaEquiv σ hσ s hdim).symm
          (HermitianModel.omegaActionOfRange σ hσ
            (HermitianModel.range_orthogonalAction_eq_commutator σ hσ hdim
              (QuadraticTransport.exists_nonfixed σ s hdim)) A))) =
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) A := by
  change HermitianModel.projectiveEquivPSL σ hσ hdim
    (QuadraticTransport.exists_nonfixed σ s hdim)
    (QuadraticTransport.minusProjectiveEquiv σ hσ s hdim _) = _
  rw [QuadraticTransport.minusProjectiveEquiv_mk, MulEquiv.apply_symm_apply]
  rw [← HermitianModel.projectiveActionOfRange_apply]
  exact HermitianModel.projectiveEquivPSL_apply σ hσ hdim
    (QuadraticTransport.exists_nonfixed σ s hdim) A

/-- Every finite field has a quadratic field realizing its actual minus-four group as PSL₂. -/
theorem exists_projectiveEquivPSL (F : Type u) [Field F] [Finite F] :
    ∃ (E : Type u) (_ : Field E) (_ : Finite E),
      Nat.card E = (Nat.card F) ^ 2 ∧
      Nonempty (ClassicalGroup.POmegaMinus 2 F ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) := by
  obtain ⟨E, hE, hfin, σ, hσ, hcard, _, hdim, _, s, _⟩ :=
    QuadraticTransport.exists_comparison F
  exact ⟨E, hE, hfin, hcard, ⟨projectiveEquivPSL σ hσ s hdim⟩⟩

end ClassicalOrthogonal.Minus.OddFourComparison
