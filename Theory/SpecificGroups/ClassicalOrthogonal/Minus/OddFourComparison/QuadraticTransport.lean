module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport.Field
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport.Form
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport.Scalars

/-!
# Transport of the chosen minus-four scalar quotient

The anisotropic parameter of the original finite field is transported to
the literal Frobenius fixed field, where its quadratic polynomial has a
root in the quadratic extension. Its norm gives exactly the original
anisotropic plane. Negating one hyperbolic coordinate then identifies the
chosen minus form with negative determinant on Hermitian matrices.

Conjugation identifies the full isometry groups and their commutators.
The scalar subgroup is carried onto the scalar subgroup, giving an
equivalence of the actual projective Omega quotients with the displayed
quotient-map equation. This construction works in every characteristic;
in particular it supplies the odd-characteristic comparison. It does not
assume that the Hermitian SL₂ image equals the orthogonal commutator.

The final existential theorem packages the extension, its instances,
cardinalities, degree, nonfixed element, coefficient equivalence, quadratic
isometry and compatible group equivalence. The parent comparison with PSL₂
discharges the independent image-equality input separately.
Sources: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport
open ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
universe u
variable {F E : Type u} [Field F] [Finite F] [Field E] [Finite E]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
  (s : F ≃+* HermitianModel.fixedField σ)
  (hdim : Module.finrank (HermitianModel.fixedField σ) E = 2)

/-- The chosen minus-four commutator acts in the transported Hermitian coordinates. -/
def minusOmegaEquiv : Omega F (Space F 1) (quadraticForm F 2) ≃*
    Omega (HermitianModel.fixedField σ) (HermitianModel.Space σ hσ)
      (HermitianModel.minusForm σ hσ) :=
  omegaSemilinearCongr s (minusSpaceEquiv σ hσ s hdim)
    (minusSpaceEquiv_value σ hσ s hdim)

/-- The chosen minus-four scalar quotient is the Hermitian scalar quotient. -/
def minusProjectiveEquiv : ClassicalGroup.POmegaMinus 2 F ≃*
    ProjectiveOmega (HermitianModel.fixedField σ) (HermitianModel.Space σ hσ)
      (HermitianModel.minusForm σ hσ) :=
  projectiveSemilinearCongr s (minusSpaceEquiv σ hσ s hdim)
    (minusSpaceEquiv_value σ hσ s hdim)

/-- Compatibility with both literal scalar-quotient projections. -/
@[simp] theorem minusProjectiveEquiv_mk (g : Omega F (Space F 1) (quadraticForm F 2)) :
    minusProjectiveEquiv σ hσ s hdim
      (QuotientGroup.mk' (scalarSubgroup F (Space F 1) (quadraticForm F 2)) g) =
    QuotientGroup.mk' (scalarSubgroup (HermitianModel.fixedField σ)
      (HermitianModel.Space σ hσ) (HermitianModel.minusForm σ hσ))
        (minusOmegaEquiv σ hσ s hdim g) := by
  exact projectiveSemilinearCongr_mk s (minusSpaceEquiv σ hσ s hdim)
    (minusSpaceEquiv_value σ hσ s hdim) g

/-- A quadratic field and an actual quadratic isometry, together with its induced
scalar-quotient equivalence. All extra geometric and field premises are discharged. -/
theorem exists_comparison (F : Type u) [Field F] [Finite F] :
    ∃ (E : Type u) (_ : Field E) (_ : Finite E)
      (σ : E ≃+* E) (hσ : Function.Involutive σ),
      Nat.card E = (Nat.card F) ^ 2 ∧
      Nat.card (HermitianModel.fixedField σ) = Nat.card F ∧
      Module.finrank (HermitianModel.fixedField σ) E = 2 ∧
      (∃ t : E, σ t ≠ t) ∧
      ∃ (s : F ≃+* HermitianModel.fixedField σ)
        (e : Space F 1 ≃ₛₗ[(s : F →+* HermitianModel.fixedField σ)] HermitianModel.Space σ hσ)
        (he : ∀ v, HermitianModel.minusForm σ hσ (e v) = s (quadraticForm F 2 v))
        (f : ClassicalGroup.POmegaMinus 2 F ≃*
          ProjectiveOmega (HermitianModel.fixedField σ) (HermitianModel.Space σ hσ)
            (HermitianModel.minusForm σ hσ)),
        ∀ g : Omega F (Space F 1) (quadraticForm F 2),
          f (QuotientGroup.mk' (scalarSubgroup F (Space F 1) (quadraticForm F 2)) g) =
          QuotientGroup.mk' (scalarSubgroup (HermitianModel.fixedField σ)
            (HermitianModel.Space σ hσ) (HermitianModel.minusForm σ hσ))
              (omegaSemilinearCongr s e he g) := by
  obtain ⟨E, hE, hfin, σ, hσ, hcard, hfix, hdim⟩ := exists_quadraticField F
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (HermitianModel.fixedField σ) := Fintype.ofFinite _
  let s : F ≃+* HermitianModel.fixedField σ := FiniteField.ringEquivOfCardEq
    (by simpa only [← Nat.card_eq_fintype_card] using hfix.symm)
  refine ⟨E, hE, hfin, σ, hσ, hcard, hfix, hdim, exists_nonfixed σ s hdim,
    s, minusSpaceEquiv σ hσ s hdim, minusSpaceEquiv_value σ hσ s hdim,
    minusProjectiveEquiv σ hσ s hdim, ?_⟩
  exact minusProjectiveEquiv_mk σ hσ s hdim

end ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport
