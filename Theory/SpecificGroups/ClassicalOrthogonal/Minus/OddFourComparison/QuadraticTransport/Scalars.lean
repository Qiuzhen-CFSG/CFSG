module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison.Transport

/-!
# Semilinear transport of literal orthogonal scalar quotients

Conjugation by a semilinear quadratic isometry carries each scalar `c` to
its image under the coefficient equivalence. The inverse equivalence gives
the converse. Thus the full-isometry commutator equivalence maps the actual
scalar subgroups onto one another, in every characteristic. The induced
quotient equivalence preserves the literal quotient projections.

The minus-four Hermitian transport applies this to its constructed quadratic
isometry. No assumption of trivial scalar kernels or Hermitian image equality
is used. Sources: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport
open ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
universe u v
variable {F V : Type u} {K W : Type v} [Field F] [Field K]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module K W]
  {Q : QuadraticForm F V} {R : QuadraticForm K W}

/-- A transported commutator element is scalar exactly when the original is scalar. -/
theorem omegaSemilinearCongr_mem_scalar_iff (s : F ≃+* K)
    (e : V ≃ₛₗ[(s : F →+* K)] W) (he : ∀ x, R (e x) = s (Q x))
    (g : Omega F V Q) :
    omegaSemilinearCongr s e he g ∈ scalarSubgroup K W R ↔
      g ∈ scalarSubgroup F V Q := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨Units.map s.symm.toMonoidHom c, ?_⟩
    intro x
    apply e.injective
    rw [← omegaSemilinearCongr_apply s e he, hc, e.map_smulₛₗ]
    simp
  · rintro ⟨c, hc⟩
    refine ⟨Units.map s.toMonoidHom c, ?_⟩
    intro w
    obtain ⟨x, rfl⟩ := e.surjective w
    rw [omegaSemilinearCongr_apply, hc, e.map_smulₛₗ]
    rfl

/-- Conjugation carries the literal scalar subgroups onto one another. -/
theorem map_scalarSubgroup_omegaSemilinearCongr (s : F ≃+* K)
    (e : V ≃ₛₗ[(s : F →+* K)] W) (he : ∀ x, R (e x) = s (Q x)) :
    (scalarSubgroup F V Q).map (omegaSemilinearCongr s e he).toMonoidHom =
      scalarSubgroup K W R := by
  apply le_antisymm
  · rintro g ⟨f, hf, rfl⟩
    exact (omegaSemilinearCongr_mem_scalar_iff s e he f).mpr hf
  · intro g hg
    obtain ⟨f, rfl⟩ := (omegaSemilinearCongr s e he).surjective g
    exact ⟨f, (omegaSemilinearCongr_mem_scalar_iff s e he f).mp hg, rfl⟩

/-- The equivalence induced on the scalar quotients of the full orthogonal commutators. -/
def projectiveSemilinearCongr (s : F ≃+* K)
    (e : V ≃ₛₗ[(s : F →+* K)] W) (he : ∀ x, R (e x) = s (Q x)) :
    ProjectiveOmega F V Q ≃* ProjectiveOmega K W R :=
  QuotientGroup.congr (scalarSubgroup F V Q) (scalarSubgroup K W R)
    (omegaSemilinearCongr s e he) (map_scalarSubgroup_omegaSemilinearCongr s e he)

/-- Compatibility with the actual quotient homomorphisms. -/
@[simp] theorem projectiveSemilinearCongr_mk (s : F ≃+* K)
    (e : V ≃ₛₗ[(s : F →+* K)] W) (he : ∀ x, R (e x) = s (Q x))
    (g : Omega F V Q) :
    projectiveSemilinearCongr s e he (QuotientGroup.mk' (scalarSubgroup F V Q) g) =
      QuotientGroup.mk' (scalarSubgroup K W R) (omegaSemilinearCongr s e he g) := by
  exact QuotientGroup.congr_mk' (scalarSubgroup F V Q) (scalarSubgroup K W R)
    (omegaSemilinearCongr s e he) (map_scalarSubgroup_omegaSemilinearCongr s e he) g

end ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport
