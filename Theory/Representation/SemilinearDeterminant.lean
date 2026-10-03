module

public import Theory.Representation.SemilinearConjugation
public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinants under coordinate semilinear conjugation

Applying a field automorphism to the coordinates of a representation applies
that automorphism to every matrix entry, and hence to the determinant. In
particular, determinant-one normalizations survive this conjugation.

This supplies the determinant calculation in the rational-extension argument
of Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

public section

noncomputable section
namespace Representation

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Coordinate semilinear conjugation applies the field automorphism to the determinant. -/
theorem det_coordinateSemilinearConjugate {F G ι : Type*} [Field F] [Monoid G] [Fintype ι]
    (φ : F ≃+* F) (ρ : Representation F G (ι → F)) (g : G) :
    LinearMap.det (semilinearConjugate φ ρ (coordinateSemilinearEquiv φ ι) g) =
      φ (LinearMap.det (ρ g)) := by
  classical
  have hm : LinearMap.toMatrix' (semilinearConjugate φ ρ
      (coordinateSemilinearEquiv φ ι) g) = (LinearMap.toMatrix' (ρ g)).map φ := by
    ext i j
    simp only [LinearMap.toMatrix'_apply, Matrix.map_apply,
      semilinearConjugate_apply, coordinateSemilinearEquiv_apply]
    have hs : (coordinateSemilinearEquiv φ ι).symm (Pi.single j 1) = Pi.single j 1 := by
      ext k
      by_cases h : j = k <;> simp [h]
    rw [hs]
  rw [← LinearMap.det_toMatrix', hm, ← LinearMap.det_toMatrix' (ρ g)]
  exact (φ.toRingHom.map_det _).symm

end Representation
