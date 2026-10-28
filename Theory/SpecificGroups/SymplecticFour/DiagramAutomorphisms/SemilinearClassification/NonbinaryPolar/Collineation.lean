module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.ProjectiveAction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Collineation.Frame
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Collineation.CoordinateField
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Collineation.CoordinateDetermination

/-!
# Projective coordinatization in the actual symplectic four-space

Every permutation of the projective points of the actual four-space preserving
line incidence has a semilinear lift. `Collineation.exists_normalized` first removes an
invertible linear map realizing the image of the standard projective frame.
`Collineation.normalized_coordinate_field` reconstructs a field automorphism
from the remaining action on coordinate lines, including its additive and
multiplicative laws. `Collineation.eq_fieldProjective_of_coordinate_lines`
then identifies the action on every point by its coordinate ratios. Reattaching
the linear map gives `projective_permutation_has_semilinear_lift`.

Source context: Aschbacher--Smith F.1.12, printed pp.263--264 of
`refs/quasithin.pdf`.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A projective permutation preserving all line incidences is induced by a
coordinatewise field automorphism followed by an invertible linear map. -/
theorem projective_permutation_has_semilinear_lift (hF : Nat.card F ≠ 2)
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q r, (φ r).submodule ≤ (φ p).submodule ⊔ (φ q).submodule ↔
      r.submodule ≤ p.submodule ⊔ q.submodule) :
    ∃ (σ : F ≃+* F) (A : Vector F ≃ₗ[F] Vector F), ∀ p,
      φ p = Projectivization.map A.toLinearMap A.injective (fieldProjective σ p) := by
  obtain ⟨A, ψ, hψ, haxes, hdiag, hφψ⟩ := Collineation.exists_normalized φ hφ
  obtain ⟨σ, hpairs⟩ := Collineation.normalized_coordinate_field hF ψ hψ haxes hdiag
  refine ⟨σ, A, fun p => ?_⟩
  rw [hφψ p, Collineation.eq_fieldProjective_of_coordinate_lines ψ hψ haxes σ hpairs p,
    Collineation.linearProjective_apply]

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
