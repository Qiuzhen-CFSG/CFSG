module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.ProjectiveAction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Collineation
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Lines
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Normalization

/-!
# Classification of nonbinary symplectic polar permutations

Every orthogonality-preserving permutation of the projective points of the
actual symplectic four-space over a nonbinary finite field of characteristic
two is induced by a symplectic matrix and a field automorphism.

The double-perpendicular construction recovers every projective line from
orthogonality. Projective coordinatization then constructs a semilinear lift.
Its linear part is a symplectic similitude, whose multiplier can be normalized
using square-surjectivity in the finite field. Thus the final theorem assumes
only preservation of orthogonality; it does not require a lift as input.

Source: the geometric automorphism fact used in Aschbacher--Smith F.1.12,
printed pp.263--264 of `refs/quasithin.pdf`.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every polar permutation over a nonbinary finite field of characteristic
two is the projective action of a symplectic matrix and a field automorphism. -/
theorem polar_permutation_eq_innerFieldProjective_of_card_ne_two
    (hF : Nat.card F ≠ 2) (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q) :
    ∃ (g : Sp F) (σ : F ≃+* F), φ = innerFieldProjective g σ := by
  obtain ⟨σ, A, hlift⟩ := projective_permutation_has_semilinear_lift hF φ
    (polar_permutation_preserves_projective_lines φ hφ)
  obtain ⟨g, hg⟩ := polar_permutation_eq_innerFieldProjective_of_lift φ hφ σ A hlift
  exact ⟨g, σ, hg⟩

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
