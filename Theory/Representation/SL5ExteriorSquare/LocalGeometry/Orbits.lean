module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.Conjugacy
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.Bivectors
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.InvolutionNormalForm
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.VectorNormalForm
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.Stabilizer

/-!
# Intrinsic orbit calculations for Λ²(F₂⁵)

This interface exports the complete intrinsic orbit calculation for Λ²(F₂⁵).
The two involution classes are exhausted by the marked representatives, and
their natural and exterior displacement ranks are transported by conjugacy.
The two nonzero-vector orbits are exhausted by the decomposable and
nondecomposable representatives. The latter stabilizer has the shared shear
subgroup as its relative normal kernel and quotient S₆.

Source: Aschbacher–Smith, 12.5.5, printed p.819/PDF p.836.
-/

public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- The two source involution classes are mutually exclusive and exhaustive. -/
theorem involution_conjugacy_exactly_one (g : Group) (hne : g ≠ 1)
    (hg : g * g = 1) :
    (IsConj j₁ g ∧ ¬ IsConj j₂ g) ∨
      (IsConj j₂ g ∧ ¬ IsConj j₁ g) := by
  rcases involution_conjugacy_exhaustion g hne hg with h | h
  · left
    refine ⟨h, ?_⟩
    intro h₂
    exact not_isConj_j₁_j₂ (h.trans h₂.symm)
  · right
    refine ⟨h, ?_⟩
    intro h₁
    exact not_isConj_j₁_j₂ (h₁.trans h.symm)

/-- The two nonzero source points lie in mutually exclusive exhaustive orbits. -/
theorem exterior_orbits_exactly_one (v : V) (hv : v ≠ 0) :
    (InExteriorOrbit decomposable v ∧
        ¬ InExteriorOrbit nondecomposable v) ∨
      (InExteriorOrbit nondecomposable v ∧
        ¬ InExteriorOrbit decomposable v) := by
  rcases exterior_orbits_exhaustive v hv with h | h
  · left
    refine ⟨h, ?_⟩
    intro h₂
    exact not_inExteriorOrbit_decomposable_nondecomposable (h.trans h₂.symm)
  · right
    refine ⟨h, ?_⟩
    intro h₁
    exact not_inExteriorOrbit_decomposable_nondecomposable (h₁.trans h.symm)

end Representation.SL5ExteriorSquare
