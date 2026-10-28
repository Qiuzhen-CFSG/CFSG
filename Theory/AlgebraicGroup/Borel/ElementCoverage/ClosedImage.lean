module

public import Theory.AlgebraicGroup.Borel.ElementCoverage.Defs
public import Theory.AlgebraicGroup.Borel.ElementCoverage.Incidence
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy

/-!
# Closedness of Borel conjugacy saturation

A genuine complete model of a Borel homogeneous space identifies its conjugacy
saturation with the image of the fixed-point incidence projection. Completeness
makes that image closed. The existing complete-model existence and geometric
Borel conjugacy theorems transfer this result to every supplied Borel, without
requiring ambient connectedness.

This proves the closedness step of Borel, *Linear Algebraic Groups*, §§11.9(1)
and 11.10, `refs/KGroup/Bor1/Chapter4.tex`. Density is a separate step.
-/

open Theory.AlgebraicGroup.Variety.Geometric

namespace Theory.AlgebraicGroup.BorelElementCoverage

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- Transport the homogeneous-space fixed-point criterion to a genuine complete model. -/
public theorem mem_conjugacySaturation_iff_completeModel_fixed
    {B : ClosedSubgroup G} (M : BorelGeometricConjugacy.CompleteModel B)
    (g : Variety.Point G) :
    g ∈ conjugacySaturation B ↔
      ∃ x : Point M.variety, M.action.toMulAction.smul g x = x := by
  rw [mem_conjugacySaturation_iff_homogeneousSpace_fixed]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨M.pointEquiv.symm q, M.pointEquiv.injective ?_⟩
    rw [M.equivariant, Equiv.apply_symm_apply, hq]
  · rintro ⟨x, hx⟩
    refine ⟨M.pointEquiv x, ?_⟩
    rw [← M.equivariant, hx]

/-- The actual complete homogeneous-space model makes conjugacy saturation closed. -/
public theorem isZariskiClosed_conjugacySaturation_of_completeModel
    {B : ClosedSubgroup G} (M : BorelGeometricConjugacy.CompleteModel B) :
    IsZariskiClosed G (conjugacySaturation B) := by
  have heq : conjugacySaturation B =
      {g : Variety.Point G | ∃ x : Point M.variety, M.action.toMulAction.smul g x = x} := by
    ext g
    exact mem_conjugacySaturation_iff_completeModel_fixed M g
  rw [heq]
  exact isZariskiClosed_has_fixedPoint M.action M.complete

/-- The union of conjugates of any Borel is Zariski closed, including in a disconnected group. -/
public theorem isZariskiClosed_conjugacySaturation
    {B : ClosedSubgroup G} (hB : IsBorelSubgroup B) :
    IsZariskiClosed G (conjugacySaturation B) := by
  obtain ⟨C, hC, ⟨M⟩⟩ := BorelGeometricConjugacy.exists_borel_completeModel B hB
  obtain ⟨g, rfl⟩ := BorelGeometricConjugacy.conjugacy hC hB
  rw [conjugacySaturation_conjugate]
  exact isZariskiClosed_conjugacySaturation_of_completeModel M

end Theory.AlgebraicGroup.BorelElementCoverage
