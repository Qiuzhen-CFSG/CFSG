module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Fibre
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Geometry
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.FixedDecomposition
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.HomogeneousFibres.Scalars
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.HomogeneousFibres.NaturalCoordinates


/-!
# Correcting lifts into homogeneous displacement fibres

The common coordinate geometry supplies W ∩ U = 0, its full quotient-axis
image, K-invariance, and C_V(Q) = C_U(Q) ⊕ W. Equivariant projection then
reduces fibre surjectivity to the natural-plane realization calculation.
For every point on the actual quotient line, subtracting its realized
projected displacement gives a lift in the zero-adjoined fibre. The literal
`complement_of_fibre_covers` application constructs a KQ-complement.

The final exports construct the natural-plane coordinates from the
same-orientation marking and discharge the realization premise. Thus the
homogeneous branch supplies fibre surjectivity and a KQ-complement, retaining
only quadraticity and fixed lifts as independent source inputs. The argument
works over every binary field, including F₄; no degree restriction is needed.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.93–94. All vector-space constructions upstairs are over ZMod 2.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open QuasisimpleSource LargeFieldComplements.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F 3 ρ} (m : QuotientCoordinates d) (j : Fin 3)

/-- Fibre surjectivity reduced to realization of equivariant natural maps.
The correction is applied to each actual Levi-fixed quotient lift. -/
theorem homogeneous_fibre_covers_of_realization
    (hreal : NaturalDisplacementRealization ρ (m.K j) (m.Q j) d.space)
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j)
    (v : V) (hfixed : v ∈ fixedSpace ρ (m.K j))
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    m.line j ≤ (displacementFibre ρ (m.K j) (m.Q j)
      (displacementSpace ρ (m.Q j) hq v)).map d.space.toSubmodule.mkQ := by
  intro l hl
  obtain ⟨z, hzK, hz⟩ := hf hl
  obtain ⟨u, huN, _, hu⟩ := fixed_lift_correction ρ (m.K j) (m.Q j) d.space
    (displacementSpace ρ (m.Q j) hq v) hq (m.largeField_K_normalizes_Q j)
    (m.largeField_displacement_disjoint j hq v hv)
    (m.largeField_displacement_stable j hq v hfixed)
    (m.largeField_fixed_decomposition j (by decide) hq v hv) hreal z hzK
  refine ⟨z - u, hu, ?_⟩
  rw [map_sub, hz, show d.space.toSubmodule.mkQ u = 0 from
    (Submodule.Quotient.mk_eq_zero _).mpr huN, sub_zero]

/-- The literal coordinate complement application, with fibre surjectivity
proved by correcting lifts. Only natural-map realization remains explicit. -/
theorem homogeneous_coordinate_complement_of_realization
    (hreal : NaturalDisplacementRealization ρ (m.K j) (m.Q j) d.space)
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j)
    (v : V) (hfixed : v ∈ fixedSpace ρ (m.K j))
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.K j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
  exact complement_of_fibre_covers ρ (m.K j) (m.Q j) d.space
    (displacementSpace ρ (m.Q j) hq v) (m.axis j) (m.line j)
    (m.largeField_axis_isCompl_line j)
    (m.largeField_displacement_disjoint j hq v hv)
    (m.largeField_displacement_map j hq v hv)
    (m.largeField_displacement_stable j hq v hfixed)
    (displacementSpace_le_fixed ρ (m.Q j) hq v)
    (homogeneous_fibre_covers_of_realization m j hreal hq hf v hfixed hv)

/-- FixedLifts supplies the canonical vector for the complement construction.
This is conditional on the explicitly stated natural-map calculation. -/
theorem homogeneous_complement_of_realization
    (hreal : NaturalDisplacementRealization ρ (m.K j) (m.Q j) d.space)
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j) :
    ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.K j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
  obtain ⟨v, hvK, hv⟩ := m.exists_fixed_lineVector j hf
  exact homogeneous_coordinate_complement_of_realization m j hreal hq hf v hvK hv


/-- Actual coherent natural-plane coordinates discharge the realization
premise: every fixed lift of the unit vector has a fibre covering the line. -/
theorem homogeneous_fibre_covers_of_coordinates
    (c : NaturalPlaneCoordinates ρ (m.K j) (m.Q j) d.space F)
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j)
    (v : V) (hfixed : v ∈ fixedSpace ρ (m.K j))
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    m.line j ≤ (displacementFibre ρ (m.K j) (m.Q j)
      (displacementSpace ρ (m.Q j) hq v)).map d.space.toSubmodule.mkQ := by
  exact homogeneous_fibre_covers_of_realization m j (realization_of_marked_planes c)
    hq hf v hfixed hv

/-- The complement consumer of scalar rigidity, with the original quotient,
axis group, Levi, and submodule retained. Coordinate existence is explicit. -/
theorem homogeneous_complement_of_coordinates
    (c : NaturalPlaneCoordinates ρ (m.K j) (m.Q j) d.space F)
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j) :
    ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.K j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
  exact homogeneous_complement_of_realization m j (realization_of_marked_planes c) hq hf

/-- The homogeneous fibre covers the actual quotient line. The same-orientation
marking supplies the coherent coordinates, so neither natural-map realization
nor a complement is assumed. This includes F₄. -/
theorem homogeneous_fibre_covers
    (hmark : ∀ g, m.action.groupEquiv g =
      m.basisChange * d.natural.groupEquiv g * m.basisChange⁻¹)
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j)
    (v : V) (hfixed : v ∈ fixedSpace ρ (m.K j))
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    m.line j ≤ (displacementFibre ρ (m.K j) (m.Q j)
      (displacementSpace ρ (m.Q j) hq v)).map d.space.toSubmodule.mkQ := by
  obtain ⟨c⟩ := m.homogeneous_naturalPlaneCoordinates j hmark
  exact homogeneous_fibre_covers_of_coordinates m j c hq hf v hfixed hv

/-- The same-orientation KQ-complement in B.4.9(1), from quadraticity and
fixed lifts. All fibre and coordinate premises of the literal complement
construction are discharged; their independent source inputs remain explicit. -/
theorem homogeneous_complement
    (hmark : ∀ g, m.action.groupEquiv g =
      m.basisChange * d.natural.groupEquiv g * m.basisChange⁻¹)
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j) :
    ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.K j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
  obtain ⟨v, hvK, hv⟩ := m.exists_fixed_lineVector j hf
  exact complement_of_fibre_covers ρ (m.K j) (m.Q j) d.space
    (displacementSpace ρ (m.Q j) hq v) (m.axis j) (m.line j)
    (m.largeField_axis_isCompl_line j)
    (m.largeField_displacement_disjoint j hq v hv)
    (m.largeField_displacement_map j hq v hv)
    (m.largeField_displacement_stable j hq v hvK)
    (displacementSpace_le_fixed ρ (m.Q j) hq v)
    (homogeneous_fibre_covers m j hmark hq hf v hvK hv)

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
