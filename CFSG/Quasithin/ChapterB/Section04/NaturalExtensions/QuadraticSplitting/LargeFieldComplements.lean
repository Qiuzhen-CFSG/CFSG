module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Fibre
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.FixedDecomposition
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.HomogeneousFibres
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.OppositeFibres

/-!
# Local complements from displacement fibres in B.4.9(1)

The quotient shear calculation proves that the displacement space of a
Levi-fixed lift maps isomorphically onto the quotient axis. A binary linear
section through its zero-adjoined displacement fibre then supplies a
KQ-complement to the original natural submodule, in either orientation.

For SL₃, the recorded quotient marking selects one of the two source
branches. In the same orientation, scalar rigidity on the natural Levi
plane corrects fixed lifts into the fibre. In the opposite orientation,
W = [C_V(Q),K], and every K-fixed lift lies in the fibre. Thus the fibre
surjectivity premise in the initial general constructions is discharged.
The opposite branch also supplies the stronger K₀Q-invariant complement,
exported as `opposite_marked_coordinate_fullLevi_complement`, using the
actual odd scalar torus and an averaged binary section.

The final local complement needs only quadraticity and fixed lifts. It
works over every binary field, including F₄. The earlier source inputs
and the passage from a local complement to a G-complement remain with the
enclosing B.4.9(1) assembly.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.93–94.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ} (m : QuotientCoordinates d) (j : Fin n)

/-- Literal application to `DoubleNatural`, with disjointness, spanning of
the quotient axis, and Levi invariance all proved from the coordinate action.
Only surjectivity of the zero-adjoined fibre onto the quotient line remains. -/
theorem largeField_coordinate_complement_of_fibre
    (hq : IsQuadratic ρ (m.Q j)) (v : V)
    (hfixed : v ∈ fixedSpace ρ (m.K j))
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j)
    (hfibre : m.line j ≤
      (displacementFibre ρ (m.K j) (m.Q j)
        (displacementSpace ρ (m.Q j) hq v)).map d.space.toSubmodule.mkQ) :
    ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.K j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
  exact complement_of_fibre_covers ρ (m.K j) (m.Q j) d.space
    (displacementSpace ρ (m.Q j) hq v) (m.axis j) (m.line j)
    (m.largeField_axis_isCompl_line j)
    (m.largeField_displacement_disjoint j hq v hv)
    (m.largeField_displacement_map j hq v hv)
    (m.largeField_displacement_stable j hq v hfixed)
    (displacementSpace_le_fixed ρ (m.Q j) hq v) hfibre

/-- The source fixed-lift input supplies the vector used by the construction.
The remaining fibre premise must be discharged in each quotient orientation. -/
theorem largeField_complement_of_fixedLifts_and_fibres
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j)
    (hfibre : ∀ v : V, v ∈ fixedSpace ρ (m.K j) →
      d.space.toSubmodule.mkQ v = m.lineVector j →
      m.line j ≤ (displacementFibre ρ (m.K j) (m.Q j)
        (displacementSpace ρ (m.Q j) hq v)).map d.space.toSubmodule.mkQ) :
    ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.K j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
  obtain ⟨v, hvK, hv⟩ := m.exists_fixed_lineVector j hf
  exact largeField_coordinate_complement_of_fibre m j hq v hvK hv (hfibre v hvK hv)

section ThreeDimensional
variable {d : DoubleNatural F 3 ρ} (m : QuotientCoordinates d) (j : Fin 3)

/-- The zero-adjoined displacement fibre covers the actual quotient line
in both orientations. No fibre, scalar-action, or upstairs splitting premise
remains beyond quadraticity and fixed lifts. -/
theorem largeField_fibre_covers
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j)
    (v : V) (hfixed : v ∈ fixedSpace ρ (m.K j))
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    m.line j ≤ (displacementFibre ρ (m.K j) (m.Q j)
      (displacementSpace ρ (m.Q j) hq v)).map d.space.toSubmodule.mkQ := by
  rcases m.marking with hsame | hopposite
  · exact homogeneous_fibre_covers m j hsame hq hf v hfixed hv
  · exact opposite_marked_coordinate_fibre_covers m j hopposite hq hf v hfixed hv

/-- The larger-field local construction of B.4.9(1) for the original
`DoubleNatural` submodule and its literal quotient groups. The construction
in fact works over every binary field; no field structure on V is used.
Quadraticity and fixed lifts are the independent earlier-source inputs. -/
theorem largeField_complement_of_fixedLifts
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j) :
    ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.K j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
  exact largeField_complement_of_fixedLifts_and_fibres m j hq hf
    (largeField_fibre_covers m j hq hf)

end ThreeDimensional

/-- Application to the full source family: degree greater than one forces
the SL₃ branch. This discharges the larger-field local-complement step,
with quadraticity and fixed lifts still supplied by their source producers. -/
theorem largeField_sourceFamily_complement
    (hfamily : SourceFamily F n) (hdegree : 1 < F.degree)
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j) :
    ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.K j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
  rcases hfamily with rfl | ⟨hbinary, _⟩
  · exact largeField_complement_of_fixedLifts m j hq hf
  · omega

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
