module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Fibre
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Geometry
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.FixedDecomposition
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.OppositeFibres.Commutators
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.OppositeFibres.Averaging
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.OppositeFibres.Models
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.OppositeFibres.CoordinateFacts
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.OppositeFibres.TorusLevi

/-!
# Opposite-orientation displacement fibres and the odd torus

Group commutator generation identifies W with [C_V(Q),K]. The actual
scalar torus normalizes both groups, so W is torus-invariant. Averaging a
binary section through C_V(K) then constructs W + range(section), with
its original quotient map and invariance under KQH.

The opposite marking discharges C_U(Q) ≤ C_V(K); root commutators give
Q = [K,Q]. The torus is exactly C_{K₀}(K), and K₀ = KH. The marked
applications below discharge all three matrix premises and retain the
explicit complement W + range(section). Only quadraticity and fixed lifts
remain as permitted earlier-source inputs to this local branch of B.4.9(1).
No field-degree restriction is needed for this construction, so it includes
F₄. The earlier-source inputs and passage to a G-complement belong to the
enclosing source assembly.

Source: Aschbacher–Smith B.4.9(1), printed p.93 (PDF p.104), combined
manuscript of 1 March 2004.
-/

public section
open Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F 3 ρ} (m : QuotientCoordinates d) (j : Fin 3)

/-- The torus preserves every canonical displacement space, via its
identification with the full fixed-space commutator. -/
theorem opposite_coordinate_torus_stable
    (hq : IsQuadratic ρ (m.Q j))
    (hU : d.space.toSubmodule ⊓ fixedSpace ρ (m.Q j) ≤ fixedSpace ρ (m.K j))
    (hgen : ⁅m.K j,m.Q j⁆ = m.Q j)
    (v : V) (hfixed : v ∈ fixedSpace ρ (m.K j))
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    m.oppositeTorus j ≤ subspaceStabilizer ρ (displacementSpace ρ (m.Q j) hq v) := by
  rw [← opposite_coordinate_fixed_commutator m j hq hU hgen v hfixed hv]
  exact opposite_commutator_normalizer ρ (m.K j) (m.Q j) (m.oppositeTorus j)
    ((m.oppositeTorus_le_fullLevi j).trans (m.oppositeFullLevi_normalizes_K j))
    ((m.oppositeTorus_le_fullLevi j).trans (m.oppositeFullLevi_normalizes_Q j))

/-- Actual DoubleNatural application of the averaged fibre section, retaining
invariance under the full Levi and axis group. Only the named matrix facts
remain in addition to the permitted quadraticity and fixed-lift inputs. -/
theorem opposite_coordinate_fullLevi_complement_of_matrix_facts
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j)
    (hU : d.space.toSubmodule ⊓ fixedSpace ρ (m.Q j) ≤ fixedSpace ρ (m.K j))
    (hgen : ⁅m.K j,m.Q j⁆ = m.Q j)
    (hLevi : m.oppositeFullLevi j ≤ m.K j ⊔ m.oppositeTorus j) :
    ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.oppositeFullLevi j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
  obtain ⟨v,hfixed,hv⟩ := m.exists_fixed_lineVector j hf
  have hH := m.oppositeTorus_le_fullLevi j
  have hHL : m.oppositeTorus j ≤
      subspaceStabilizer d.space.quotientRepresentation (m.line j) :=
    hH.trans inf_le_right
  obtain ⟨C,hC,hstab⟩ := opposite_odd_complement ρ (m.K j) (m.oppositeTorus j)
    (m.Q j) d.space (displacementSpace ρ (m.Q j) hq v) (m.axis j) (m.line j)
    (m.largeField_axis_isCompl_line j)
    (m.largeField_displacement_disjoint j hq v hv)
    (m.largeField_displacement_map j hq v hv)
    (m.largeField_displacement_stable j hq v hfixed)
    (displacementSpace_le_fixed ρ (m.Q j) hq v)
    (opposite_coordinate_torus_stable m j hq hU hgen v hfixed hv) hHL
    (hH.trans (m.oppositeFullLevi_normalizes_K j)) hf
    (opposite_coordinate_fixedSpace_le_fibre m j hq hU hgen v hfixed hv)
    (m.oppositeTorus_odd j)
  refine ⟨C,hC,le_trans ?_ hstab⟩
  calc
    m.oppositeFullLevi j ⊔ m.Q j ≤ (m.K j ⊔ m.oppositeTorus j) ⊔ m.Q j :=
      sup_le_sup hLevi le_rfl
    _ = (m.K j ⊔ m.Q j) ⊔ m.oppositeTorus j := by ac_rfl

/-- Actual commutator generation of Q gives W = [W,K] for every K-fixed
vector. This step is independent of the orientation of the original U. -/
theorem opposite_coordinate_displacement_commutator
    (hq : IsQuadratic ρ (m.Q j)) (v : V)
    (hfixed : v ∈ fixedSpace ρ (m.K j)) :
    subspaceCommutator ρ (displacementSpace ρ (m.Q j) hq v) (m.K j) =
      displacementSpace ρ (m.Q j) hq v := by
  exact opposite_displacement_eq_commutator ρ (m.K j) (m.Q j) hq v hfixed
    (m.largeField_K_normalizes_Q j) (m.axis_commutator_eq j (by decide))

/-- The canonical displacement space is [C_V(Q),K], with fixation of the
original C_U(Q) proved using the recorded opposite marking. -/
theorem opposite_marked_coordinate_fixed_commutator
    (hop : ∀ g, m.action.groupEquiv g = m.basisChange *
      Matrix.SpecialLinearGroup.transpose ((d.natural.groupEquiv g)⁻¹) * m.basisChange⁻¹)
    (hq : IsQuadratic ρ (m.Q j))
    (v : V) (hfixed : v ∈ fixedSpace ρ (m.K j))
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    subspaceCommutator ρ (fixedSpace ρ (m.Q j)) (m.K j) =
      displacementSpace ρ (m.Q j) hq v := by
  exact opposite_coordinate_fixed_commutator m j hq
    (m.opposite_original_fixedSpace_le_K j hop)
    (m.axis_commutator_eq j (by decide)) v hfixed hv

/-- The actual odd scalar torus preserves W in the opposite orientation;
no scalar action on the original binary extension is assumed. -/
theorem opposite_marked_coordinate_torus_stable
    (hop : ∀ g, m.action.groupEquiv g = m.basisChange *
      Matrix.SpecialLinearGroup.transpose ((d.natural.groupEquiv g)⁻¹) * m.basisChange⁻¹)
    (hq : IsQuadratic ρ (m.Q j))
    (v : V) (hfixed : v ∈ fixedSpace ρ (m.K j))
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    m.oppositeTorus j ≤ subspaceStabilizer ρ (displacementSpace ρ (m.Q j) hq v) := by
  exact opposite_coordinate_torus_stable m j hq
    (m.opposite_original_fixedSpace_le_K j hop)
    (m.axis_commutator_eq j (by decide)) v hfixed hv

/-- An H-invariant binary section through the canonical fibre, together with
the explicit K₀Q-complement W + range(section). The section uses the original
quotient by U; averaging supplies its invariant range. -/
theorem opposite_marked_coordinate_fibreSection
    (hop : ∀ g, m.action.groupEquiv g = m.basisChange *
      Matrix.SpecialLinearGroup.transpose ((d.natural.groupEquiv g)⁻¹) * m.basisChange⁻¹)
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j)
    (v : V) (hfixed : v ∈ fixedSpace ρ (m.K j))
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    ∃ t : m.line j →ₗ[ZMod 2] V,
      (∀ z : m.line j, d.space.toSubmodule.mkQ (t z) = z) ∧
      (∀ z : m.line j, t z ∈ displacementFibre ρ (m.K j) (m.Q j)
        (displacementSpace ρ (m.Q j) hq v)) ∧
      m.oppositeTorus j ≤ subspaceStabilizer ρ (LinearMap.range t) ∧
      IsCompl d.space.toSubmodule
        (displacementSpace ρ (m.Q j) hq v ⊔ LinearMap.range t) ∧
      m.oppositeFullLevi j ⊔ m.Q j ≤ subspaceStabilizer ρ
        (displacementSpace ρ (m.Q j) hq v ⊔ LinearMap.range t) := by
  have hH := m.oppositeTorus_le_fullLevi j
  obtain ⟨t, ht, htK, htH⟩ := opposite_fixed_section ρ (m.K j) (m.oppositeTorus j)
    d.space (m.line j) (hH.trans inf_le_right)
    (hH.trans (m.oppositeFullLevi_normalizes_K j)) hf (m.oppositeTorus_odd j)
  have htf (z : m.line j) :=
    opposite_marked_coordinate_fixedSpace_le_fibre m j hop hq v hfixed hv (htK z)
  have hC := fibreSection_complement ρ (m.K j) (m.Q j) d.space
    (displacementSpace ρ (m.Q j) hq v) (m.axis j) (m.line j)
    (m.largeField_axis_isCompl_line j)
    (m.largeField_displacement_disjoint j hq v hv)
    (m.largeField_displacement_map j hq v hv)
    (m.largeField_displacement_stable j hq v hfixed)
    (displacementSpace_le_fixed ρ (m.Q j) hq v) t ht htf
  refine ⟨t, ht, htf, htH, hC.1, ?_⟩
  have hCH := subspaceStabilizer_sup ρ
    (opposite_marked_coordinate_torus_stable m j hop hq v hfixed hv) htH
  rw [m.oppositeFullLevi_eq_sup j]
  exact sup_le (sup_le (le_sup_left.trans hC.2) hCH) (le_sup_right.trans hC.2)

/-- The opposite-orientation local conclusion of B.4.9(1) for the literal
DoubleNatural extension. All matrix premises have been discharged; only
the source's earlier quadraticity and fixed-lift inputs remain. -/
theorem opposite_marked_coordinate_fullLevi_complement
    (hop : ∀ g, m.action.groupEquiv g = m.basisChange *
      Matrix.SpecialLinearGroup.transpose ((d.natural.groupEquiv g)⁻¹) * m.basisChange⁻¹)
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j) :
    ∃ C : Submodule (ZMod 2) V, IsCompl d.space.toSubmodule C ∧
      m.oppositeFullLevi j ⊔ m.Q j ≤ subspaceStabilizer ρ C := by
  exact opposite_coordinate_fullLevi_complement_of_matrix_facts m j hq hf
    (m.opposite_original_fixedSpace_le_K j hop)
    (m.axis_commutator_eq j (by decide)) (m.oppositeFullLevi_le_sup j)

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
