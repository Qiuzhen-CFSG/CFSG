module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Geometry

/-!
# The full axis-group fixed space

The quotient fixed space is exactly its coordinate axis. Surjectivity of
the displacement space onto this axis gives
`C_V(Q) = (U ∩ C_V(Q)) + W`; the intersection of the two summands is zero
by `largeField_displacement_disjoint`. This is the common decomposition
used by the two orientations on printed pp.93–94 of Aschbacher–Smith B.4.9.
The argument retains the literal quotient by the original U.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
open QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ} (m : QuotientCoordinates d) (j : Fin n)
namespace QuotientCoordinates

theorem largeField_quotient_fixed_eq_axis (hn : 2 ≤ n) :
    fixedSpace d.space.quotientRepresentation (m.Q j) = m.axis j := by
  apply le_antisymm
  · intro z hz
    apply (m.largeField_mem_axis j z).mpr
    have hfix : m.action.linearEquiv z ∈
        fixedSpace (linearNatural F n) (hyperplaneCentralizer F n j) := by
      intro g
      let x := m.action.groupEquiv.symm g
      have hx : x ∈ m.Q j := by
        apply (m.largeField_mem_Q j x).mpr
        simpa only [x, MulEquiv.apply_symm_apply] using g.property
      have hh := congrArg m.action.linearEquiv (hz ⟨x, hx⟩)
      change m.action.linearEquiv (d.space.quotientRepresentation x z) = _ at hh
      rw [m.action.intertwines] at hh
      change linearNatural F n g (m.action.linearEquiv z) = m.action.linearEquiv z
      simpa only [x, MulEquiv.apply_symm_apply] using hh
    rw [subgroup_fixedSpace F n j le_rfl
      (hyperplaneCentralizer_elementary F n j hn).1] at hfix
    exact hfix
  · intro z hz x
    exact x.property.2 z hz

/-- The entire fixed space, not just the displacement image, splits over
its intersection with the original natural submodule. -/
theorem largeField_fixed_decomposition (hn : 2 ≤ n)
    (hq : IsQuadratic ρ (m.Q j)) (v : V)
    (hv : d.space.toSubmodule.mkQ v = m.lineVector j) :
    fixedSpace ρ (m.Q j) = (d.space.toSubmodule ⊓ fixedSpace ρ (m.Q j)) ⊔
      displacementSpace ρ (m.Q j) hq v := by
  have hW := displacementSpace_le_fixed ρ (m.Q j) hq v
  apply le_antisymm
  · intro z hz
    have hzq : d.space.toSubmodule.mkQ z ∈ m.axis j := by
      rw [← m.largeField_quotient_fixed_eq_axis j hn]
      intro x
      exact congrArg d.space.toSubmodule.mkQ (hz x)
    rw [← m.largeField_displacement_map j hq v hv] at hzq
    obtain ⟨w, hw, hwz⟩ := hzq
    have hnz : z - w ∈ d.space.toSubmodule := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change d.space.toSubmodule.mkQ (z - w) = 0
      rw [map_sub, hwz, sub_self]
    exact Submodule.mem_sup.mpr ⟨z - w, ⟨hnz, (fixedSpace ρ (m.Q j)).sub_mem hz (hW hw)⟩,
      w, hw, sub_add_cancel _ _⟩
  · exact sup_le inf_le_right hW

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
