module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Assembly
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality

/-!
# The completed geometry on the graph-twisted exterior cube

The complementary-wedge equivalence intertwines the actual exterior actions
along inverse transpose. Applying it to the completed square calculations
gives the two cube orbits, the involution displacement ranks, the four marked
parabolic stabilizers and the fixed space of the graph image of R₆. Invariant
sections and their literal quotient maps are transported by `cubeSectionEquiv`,
re-exported from `Duality`.

Source: Aschbacher–Smith §12.5, printed pp.816–821/PDF pp.833–838, for the
exterior models in I.1.6(7). Recognition of an arbitrary irreducible module as
one of these two exterior models remains with the source classification owner.
-/

public section

namespace Representation.SL5ExteriorSquare.Duality
open SL5TenDimensional

/-- The two square point representatives give the two cube vector orbits,
with the prescribed complementary-basis and graph marking. -/
theorem cube_orbits_exactly_one (v : ExteriorModule 3) (hv : v ≠ 0) :
    ((∃ g : Group, exteriorAction 3 g (hodge.symm decomposable) = v) ∧
      ¬ ∃ g : Group, exteriorAction 3 g (hodge.symm nondecomposable) = v) ∨
    ((∃ g : Group, exteriorAction 3 g (hodge.symm nondecomposable) = v) ∧
      ¬ ∃ g : Group, exteriorAction 3 g (hodge.symm decomposable) = v) := by
  have h := exterior_orbits_exactly_one (hodge v) (hodge.map_ne_zero_iff.mpr hv)
  rw [cube_orbit_iff, cube_orbit_iff] at h
  simpa only [LinearEquiv.symm_apply_apply] using h

/-- Every involution on the cube has displacement rank three or four. -/
theorem cube_involution_displacement_ranks (g : Group) (hne : g ≠ 1) (hg : g * g = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (cubeDisplacement g)) = 3 ∨
      Module.finrank (ZMod 2) (LinearMap.range (cubeDisplacement g)) = 4 := by
  have hne' : graph g ≠ 1 := by
    intro h
    exact hne (graph.injective (h.trans (map_one graph).symm))
  have hg' : graph g * graph g = 1 := by rw [← map_mul, hg, map_one]
  have hr := cube_displacement_rank (graph g)
  rw [graph_involutive] at hr
  rcases involution_displacement_ranks (graph g) hne' hg' with h | h
  · exact Or.inl (hr.trans h.2)
  · exact Or.inr (hr.trans h.2)


/-- The fixed-space calculation uses the graph image of R₆ on the cube. -/
theorem cube_radicalSix_fixedSpace :
    BinaryOffender.fixedSpace (exteriorAction 3)
      ((parabolicResidualTwoCore 4).map graph.toMonoidHom) = cubeSubspace V₆ := by
  rw [BinaryOffender.fixedSpace, ← cubeSubspace_subgroup_fixed]
  change cubeSubspace (BinaryOffender.fixedSpace (exteriorAction 2)
    (parabolicResidualTwoCore 4)) = cubeSubspace V₆
  rw [radicalSix_fixedSpace_and_commutator.1]

/-- All four source stabilizers transfer with the actual graph-marked parabolics. -/
theorem cube_parabolic_stabilizers :
    subspaceStabilizer (exteriorAction 3) (cubeSubspace V₁) =
      (parabolic 2).map graph.toMonoidHom ∧
    subspaceStabilizer (exteriorAction 3) (cubeSubspace V₃) =
      (parabolic 3).map graph.toMonoidHom ∧
    subspaceStabilizer (exteriorAction 3) (cubeSubspace V₄) =
      (parabolic 1).map graph.toMonoidHom ∧
    subspaceStabilizer (exteriorAction 3) (cubeSubspace V₆) =
      (parabolic 4).map graph.toMonoidHom := by
  simp only [← cube_subspaceStabilizer, exteriorStabilizer_V₁_eq_parabolic,
    exteriorStabilizer_V₃_eq_parabolic, exteriorStabilizer_V₄_eq_parabolic,
    exteriorStabilizer_V₆_eq_parabolic, and_self]

end Representation.SL5ExteriorSquare.Duality
