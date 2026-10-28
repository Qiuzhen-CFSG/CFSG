module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Core
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Transport
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.Basic

/-!
# Geometry transport between the two binary SL₅ exterior modules

The complementary-basis equivalence transports the square's geometry to the cube
along the inverse-transpose automorphism. All groups are determinant-one matrix
groups, all vector spaces are actual exterior powers, and sections use the
literal submodule quotient maps. In particular the square's displacement ranks
three and four and its first fixed space transfer to the cube.

This supplies the change of model implicit in Aschbacher--Smith §12.5, printed
pp.816–821/PDF pp.833–838, for the two exterior models in I.1.6(7). Identifying an
arbitrary ten-dimensional irreducible with one of these models is a separate
source theorem and is not assumed here.
-/

@[expose] public section
namespace Representation.SL5ExteriorSquare.Duality
open SL5TenDimensional

/-- The corresponding cube subspace, in the complementary wedge basis. -/
noncomputable def cubeSubspace (U : Submodule (ZMod 2) V) :
    Submodule (ZMod 2) (ExteriorModule 3) := U.map hodge.symm.toLinearMap

/-- Actual displacement on the exterior cube. -/
noncomputable def cubeDisplacement (g : Group) :
    ExteriorModule 3 →ₗ[ZMod 2] ExteriorModule 3 := exteriorAction 3 g - LinearMap.id

/-- Actual fixed space on the exterior cube. -/
noncomputable def cubeFixedSpace (g : Group) : Submodule (ZMod 2) (ExteriorModule 3) :=
  LinearMap.ker (cubeDisplacement g)

/-- Fixed spaces transport at the graph-marked group element. -/
theorem cubeSubspace_fixedSpace (g : Group) :
    cubeSubspace (fixedSpace g) = cubeFixedSpace (graph g) :=
  EquivariantGeometry.map_fixed_kernel (exteriorAction 2) (exteriorAction 3)
    graph hodge.symm hodge_symm_action g

/-- The literal displacement range transports under the same map. -/
theorem cubeSubspace_displacement_range (g : Group) :
    cubeSubspace (LinearMap.range (displacement g)) =
      LinearMap.range (cubeDisplacement (graph g)) :=
  EquivariantGeometry.map_displacement_range (exteriorAction 2) (exteriorAction 3)
    graph hodge.symm hodge_symm_action g

theorem cube_displacement_rank (g : Group) :
    Module.finrank (ZMod 2) (LinearMap.range (cubeDisplacement (graph g))) =
      Module.finrank (ZMod 2) (LinearMap.range (displacement g)) :=
  (EquivariantGeometry.displacement_rank (exteriorAction 2) (exteriorAction 3)
    graph hodge.symm hodge_symm_action g).symm

/-- Fixed-space dimensions agree at corresponding actors. -/
theorem cube_fixed_rank (g : Group) :
    Module.finrank (ZMod 2) (cubeFixedSpace (graph g)) =
      Module.finrank (ZMod 2) (fixedSpace g) :=
  (EquivariantGeometry.fixed_rank (exteriorAction 2) (exteriorAction 3)
    graph hodge.symm hodge_symm_action g).symm

/-- Subspace dimensions are preserved by the actual complementary-basis map. -/
theorem cubeSubspace_finrank (U : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) (cubeSubspace U) = Module.finrank (ZMod 2) U :=
  (hodge.symm.submoduleMap U).finrank_eq.symm

/-- The source fixed-space calculation for the cube representative. -/
theorem cubeFixedSpace_graph_j₁ :
    cubeFixedSpace (graph j₁) = cubeSubspace V₄ ⊔ cubeSubspace V₆ := by
  rw [← cubeSubspace_fixedSpace, fixedSpace_j₁]
  exact Submodule.map_sup _ _ _

/-- The two source displacement ranks also hold on the graph-twisted cube. -/
theorem cube_involution_ranks :
    Module.finrank (ZMod 2) (LinearMap.range (cubeDisplacement (graph j₁))) = 3 ∧
    Module.finrank (ZMod 2) (LinearMap.range (cubeDisplacement (graph j₂))) = 4 := by
  rw [cube_displacement_rank, cube_displacement_rank]
  exact ⟨finrank_displacement_j₁, finrank_displacement_j₂⟩

/-- Subgroup fixed spaces, using the actual image of the subgroup under graph. -/
theorem cubeSubspace_subgroup_fixed (A : Subgroup Group) :
    cubeSubspace (Representation.invariants ((exteriorAction 2).comp A.subtype)) =
      Representation.invariants
        ((exteriorAction 3).comp (A.map graph.toMonoidHom).subtype) :=
  EquivariantGeometry.map_subgroup_fixed (exteriorAction 2) (exteriorAction 3)
    graph hodge.symm hodge_symm_action A

/-- Stabilizers are transported by graph, not identified as the same subgroup. -/
theorem cube_subspaceStabilizer (U : Submodule (ZMod 2) V) :
    (exteriorStabilizer U).map graph.toMonoidHom =
      subspaceStabilizer (exteriorAction 3) (cubeSubspace U) :=
  EquivariantGeometry.map_stabilizer (exteriorAction 2) (exteriorAction 3)
    graph hodge.symm hodge_symm_action U

/-- Orbit transport agrees with the geometry's existing square orbit relation. -/
theorem cube_orbit_iff (v w : V) :
    InExteriorOrbit v w ↔
      ∃ g : Group, exteriorAction 3 g (hodge.symm v) = hodge.symm w :=
  EquivariantGeometry.orbit_iff (exteriorAction 2) (exteriorAction 3)
    graph hodge.symm hodge_symm_action v w

/-- The actual bijection on each square orbit and its corresponding cube orbit. -/
noncomputable def cubeOrbitEquiv (v : V) :
    Set.range (fun g => exteriorAction 2 g v) ≃
      Set.range (fun g => exteriorAction 3 g (hodge.symm v)) :=
  EquivariantGeometry.orbitEquiv (exteriorAction 2) (exteriorAction 3)
    graph hodge.symm hodge_symm_action v

/-- Orbit cardinalities transport through the prescribed orbit bijection. -/
theorem cube_orbit_card (v : V) :
    Nat.card (Set.range (fun g => exteriorAction 2 g v)) =
      Nat.card (Set.range (fun g => exteriorAction 3 g (hodge.symm v))) :=
  EquivariantGeometry.orbit_card (exteriorAction 2) (exteriorAction 3)
    graph hodge.symm hodge_symm_action v

/-- A lower subspace is the literal image inside the transported upper space. -/
theorem cube_lower_subspace_image (U L : Submodule (ZMod 2) V) :
    (L.comap U.subtype).map (hodge.symm.submoduleMap U).toLinearMap =
      (cubeSubspace L).comap (cubeSubspace U).subtype :=
  EquivariantGeometry.lower_subspace_image hodge.symm U L

/-- Equivariance on each actual subgroup and its graph image. -/
noncomputable def cubeSubgroupEquiv (A : Subgroup Group) :
    Representation.Equiv ((exteriorAction 2).comp A.subtype)
      (((exteriorAction 3).comp (A.map graph.toMonoidHom).subtype).comp
        (graph.subgroupMap A).toMonoidHom) :=
  EquivariantGeometry.restrictionEquiv (exteriorAction 2) (exteriorAction 3)
    graph hodge.symm hodge_symm_action A

/-- Invariant sections of any subgroup, in particular the source parabolics,
transfer with both the quotient map and group marking fixed. -/
noncomputable def cubeSectionEquiv (A : Subgroup Group) (U : Submodule (ZMod 2) V)
    (hU : ∀ g : A, U ≤ U.comap (exteriorAction 2 g)) (B : Submodule (ZMod 2) U)
    (hB : ∀ g : A, B ≤ B.comap
      (Representation.subrepresentation ((exteriorAction 2).comp A.subtype) U hU g)) :=
  EquivariantGeometry.subquotientEquiv ((exteriorAction 2).comp A.subtype)
    ((exteriorAction 3).comp (A.map graph.toMonoidHom).subtype)
    (graph.subgroupMap A) hodge.symm (fun g v => hodge_symm_action g v) U hU B hB

/-- The section map sends the class of u to the class of its complement image. -/
theorem cubeSectionEquiv_mk (A : Subgroup Group) (U : Submodule (ZMod 2) V)
    (hU : ∀ g : A, U ≤ U.comap (exteriorAction 2 g)) (B : Submodule (ZMod 2) U)
    (hB : ∀ g : A, B ≤ B.comap
      (Representation.subrepresentation ((exteriorAction 2).comp A.subtype) U hU g)) (v : U) :
    cubeSectionEquiv A U hU B hB (Submodule.Quotient.mk v) =
      (Submodule.Quotient.mk (hodge.symm.submoduleMap U v) :
        cubeSubspace U ⧸ B.map (hodge.symm.submoduleMap U).toLinearMap) := rfl

end Representation.SL5ExteriorSquare.Duality
