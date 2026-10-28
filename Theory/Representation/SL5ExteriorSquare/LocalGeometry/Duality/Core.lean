module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Coordinates
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Tactic.FinCases

/-!
# Complementary-basis duality for the binary SL₅ exterior powers

The Hodge map sends each standard three-fold wedge to the two-fold wedge on
its complementary set of indices. Its intertwining orientation is
`hodge (Λ³(g) v) = Λ²((g⁻¹)ᵀ) (hodge v)`.

We prove the complementary-minor formula first on elementary transvections,
using the explicit two- and three-by-three determinant formulas. This single
finite calculation is checked by the kernel, in separate generator cases.
Generation of SL₅(2) then proves equivariance for every group element, and
recovering coordinates gives the full complementary-minor identity. The map is
an equivalence of actual exterior modules, not a dimension-based identification.

The coordinate calculation follows `ExteriorVanishing/Reduction.lean` and
`ExteriorVanishing/CubeRelations.lean`. The graph automorphism is the existing
inverse-transpose automorphism of the determinant-one matrix group.

Source: Aschbacher--Smith, §12.5, printed pp.816–821/PDF pp.833–838, and the
exterior models used in I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

open scoped BigOperators
namespace Representation.SL5ExteriorSquare.Duality
open SL5TenDimensional

/-- The actual inverse-transpose automorphism of SL₅(2). -/
abbrev graph : Group ≃* Group := BinaryLinear.OuterCyclic.graphSL 5

/-- Matrix formula, with inverse taken in the determinant-one group. -/
theorem graph_apply (g : Group) :
    (graph g).val = (g⁻¹).val.transpose := by
  exact (Matrix.adjugate_transpose g.val).symm

/-- The graph automorphism has square one. -/
theorem graph_involutive (g : Group) : graph (graph g) = g :=
  graph.left_inv g

/-- Inverse transpose swaps the source and target of each binary transvection. -/
theorem graph_elementary (i j : Fin 5) : graph (elementary i j) = elementary j i := by
  apply Subtype.ext
  rw [graph_apply]
  have hi : (elementary i j)⁻¹ = elementary i j :=
    inv_eq_of_mul_eq_one_right (elementary_square i j)
  rw [hi]
  by_cases hij : i = j
  · subst j; simp
  · simp [elementary, hij, Ne.symm hij, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.transpose_add, Matrix.transpose_single]

/-- Complementary subsets, with cube indices as source. -/
def complement : ExteriorIndex 3 ≃ ExteriorIndex 2 := Set.powersetCard.compl (by decide)

/-- The index map is literally set complementation. -/
@[simp] theorem complement_coe (s : ExteriorIndex 3) :
    (complement s : Finset (Fin 5)) = (s : Finset (Fin 5))ᶜ := rfl

/-- The complementary-basis map from the cube to the square. -/
noncomputable def hodge : ExteriorModule 3 ≃ₗ[ZMod 2] ExteriorModule 2 :=
  ((exteriorCoordinates 3).trans
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) complement.symm)).trans
      (exteriorCoordinates 2).symm

/-- Coordinates of the complementary-basis map. -/
theorem hodge_coordinates (v : ExteriorModule 3) (s : ExteriorIndex 2) :
    exteriorCoordinates 2 (hodge v) s = exteriorCoordinates 3 v (complement.symm s) := by
  simp [hodge, LinearEquiv.funCongrLeft]

/-- Each standard wedge goes to its complementary standard wedge. -/
theorem hodge_basis (s : ExteriorIndex 3) :
    hodge (exteriorBasis 3 s) = exteriorBasis 2 (complement s) := by
  apply (exteriorCoordinates 2).injective
  funext t
  rw [hodge_coordinates]
  simp only [exteriorCoordinates, Module.Basis.equivFun_self]
  congr 1
  exact propext (Equiv.eq_symm_apply complement)

private def triple (s : Fin 10) : Fin 3 ↪o Fin 5 :=
  OrderEmbedding.ofStrictMono
    (![![2,3,4], ![1,3,4], ![1,2,4], ![1,2,3], ![0,3,4],
       ![0,2,4], ![0,2,3], ![0,1,4], ![0,1,3], ![0,1,2]] s)
    (by revert s; decide)

private theorem complement_index (s : Fin 10) :
    complement.symm (index s) = Set.powersetCard.ofFinEmbEquiv (triple s) := by
  fin_cases s <;> decide

private theorem complement_index_order (s : Fin 10) :
    Set.powersetCard.ofFinEmbEquiv.symm (complement.symm (index s)) = triple s := by
  rw [complement_index]
  exact _root_.Equiv.symm_apply_apply _ _

private theorem elementary_entry (i j a b : Fin 5) : (elementary i j).val a b =
    (if a = b then 1 else 0) + (if i ≠ j ∧ a = i ∧ b = j then 1 else 0) := by
  by_cases hij : i = j
  · subst j; simp [elementary, Matrix.one_apply]
  · simp [elementary, hij, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

private theorem elementary_complementary_minor (i j : Fin 5) (s t : ExteriorIndex 2) :
    exteriorMatrix 3 (elementary i j) (complement.symm s) (complement.symm t) =
      exteriorMatrix 2 (elementary j i) s t := by
  obtain ⟨s, rfl⟩ := index_bijective.surjective s
  obtain ⟨t, rfl⟩ := index_bijective.surjective t
  simp only [exteriorMatrix, complement_index_order,
    index_order, Matrix.det_fin_three, Matrix.det_fin_two, Matrix.of_apply, elementary_entry]
  fin_cases i <;> fin_cases j <;> revert s t <;> decide +kernel

private theorem hodge_elementary (i j : Fin 5) (v : ExteriorModule 3) :
    hodge (exteriorAction 3 (elementary i j) v) =
      exteriorAction 2 (graph (elementary i j)) (hodge v) := by
  apply (exteriorCoordinates 2).injective
  funext s
  rw [hodge_coordinates, exteriorCoordinates_action, exteriorCoordinates_action,
    graph_elementary]
  simp only [Matrix.mulVec, dotProduct, hodge_coordinates]
  rw [← complement.symm.sum_comp]
  simp only [elementary_complementary_minor]

/-- Equivariance from the exterior cube to the graph-twisted exterior square. -/
theorem hodge_action (g : Group) (v : ExteriorModule 3) :
    hodge (exteriorAction 3 g v) = exteriorAction 2 (graph g) (hodge v) := by
  induction g using elementary_induction generalizing v with
  | hone => simp
  | he i j => exact hodge_elementary i j v
  | hmul g h hg hh =>
    simp only [map_mul, Module.End.mul_apply]
    rw [hg, hh]

/-- A genuine intertwining linear equivalence, including the group twist. -/
noncomputable def graphTwistEquiv :
    (exteriorAction 3).Equiv ((exteriorAction 2).comp graph.toMonoidHom) :=
  Representation.Equiv.mk hodge (fun g => LinearMap.ext (hodge_action g))

/-- Jacobi's complementary-minor identity for these binary determinant-one matrices. -/
theorem complementary_minor (g : Group) (s t : ExteriorIndex 3) :
    exteriorMatrix 3 g s t = exteriorMatrix 2 (graph g) (complement s) (complement t) := by
  have h := congrArg (fun v => exteriorCoordinates 2 v (complement s))
    (hodge_action g (exteriorBasis 3 t))
  simpa only [hodge_coordinates, _root_.Equiv.symm_apply_apply, hodge_basis,
    exteriorCoordinates_action_basis] using h

/-- Reverse transport sends the square at g to the cube at the graph image of g. -/
theorem hodge_symm_action (g : Group) (v : ExteriorModule 2) :
    hodge.symm (exteriorAction 2 g v) = exteriorAction 3 (graph g) (hodge.symm v) := by
  apply hodge.injective
  rw [LinearEquiv.apply_symm_apply, hodge_action, graph_involutive,
    LinearEquiv.apply_symm_apply]

/-- The inverse complementary-basis equivalence, with the group marking explicit. -/
noncomputable def squareGraphTwistEquiv :
    (exteriorAction 2).Equiv ((exteriorAction 3).comp graph.toMonoidHom) :=
  Representation.Equiv.mk hodge.symm (fun g => LinearMap.ext (hodge_symm_action g))

/-- Complementation uses the actual wedge basis already fixed by the geometry. -/
theorem hodge_symm_square_basis (i : Fin 10) :
    hodge.symm (basis i) = exteriorBasis 3 (complement.symm (index i)) := by
  apply hodge.injective
  rw [LinearEquiv.apply_symm_apply, hodge_basis, _root_.Equiv.apply_symm_apply, basis_apply]

end Representation.SL5ExteriorSquare.Duality
