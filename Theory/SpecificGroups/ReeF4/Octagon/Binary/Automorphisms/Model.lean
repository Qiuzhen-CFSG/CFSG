module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.Rigidity
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.FiniteBridge
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.RootPaths
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.NeighborCounts
public import Theory.GroupAction.RankTwoCosetGeometry.AutomorphismRigidity

/-!
# All automorphisms of the original binary Ree building

The finite graph/coset isomorphism transports the checked nine-path rigidity to
the actual full Ree incidence graph. Its unequal valences force preservation
of point and line types. The native BN-pair nine-path transitivity then proves
that every graph automorphism is a literal Model0 left translation.

Source: Aschbacher--Smith J.5.6, printed p.447. No graph-automorphism order,
abstract stabilizer bound, small completion, or recognition premise is used.
-/

public section
noncomputable section
namespace ReeF4.Octagon.Binary.Automorphisms
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.AlgebraicGroup.TitsSystem

/-- Unequal local valences force every incidence automorphism to preserve types. -/
theorem automorphism_preserves_type (a : DihedralGeometry.graph family ≃g
    DihedralGeometry.graph family) (v : CosetGeometry.Vertex family) :
    (a v).type=v.type := by
  have hc := Nat.card_congr (a.mapNeighborSet v)
  rw [card_neighbors,card_neighbors] at hc
  cases h1 : v.type <;> cases h2 : (a v).type <;> simp_all

private def markedPath : BasedWalk (DihedralGeometry.graph family) 9
    (FiniteBridge.graphIso 0) := FiniteGraph.seedPath.map FiniteBridge.graphIso.toHom

private theorem markedPath_nonbacktracking : markedPath.Nonbacktracking := by
  apply (BasedWalk.nonbacktracking_map_iff FiniteBridge.graphIso.toHom _ _).mpr
    FiniteGraph.seedPath_nonbacktracking
  intro x y z he
  apply Subtype.ext
  exact FiniteBridge.graphIso.injective (congrArg Subtype.val he)

private theorem markedPath_rigid (a : DihedralGeometry.graph family ≃g
    DihedralGeometry.graph family) (h : ∀w∈markedPath.vertices,a w=w) :
    a=SimpleGraph.Iso.refl := by
  let e := FiniteBridge.graphIso
  let b := e.trans (a.trans e.symm)
  have hb : b=SimpleGraph.Iso.refl := FiniteGraph.eq_refl_of_fix_seed b (by
    intro w hw
    have hew : e w∈markedPath.vertices := by
      change e w∈(FiniteGraph.seedPath.map e.toHom).vertices
      rw [BasedWalk.vertices_map,FiniteGraph.seedPath_vertices]
      exact List.mem_map.mpr ⟨w,hw,rfl⟩
    change e.symm (a (e w))=w
    rw [h (e w) hew,e.symm_apply_apply])
  ext v
  obtain ⟨w,rfl⟩ := e.surjective v
  have hh := congrArg (fun k : FiniteGraph.graph ≃g FiniteGraph.graph => k w) hb
  change e.symm (a (e w))=w at hh
  change a (e w)=e w
  simpa only [e.apply_symm_apply] using congrArg e hh

/-- Every automorphism of the original binary Ree coset incidence graph is
induced by the literal left action of an element of the full Ree group. -/
theorem automorphism_eq_left_action (a : DihedralGeometry.graph family ≃g
    DihedralGeometry.graph family) :
    ∃ g : Model 0, ∀v,a v=g • v := by
  exact CosetGeometry.RankTwo.automorphism_eq_translation_of_path_rigid family
    markedPath markedPath_nonbacktracking (rootPathTransitive_nine _)
    markedPath_rigid a (automorphism_preserves_type a _).symm
end ReeF4.Octagon.Binary.Automorphisms
