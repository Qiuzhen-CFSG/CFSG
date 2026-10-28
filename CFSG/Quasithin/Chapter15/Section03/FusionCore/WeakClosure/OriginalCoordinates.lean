module
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource.ActionComparison
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action

/-!
# Quadratic geometry for the original wreath action

The compatible wreath-to-isometry equivalence transports the original
conjugation action into standard quadratic coordinates. Pulling back that
form gives the full quadratic action on the unchanged subgroup V. Its
quadratic value is the sum of the two original plane forms, so each literal
coordinate plane is definite. The coordinate-model record keeps the original
action itself, with no new choice of plane or ambient conjugator.

The concluding consumer applies 15.3.46 to these same coordinates and
supplies its conjugate-centralization and fixed-plane normalizer bounds to
the original 15.3.48 argument.

Source: Aschbacher–Smith, the plane decomposition on printed pp.1121–1122,
Lemma 15.3.46 and Lemma 15.3.48, printed pp.1141–1142.
-/

public section
open Subgroup OrthogonalFourBinary
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.OriginalCoordinates

private noncomputable def coordinateEquiv : OrthogonalVector ≃* Multiplicative Space :=
  standard_wreath_coordinates.choose

private noncomputable def actorEquiv : OrthogonalActor ≃* IsometryGroup :=
  standard_wreath_coordinates.choose_spec.choose

attribute [local instance] FourGroupMatrixCoordinates.naturalAction orthogonalAction

private theorem equiv_compatible (g : OrthogonalActor) (v : OrthogonalVector) :
    (actorEquiv g).val (coordinateEquiv v).toAdd = (coordinateEquiv (g • v)).toAdd :=
  standard_wreath_coordinates.choose_spec.choose_spec.1 g v

private theorem equiv_form (v : OrthogonalVector) :
    form (coordinateEquiv v).toAdd = orthogonalCoordinateValue v :=
  standard_wreath_coordinates.choose_spec.choose_spec.2 v

variable {G : Type*} [Group G] {M V : Subgroup G}
  (d : CFSG.Quasithin.Chapter15.Section03.NaturalOrthogonalAction M V)

noncomputable def standardAction : NaturalAction V M where
  coordinates := d.coordinates.trans coordinateEquiv
  action := actorEquiv.toMonoidHom.comp d.actor
  onto := actorEquiv.surjective.comp d.onto
  intertwines m v := by
    change _ = (V.normalizerMonoidHom ⟨m,d.normalizes m.property⟩ v : G)
    apply congrArg (fun x : V => (x : G))
    apply (d.coordinates.trans coordinateEquiv).injective
    rw [MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    change (actorEquiv (d.actor m)).val (coordinateEquiv (d.coordinates v)).toAdd =
      (coordinateEquiv (d.coordinates (V.normalizerMonoidHom
        ⟨m,d.normalizes m.property⟩ v))).toAdd
    rw [equiv_compatible,d.compatible]

variable [IsElementaryAbelian 2 V]

noncomputable def quadraticAction : FusionCore.NaturalOrthogonalAction M V :=
  TerminalSourceEndgame.OriginalSource.quadraticAction (standardAction d)

/-- Singularity is unchanged by the quadratic-action conversion. -/
theorem quadraticAction_singular (v : V) :
    (quadraticAction d).form (Additive.ofMul v) = 0 ↔ (standardAction d).singular v :=
  TerminalSourceEndgame.OriginalSource.quadraticAction_singular (standardAction d) v

theorem form_eq (v : V) :
    (quadraticAction d).form (Additive.ofMul v) = orthogonalCoordinateValue (d.coordinates v) :=
  equiv_form (d.coordinates v)

private theorem coordinate_plane_nonsingular (i : OrthogonalPlaneIndex)
    (v : OrthogonalVector) (hv : v ∈ orthogonalCoordinatePlane i) (hn : v ≠ 1) :
    orthogonalCoordinateValue v ≠ 0 := by
  have cert : ∀ i : OrthogonalPlaneIndex, ∀ v : OrthogonalVector,
      (∀ j, j ≠ i → v j = 1) → v ≠ 1 → orthogonalCoordinateValue v ≠ 0 := by
    decide +kernel
  exact cert i v hv hn

theorem plane_definite (i : OrthogonalPlaneIndex) :
    IsDefinitePlane (quadraticAction d).form (d.plane i) := by
  refine ⟨d.plane_le i,d.card_plane i,?_⟩
  intro v hv hv1
  rw [form_eq]
  apply coordinate_plane_nonsingular i
  · exact (mem_map_iff_mem V.subtype_injective).mp hv
  · exact fun he => hv1 (d.coordinates.injective (he.trans d.coordinates.map_one.symm))

noncomputable def coordinateModel (i : OrthogonalPlaneIndex) :
    OrthogonalCoordinateModel (quadraticAction d) (d.plane i) where
  action := d
  form_eq := form_eq d
  plane_eq := ⟨i,rfl⟩

/-- The literal original planes supply the two 15.3.46 inputs used in 15.3.48. -/
theorem fusion_bounds [Finite G] {T : Sylow 2 G}
    (h : EarlierFusionInputs T M V (d.plane 1)) :
    (∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ M →
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) ∧
    normalizer (fixedPlane V (planeStabilizer T (d.plane 1)) : Set G) ≤ M := by
  have hf := lemma_15_3_46_of_earlier_inputs (quadraticAction d) h (plane_definite d 1)
  exact ⟨hf.2.2.2.1.2.2.1,hf.2.2.2.2.1⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.OriginalCoordinates
