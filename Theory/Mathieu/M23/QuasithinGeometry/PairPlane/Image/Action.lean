module

public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Coordinates
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Stabilizers
public import Theory.SpecificGroups.PSL3Four.FieldExtension

/-!
# The faithful coordinate action of the M23 pair stabilizer

The two natural actions of the stabilizer of `x = {11,17}` are transported
through the explicit coordinates of `Coordinates.lean`.  The resulting paired
collineation action is faithful. We allow an arbitrary incidence coordinate
system so a diagonal adjustment can be made when identifying its image with
the concrete `PSL(3,4) ⋊ C₂` action.

Source: Aschbacher, *Sporadic Groups*, §18; Aschbacher--Smith,
*The Classification of Quasithin Groups*, §5.2, PDF pp.672–674.
-/

@[expose] public section

open scoped Pointwise
open Configuration Projectivization

namespace Sporadic.Mathieu.M23Geometry.PairPlaneImage

abbrev PG := PairPlaneCoordinates.PG

/-- Incidence coordinates, including any adjustment of the original tables. -/
structure Coordinates where
  pointEquiv : pairComplement x.val ≃ PG
  lineEquiv : pairLines x.val ≃ PG
  incident_iff (p : pairComplement x.val) (l : pairLines x.val) :
    pointEquiv p ∈ lineEquiv l ↔ p.val ∈ l.val

/-- The original coordinate tables, without diagonal adjustment. -/
noncomputable def tableCoordinates : Coordinates where
  pointEquiv := PairPlaneCoordinates.pointEquiv
  lineEquiv := PairPlaneCoordinates.lineEquiv
  incident_iff := PairPlaneCoordinates.incident_iff

variable (C : Coordinates)

/-- Transport of the complementary-point action to projective points. -/
noncomputable def pairPointAction : pairStabilizer →* Equiv.Perm PG :=
  { toFun := fun g => C.pointEquiv.symm.trans ((complementAction x.val g).trans C.pointEquiv)
    map_one' := by
      apply Equiv.ext
      intro p
      simp
    map_mul' := by
      intro g h
      apply Equiv.ext
      intro p
      simp }

/-- Transport of the derived-line action to projective line covectors. -/
noncomputable def pairLineAction : pairStabilizer →* Equiv.Perm PG :=
  { toFun := fun g => C.lineEquiv.symm.trans ((lineAction x.val g).trans C.lineEquiv)
    map_one' := by
      apply Equiv.ext
      intro l
      simp
    map_mul' := by
      intro g h
      apply Equiv.ext
      intro l
      simp }

@[simp] theorem pairPointAction_apply (g : pairStabilizer) (p : PG) :
    pairPointAction C g p = C.pointEquiv (complementAction x.val g (C.pointEquiv.symm p)) := rfl

@[simp] theorem pairLineAction_apply (g : pairStabilizer) (l : PG) :
    pairLineAction C g l = C.lineEquiv (lineAction x.val g (C.lineEquiv.symm l)) := rfl

/-- The transported actions preserve the projective-plane incidence relation. -/
theorem pair_actions_incidence (g : pairStabilizer) (p l : PG) :
    pairPointAction C g p ∈ pairLineAction C g l ↔ p ∈ l := by
  rw [pairPointAction_apply, pairLineAction_apply]
  obtain ⟨p', rfl⟩ := C.pointEquiv.surjective p
  obtain ⟨l', rfl⟩ := C.lineEquiv.surjective l
  rw [C.incident_iff, C.incident_iff]
  simpa only [Equiv.symm_apply_apply] using action_preserves_incidence x.val g p' l'

/-- The paired projective collineation representation of the M23 pair stabilizer. -/
noncomputable def pairCollineation : pairStabilizer →* Collineation PG PG where
  toFun g := ⟨(pairPointAction C g, pairLineAction C g), pair_actions_incidence C g⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext <;> apply Equiv.ext <;> intro z <;> simp
  map_mul' g h := by
    apply Subtype.ext
    apply Prod.ext <;> apply Equiv.ext <;> intro z <;> simp

@[simp] theorem pairCollineation_point (g : pairStabilizer) (p : PG) :
    Collineation.pointHom PG PG (pairCollineation C g) p = pairPointAction C g p := by
  rfl

@[simp] theorem pairCollineation_line (g : pairStabilizer) (l : PG) :
    Collineation.lineHom PG PG (pairCollineation C g) l = pairLineAction C g l := by
  rfl

theorem pairCollineation_injective : Function.Injective (pairCollineation C) := by
  intro g h e
  apply complementAction_injective
  apply Equiv.ext
  intro p
  have hp := congrArg (fun c : Collineation PG PG =>
    Collineation.pointHom PG PG c (C.pointEquiv p)) e
  rw [pairCollineation_point, pairCollineation_point] at hp
  exact C.pointEquiv.injective (by simpa only [pairPointAction_apply, Equiv.symm_apply_apply] using hp)

end Sporadic.Mathieu.M23Geometry.PairPlaneImage
