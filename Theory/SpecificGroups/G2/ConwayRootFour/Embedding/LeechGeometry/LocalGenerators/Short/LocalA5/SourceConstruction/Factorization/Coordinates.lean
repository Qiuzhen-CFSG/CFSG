module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Inputs
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Scalar

/-!
# The literal local action in an additive long frame

The coordinate map identifies the six-tuple additive group with the whole
U-fixed space. Conjugating the actual centralizer action gives an additive
representation. No linearity of the coordinate equivalence is used. The
literal dihedral action proves commutation and invariance of the pair (0,5),
using the previously established fixed-space characterization.

`Factorization.ScalarLinearity` recovers field linearity; `Factorization`
uses the fixed-pair invariant in its two-factor construction.
Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Factorization
open scoped Long

def coordinateEquiv (L : LongFrame) : (Fin 6 → F) ≃+ fixedSpace :=
  AddEquiv.ofBijective
    ({ toFun := fun v => ⟨L.coordinates v, (L.coordinates_range _).mpr ⟨v, rfl⟩⟩
       map_zero' := by apply Subtype.ext; exact map_zero _
       map_add' := by intro v w; apply Subtype.ext; exact map_add _ _ _ } : (Fin 6 → F) →+ fixedSpace)
    ⟨fun _ _ h => L.coordinates_injective (congrArg Subtype.val h), by
      intro v
      obtain ⟨w, hw⟩ := (L.coordinates_range v.val).mp v.property
      exact ⟨w, Subtype.ext hw⟩⟩

@[simp] theorem coordinateEquiv_val (L : LongFrame) (v : Fin 6 → F) :
    (coordinateEquiv L v).val = L.coordinates v := rfl

def coordinateAction (L : LongFrame) : centralizerI →* Multiplicative (AddAut (Fin 6 → F)) where
  toFun g := Multiplicative.ofAdd ((coordinateEquiv L).trans
    ((Long.centralizerAction g).toAddEquiv.trans (coordinateEquiv L).symm))
  map_one' := by
    ext v : 2
    change (coordinateEquiv L).symm (Long.centralizerAction 1 (coordinateEquiv L v)) = v
    rw [map_one]
    exact (coordinateEquiv L).symm_apply_apply v
  map_mul' g h := by
    ext v : 2
    change (coordinateEquiv L).symm (Long.centralizerAction (g * h) (coordinateEquiv L v)) =
      (coordinateEquiv L).symm (Long.centralizerAction g
        (coordinateEquiv L ((coordinateEquiv L).symm
          (Long.centralizerAction h (coordinateEquiv L v)))))
    rw [(coordinateEquiv L).apply_symm_apply, map_mul]
    rfl

theorem coordinateAction_spec (L : LongFrame) (g : centralizerI) (v : Fin 6 → F) :
    L.coordinates (coordinateAction L g v) =
      quotientModTwoRepresentation g.val (L.coordinates v) := by
  change ((coordinateEquiv L) ((coordinateEquiv L).symm
    (Long.centralizerAction g (coordinateEquiv L v)))).val = _
  rw [(coordinateEquiv L).apply_symm_apply]
  rfl

def localAction {L : LongFrame} (G : Geometry L) : G.subgroup →* Multiplicative (AddAut (Fin 6 → F)) :=
  (coordinateAction L).comp (G.subgroup.subtype.codRestrict centralizerI G.mem)

theorem localAction_spec {L : LongFrame} (G : Geometry L) (a : G.subgroup) (v : Fin 6 → F) :
    L.coordinates (localAction G a v) =
      quotientModTwoRepresentation a.val (L.coordinates v) :=
  coordinateAction_spec L ⟨a.val, G.mem a⟩ v

theorem localAction_commutes {L : LongFrame} (G : Geometry L) (a : G.subgroup)
    (d : DihedralGroup 5) (v : Fin 6 → F) :
    localAction G a (blockAction (slEquiv (dihedralModel d)) v) =
      blockAction (slEquiv (dihedralModel d)) (localAction G a v) := by
  apply L.coordinates_injective
  rw [localAction_spec, ← dihedralLift_action, ← dihedralLift_action, localAction_spec]
  have h := congrArg (fun g => quotientModTwoRepresentation g (L.coordinates v))
    (G.centralizes a d).eq
  simpa only [map_mul, LinearEquiv.mul_apply] using h

theorem localAction_preserves_fixed {L : LongFrame} (G : Geometry L) (a : G.subgroup)
    (v : Fin 6 → F) (hv : v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0) :
    localAction G a v 1 = 0 ∧ localAction G a v 2 = 0 ∧
      localAction G a v 3 = 0 ∧ localAction G a v 4 = 0 := by
  apply (dihedralLift_fixed_iff L _).mp
  intro d
  rw [dihedralLift_action, ← localAction_commutes]
  have hd := (dihedralLift_fixed_iff L v).mpr hv d
  rw [dihedralLift_action] at hd
  rw [L.coordinates_injective hd]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Factorization
