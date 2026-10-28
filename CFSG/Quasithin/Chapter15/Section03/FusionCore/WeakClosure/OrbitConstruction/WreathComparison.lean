module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.CoordinateModel
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.DefinitePlanes

/-!
# The full quadratic action in literal matrix wreath coordinates

The two-coordinate function module is identified explicitly with the orthogonal
sum of two definite binary planes. Its literal matrix wreath action preserves the
quadratic form and is faithful. Both that wreath group and the actual isometry
group have order 72, so the compatible homomorphism between them is an isomorphism.

Given an isometry from the quadratic space on `V`, conjugation by `M` transports
to these coordinates. The full-action hypothesis proves surjectivity. Finally,
the classification of definite four-subgroups identifies the image of the chosen
`P` with one of the two supported coordinate planes. Every action and quadratic
compatibility is retained in `OrthogonalCoordinateModel`.

This is a conditional comparison: the isometry of quadratic spaces is supplied
explicitly, and its construction belongs to the source assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the plane
decomposition on printed pp.1121–1122 and its use on pp.1140–1141.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore

open OrthogonalFourBinary Theory.AlgebraicGroup
open scoped IsMulCommutative

private def planeCoordinates : OrthogonalPlaneVector ≃* Multiplicative Plane where
  toFun v := Multiplicative.ofAdd (v.toAdd 0, v.toAdd 1)
  invFun x := Multiplicative.ofAdd ![x.toAdd.1, x.toAdd.2]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv x := rfl
  map_mul' v w := rfl

private def spaceCoordinates : OrthogonalVector ≃* Multiplicative Space where
  toFun v := Multiplicative.ofAdd ((planeCoordinates (v 1)).toAdd,
    (planeCoordinates (v (Multiplicative.ofAdd 1))).toAdd)
  invFun x i := planeCoordinates.symm (Multiplicative.ofAdd
    (if i = 1 then x.toAdd.1 else x.toAdd.2))
  left_inv v := by funext i; fin_cases i <;> exact planeCoordinates.symm_apply_apply _
  right_inv x := rfl
  map_mul' v w := rfl

attribute [local instance] FourGroupMatrixCoordinates.naturalAction orthogonalAction

private theorem plane_preserves (a : OrthogonalPlaneActor) (v : OrthogonalPlaneVector) :
    planeForm (planeCoordinates (a • v)).toAdd =
      planeForm (planeCoordinates v).toAdd := by
  simp only [planeForm_indicator]
  have hz (w : OrthogonalPlaneVector) : (planeCoordinates w).toAdd = 0 ↔ w = 1 :=
    planeCoordinates.map_eq_one_iff
  have ha : a • v = 1 ↔ v = 1 :=
    (MulDistribMulAction.toMulAut OrthogonalPlaneActor OrthogonalPlaneVector a).map_eq_one_iff
  simp only [hz, ha]

private theorem actor_preserves (a : OrthogonalActor) (v : OrthogonalVector) :
    form (spaceCoordinates (a • v)).toAdd = form (spaceCoordinates v).toAdd := by
  change planeForm (planeCoordinates (a.left 1 • v (a.right⁻¹ * 1))).toAdd +
    planeForm (planeCoordinates (a.left (Multiplicative.ofAdd 1) •
      v (a.right⁻¹ * Multiplicative.ofAdd 1))).toAdd = _
  rw [plane_preserves, plane_preserves]
  have hi : ∀ i : OrthogonalPlaneIndex, i = 1 ∨ i = Multiplicative.ofAdd 1 := by
    decide +kernel
  change _ = planeForm (planeCoordinates (v 1)).toAdd +
    planeForm (planeCoordinates (v (Multiplicative.ofAdd 1))).toAdd
  rcases hi a.right with h | h
  · rw [h, inv_one, one_mul, one_mul]
  · have hinv : (Multiplicative.ofAdd (1 : F))⁻¹ = Multiplicative.ofAdd 1 := by decide +kernel
    have hsq : Multiplicative.ofAdd (1 : F) * Multiplicative.ofAdd 1 = 1 := by decide +kernel
    rw [h, hinv, mul_one, hsq, add_comm]

private def linearAutHom : MulAut (Multiplicative Space) →* (Space ≃ₗ[F] Space) where
  toFun a :=
    let e : Space ≃+ Space := MulEquiv.toAdditiveLeft a
    e.toLinearEquiv (ZMod.map_smul e)
  map_one' := by apply LinearEquiv.ext; intro x; rfl
  map_mul' a b := by apply LinearEquiv.ext; intro x; rfl

private def actionHom {A W : Type*} [Group A] [Group W]
    (c : W ≃* Multiplicative Space) (ρ : A →* MulAut W)
    (hp : ∀ a v, form (c (ρ a v)).toAdd = form (c v).toAdd) : A →* IsometryGroup :=
  let f := linearAutHom.comp ((MulAut.congr c).toMonoidHom.comp ρ)
  f.codRestrict (quadraticIsometrySubgroup form) (by
    intro a
    apply (mem_quadraticIsometrySubgroup form _).mpr
    intro x
    change form (c (ρ a (c.symm (Multiplicative.ofAdd x)))).toAdd = form x
    rw [hp, c.apply_symm_apply]
    rfl)

private def actorHom : OrthogonalActor →* IsometryGroup :=
  actionHom spaceCoordinates
    (MulDistribMulAction.toMulAut OrthogonalActor OrthogonalVector) actor_preserves

/-- Faithfulness and the two actual orders identify the full isometry group. -/
private theorem actorHom_bijective : Function.Bijective actorHom := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · let _ := FourGroupMatrixCoordinates.naturalAction_faithful
    let _ : FaithfulSMul OrthogonalActor OrthogonalVector :=
      RegularWreathProduct.functionModule_faithful _ _ _
    intro a b h
    apply FaithfulSMul.eq_of_smul_eq_smul (α := OrthogonalVector)
    intro v
    have hx := congrArg (fun g : IsometryGroup => g.val (spaceCoordinates v).toAdd) h
    change (spaceCoordinates (a • spaceCoordinates.symm (spaceCoordinates v))).toAdd =
      (spaceCoordinates (b • spaceCoordinates.symm (spaceCoordinates v))).toAdd at hx
    rw [spaceCoordinates.symm_apply_apply] at hx
    exact spaceCoordinates.injective hx
  · rw [isometryGroup_card, RegularWreathProduct.card]
    have hc : Nat.card OrthogonalPlaneActor = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [hc]
    norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]

private noncomputable def actorEquiv : OrthogonalActor ≃* IsometryGroup :=
  MulEquiv.ofBijective actorHom actorHom_bijective

/-- The literal wreath action has compatible standard quadratic coordinates.
This comparison also transports original wreath actions back to quadratic
actions without selecting a new action or changing their marked planes. -/
theorem standard_wreath_coordinates :
    ∃ c : OrthogonalVector ≃* Multiplicative Space,
    ∃ a : OrthogonalActor ≃* IsometryGroup,
      (∀ g v, (a g).val (c v).toAdd = (c (g • v)).toAdd) ∧
      ∀ v, form (c v).toAdd = orthogonalCoordinateValue v := by
  refine ⟨spaceCoordinates, actorEquiv, ?_, fun _ => rfl⟩
  intro g v
  change (spaceCoordinates (g • spaceCoordinates.symm (spaceCoordinates v))).toAdd = _
  rw [spaceCoordinates.symm_apply_apply]

variable {G : Type*} [Group G] {M V P : Subgroup G} [IsElementaryAbelian 2 V]

private def vectorEquiv (d : NaturalOrthogonalAction M V)
    (e : d.form.IsometryEquiv form) : V ≃* Multiplicative Space :=
  e.toLinearEquiv.toAddEquiv.toMultiplicativeRight

private def conjugationHom (d : NaturalOrthogonalAction M V) : M →* MulAut V :=
  V.normalizerMonoidHom.comp (Subgroup.inclusion d.normalizes)

private theorem conjugation_preserves (d : NaturalOrthogonalAction M V)
    (e : d.form.IsometryEquiv form) (m : M) (v : V) :
    form (vectorEquiv d e (conjugationHom d m v)).toAdd =
      form (vectorEquiv d e v).toAdd := by
  change form (e (Additive.ofMul (conjugationHom d m v))) = form (e (Additive.ofMul v))
  rw [e.map_app, e.map_app]
  exact d.preserves m v

private def standardHom (d : NaturalOrthogonalAction M V)
    (e : d.form.IsometryEquiv form) : M →* IsometryGroup :=
  actionHom (vectorEquiv d e) (conjugationHom d) (conjugation_preserves d e)

/-- Full conjugation realizes each isometry transported back through `e`. -/
private theorem standardHom_onto (d : NaturalOrthogonalAction M V)
    (e : d.form.IsometryEquiv form) : Function.Surjective (standardHom d e) := by
  intro a
  let aI : form.IsometryEquiv form :=
    ⟨a.val, (mem_quadraticIsometrySubgroup form _).mp a.property⟩
  obtain ⟨m, hm⟩ := d.full ((e.trans aI).trans e.symm)
  refine ⟨m, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  let v := (vectorEquiv d e).symm (Multiplicative.ofAdd x)
  have hv : conjugationHom d m v = (e.symm (a.val (e (Additive.ofMul v)))).toMul :=
    Subtype.ext (hm v)
  change (vectorEquiv d e (conjugationHom d m v)).toAdd = a.val x
  rw [hv]
  change e (e.symm (a.val (e (Additive.ofMul v)))) = a.val x
  rw [e.apply_symm_apply]
  exact congrArg a.val (e.apply_symm_apply x)

private noncomputable def coordinateAction
    (d : NaturalOrthogonalAction M V)
    (e : d.form.IsometryEquiv form) :
    CFSG.Quasithin.Chapter15.Section03.NaturalOrthogonalAction M V where
  normalizes := d.normalizes
  coordinates := (vectorEquiv d e).trans spaceCoordinates.symm
  actor := actorEquiv.symm.toMonoidHom.comp (standardHom d e)
  onto := actorEquiv.symm.surjective.comp (standardHom_onto d e)
  compatible := by
    intro m v
    apply spaceCoordinates.injective
    change spaceCoordinates (spaceCoordinates.symm (vectorEquiv d e (conjugationHom d m v))) =
      spaceCoordinates (actorEquiv.symm (standardHom d e m) •
        spaceCoordinates.symm (vectorEquiv d e v))
    rw [spaceCoordinates.apply_symm_apply]
    have h := congrArg (fun a : IsometryGroup => a.val (vectorEquiv d e v).toAdd)
      (actorEquiv.apply_symm_apply (standardHom d e m))
    change (spaceCoordinates (actorEquiv.symm (standardHom d e m) •
      spaceCoordinates.symm (vectorEquiv d e v))).toAdd =
        (vectorEquiv d e (conjugationHom d m
          ((vectorEquiv d e).symm (vectorEquiv d e v)))).toAdd at h
    rw [(vectorEquiv d e).symm_apply_apply] at h
    exact h.symm

private theorem coordinate_plane_mem (b : Bool) (v : OrthogonalVector) :
    spaceCoordinates v ∈ SylowGeometry.definitePlane b ↔
      v ∈ orthogonalCoordinatePlane (if b then Multiplicative.ofAdd 1 else 1) := by
  have hi : ∀ i : OrthogonalPlaneIndex, i = 1 ∨ i = Multiplicative.ofAdd 1 := by
    decide +kernel
  cases b
  · change planeCoordinates (v (Multiplicative.ofAdd 1)) = 1 ↔
      ∀ j, j ≠ 1 → v j = 1
    rw [planeCoordinates.map_eq_one_iff]
    constructor
    · intro hv j hj
      rcases hi j with rfl | rfl
      · exact (hj rfl).elim
      · exact hv
    · intro hv
      exact hv _ (by decide +kernel)
  · change planeCoordinates (v 1) = 1 ↔
      ∀ j, j ≠ Multiplicative.ofAdd 1 → v j = 1
    rw [planeCoordinates.map_eq_one_iff]
    constructor
    · intro hv j hj
      rcases hi j with rfl | rfl
      · exact hv
      · exact (hj rfl).elim
    · intro hv
      exact hv _ (by decide +kernel)

private theorem coordinateAction_plane
    (d : NaturalOrthogonalAction M V)
    (e : d.form.IsometryEquiv form) (hP : IsDefinitePlane d.form P) :
    ∃ i : OrthogonalPlaneIndex, P = (coordinateAction d e).plane i := by
  let c := vectorEquiv d e
  let A := (P.subgroupOf V).map c.toMonoidHom
  have hc : Nat.card A = 4 := by
    rw [← Nat.card_congr ((P.subgroupOf V).equivMapOfInjective c.toMonoidHom c.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv]
    exact hP.2.1
  have ha : ∀ w ∈ A, w ≠ 1 → form w.toAdd ≠ 0 := by
    rintro w ⟨v, hv, rfl⟩ hw
    change form (e (Additive.ofMul v)) ≠ 0
    rw [e.map_app]
    exact hP.2.2 v hv (fun h => hw (h ▸ c.map_one))
  obtain ⟨b, hb⟩ := SylowGeometry.definite_four_eq_plane A hc ha
  let i : OrthogonalPlaneIndex := if b then Multiplicative.ofAdd 1 else 1
  refine ⟨i, ?_⟩
  have hsub : P.subgroupOf V =
      (orthogonalCoordinatePlane i).comap (coordinateAction d e).coordinates.toMonoidHom := by
    ext v
    change v ∈ P.subgroupOf V ↔ spaceCoordinates.symm (c v) ∈ orthogonalCoordinatePlane i
    rw [← coordinate_plane_mem b, spaceCoordinates.apply_symm_apply, ← hb]
    exact (Subgroup.mem_map_iff_mem c.injective).symm
  have hmap := congrArg (Subgroup.map V.subtype) hsub
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP.1] at hmap
  exact hmap

/-- A supplied isometry to the standard plus-four form yields actual matrix wreath
coordinates, with surjective conjugation action, quadratic values and the chosen
plane all preserved. No actor comparison or plane marking is an extra premise. -/
theorem orthogonalCoordinateModel_nonempty_of_isometry [Finite G]
    (d : NaturalOrthogonalAction M V)
    (hP : IsDefinitePlane d.form P) (e : d.form.IsometryEquiv form) :
    Nonempty (OrthogonalCoordinateModel d P) := by
  refine ⟨⟨coordinateAction d e, ?_, coordinateAction_plane d e hP⟩⟩
  intro v
  change d.form (Additive.ofMul v) =
    form (spaceCoordinates (spaceCoordinates.symm (vectorEquiv d e v))).toAdd
  rw [spaceCoordinates.apply_symm_apply]
  exact (e.map_app (Additive.ofMul v)).symm

end CFSG.Quasithin.Chapter15.Section03.FusionCore
