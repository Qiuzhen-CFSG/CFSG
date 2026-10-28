module

public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteIndex

universe u

set_option linter.style.haveILetI false

/-! Connectedness and restrictions of algebraic-group morphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Restricting a surjective morphism to the identity component of the closed
preimage of a connected closed subgroup remains surjective. -/
public theorem Morphism.preimageRestriction_identityComponent_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hf : Function.Surjective f.onPoints)
    (R : ClosedSubgroup H)
    (hR : Variety.IsConnected R.carrierVariety) :
    let P := f.closedSubgroupPreimage R
    let _ : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
    let P0 := AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety
    let _ : AlgebraicGroup P0.carrierVariety := P0.carrierAlgebraicGroup
    Function.Surjective
      ((f.preimageRestriction R).comp P0.inclusion).onPoints := by
  let P := f.closedSubgroupPreimage R
  letI : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  let g := f.preimageRestriction R
  have hgsurj : Function.Surjective g.onPoints :=
    f.preimageRestriction_surjective hf R
  let P0 := AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety
  letI : AlgebraicGroup P0.carrierVariety := P0.carrierAlgebraicGroup
  let : P0.toSubgroup.FiniteIndex := by
    change (AlgebraicGroup.identityComponentSubgroup P.carrierVariety).FiniteIndex
    infer_instance
  let r : AlgebraicGroup.Morphism P0.carrierVariety R.carrierVariety :=
    g.comp P0.inclusion
  have hRset : _root_.IsConnected (R : Set (Variety.Point H)) := by
    let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
    let : ConnectedSpace (Variety.Point R.carrierVariety) :=
      connectedSpace_iff_univ.mpr hR
    rw [isConnected_iff_connectedSpace]
    exact e.connectedSpace_iff.mp inferInstance
  have hsurj := finiteIndex_subgroup_surjective_of_connected_target
    P P0 R g hgsurj hRset
  change Function.Surjective r.onPoints
  exact hsurj

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The ambient identity component of the closed preimage of a connected
closed subgroup maps onto that subgroup under a surjective morphism. -/
public theorem Morphism.closedSubgroupPreimage_identityComponent_image_eq
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hf : Function.Surjective f.onPoints)
    (S : ClosedSubgroup H)
    (hS : _root_.IsConnected (S : Set (Variety.Point H))) :
    let P := f.closedSubgroupPreimage S
    (f.comp P.identityComponentAmbient.inclusion).imageClosedSubgroup = S := by
  let P := f.closedSubgroupPreimage S
  let I := P.identityComponentAmbient
  let q := f.comp I.inclusion
  have hSvar : Variety.IsConnected S.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph S.isZariskiClosed
    let : ConnectedSpace
        {x : Variety.Point H // x ∈ (S : Set (Variety.Point H))} :=
      Subtype.connectedSpace hS
    let : ConnectedSpace (Variety.Point S.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  apply SetLike.coe_injective
  ext y
  constructor
  · intro hy
    change y ∈ q.image at hy
    rcases hy with ⟨x, rfl⟩
    have hxI := (I.pointEquiv x).property
    exact ClosedSubgroup.identityComponentAmbient_le P hxI
  · intro hy
    let P0 := AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety
    letI : AlgebraicGroup P0.carrierVariety := P0.carrierAlgebraicGroup
    let yS : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨y, hy⟩
    obtain ⟨z, hz⟩ :=
      f.preimageRestriction_identityComponent_surjective hf S hSvar yS
    let xG := P.inclusion.onPoints (P0.inclusion.onPoints z)
    have hxI : xG ∈ I := by
      apply (ClosedSubgroup.mem_identityComponentAmbient_iff P xG).mpr
      exact ⟨P0.inclusion.onPoints z, (P0.pointEquiv z).property, rfl⟩
    let xI : Variety.Point I.carrierVariety := I.pointEquiv.symm ⟨xG, hxI⟩
    change y ∈ q.image
    refine ⟨xI, ?_⟩
    change f.onPoints (I.inclusion.onPoints xI) = y
    have hxIAmb : I.inclusion.onPoints xI = xG := by
      change (I.pointEquiv xI).val = xG
      dsimp only [xI]
      rw [I.pointEquiv.apply_symm_apply]
    rw [hxIAmb]
    have hzAmb := congrArg S.inclusion.onPoints hz
    change S.inclusion.onPoints
        ((f.preimageRestriction S).onPoints (P0.inclusion.onPoints z)) =
      S.inclusion.onPoints yS at hzAmb
    rw [f.preimageRestriction_inclusion_apply] at hzAmb
    change f.onPoints xG = y
    exact hzAmb.trans (by
      change (S.pointEquiv yS).val = y
      dsimp only [yS]
      rw [S.pointEquiv.apply_symm_apply])

end Theory.AlgebraicGroup
