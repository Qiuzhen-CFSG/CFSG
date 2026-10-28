module

public import Theory.AlgebraicGroup.Solvable.SubtorusCentralizer
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Morphism.CodRestrict
public import Theory.AlgebraicGroup.Borel.Defs

/-!
# Connectedness of the intrinsic Borel restriction

For a subtorus `S ≤ B` of a connected solvable group `B`, identify the
centralizer inside `B` with the intersection, and exchange the two intrinsic
presentations of that intersection. The solvable centralizer theorem therefore
proves connectedness of `B ∩ C_H(S)` as a subgroup of `C_H(S)`.
Solvability follows from its injective morphism into `B`.

This is the connected-solvable step in Borel, *Linear Algebraic Groups*,
§11.15 (`refs/KGroup/Bor1/Chapter4.tex`). No connectedness or solvability
of the ambient centralizer is inferred here.
-/

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction

set_option allowUnsafeReducibility true in
attribute [local semireducible] ClosedSubgroup.carrierVariety
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Variety k} [AlgebraicGroup H]

omit [IsAlgClosed k] in
private theorem carrier_connected (K : ClosedSubgroup H)
    (hK : _root_.IsConnected (K : Set (Variety.Point H))) :
    Variety.IsConnected K.carrierVariety := by
  let : ConnectedSpace {x : Variety.Point H // x ∈ (K : Set (Variety.Point H))} :=
    Subtype.connectedSpace hK
  let : ConnectedSpace (Variety.Point K.carrierVariety) :=
    (Variety.closedSubvarietyPointHomeomorph K.isZariskiClosed).connectedSpace_iff.mpr
      inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

omit [IsAlgClosed k] in
private theorem set_connected (K : ClosedSubgroup H)
    (hK : Variety.IsConnected K.carrierVariety) :
    _root_.IsConnected (K : Set (Variety.Point H)) := by
  let : ConnectedSpace (Variety.Point K.carrierVariety) :=
    connectedSpace_iff_univ.mpr hK
  change _root_.IsConnected (K.toSubgroup : Set (Variety.Point H))
  rw [← K.range_inclusion]
  exact isConnected_range K.inclusion.toVariety.continuous

omit [IsAlgClosed k] in
private noncomputable def intersectionSwap (B C : ClosedSubgroup H) :
    AlgebraicGroup.Iso (B.inclusion.closedSubgroupPreimage C).carrierVariety
      (C.inclusion.closedSubgroupPreimage B).carrierVariety := by
  let P := B.inclusion.closedSubgroupPreimage C
  let Q := C.inclusion.closedSubgroupPreimage B
  let f : AlgebraicGroup.Morphism P.carrierVariety Q.carrierVariety :=
    (B.inclusion.preimageRestriction C).codRestrictClosedSubgroup Q (by
      intro x
      change C.inclusion.onPoints ((B.inclusion.preimageRestriction C).onPoints x) ∈ B
      rw [AlgebraicGroup.Morphism.preimageRestriction_inclusion_apply]
      exact (B.pointEquiv (P.inclusion.onPoints x)).property)
  let g : AlgebraicGroup.Morphism Q.carrierVariety P.carrierVariety :=
    (C.inclusion.preimageRestriction B).codRestrictClosedSubgroup P (by
      intro x
      change B.inclusion.onPoints ((C.inclusion.preimageRestriction B).onPoints x) ∈ C
      rw [AlgebraicGroup.Morphism.preimageRestriction_inclusion_apply]
      exact (C.pointEquiv (Q.inclusion.onPoints x)).property)
  refine ⟨f, g, ?_, ?_⟩
  · intro x
    apply P.inclusion_injective
    apply B.inclusion_injective
    rfl
  · intro x
    apply Q.inclusion_injective
    apply C.inclusion_injective
    rfl

/-- The intrinsic restriction of a Borel containing a subtorus is connected
and solvable. Maximality requires the separate fixed-component argument. -/
public theorem connected_solvable
    (S B : ClosedSubgroup H) (hS : IsSubtorus S)
    (hB : IsBorelSubgroup B) (hSB : S ≤ B) :
    _root_.IsConnected
        (S.centralizer.inclusion.closedSubgroupPreimage B :
          Set (Variety.Point S.centralizer.carrierVariety)) ∧
      Group.IsSolvable
        (Variety.Point (S.centralizer.inclusion.closedSubgroupPreimage B).carrierVariety) := by
  let t : AlgebraicGroup.Morphism S.carrierVariety B.carrierVariety :=
    S.inclusion.codRestrictClosedSubgroup B (fun x => hSB (S.pointEquiv x).property)
  let T : ClosedSubgroup B.carrierVariety := t.imageClosedSubgroup
  have hT : IsSubtorus T := morphism_image_isTorus t hS
  have heq : B.inclusion.closedSubgroupPreimage S.centralizer = T.centralizer := by
    apply SetLike.coe_injective
    ext x
    change B.inclusion.onPoints x ∈ Subgroup.centralizer (S.toSubgroup : Set _) ↔
      x ∈ Subgroup.centralizer (T.toSubgroup : Set _)
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx y hy
      change ∃ z, t.onPoints z = y at hy
      obtain ⟨z, rfl⟩ := hy
      apply B.inclusion_injective
      simpa only [map_mul, t, AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        using hx (S.inclusion.onPoints z) (S.pointEquiv z).property
    · intro hx s hs
      let z : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨s, hs⟩
      have hz : t.onPoints z ∈ T.toSubgroup := ⟨z, rfl⟩
      have he := congrArg B.inclusion.onPoints (hx (t.onPoints z) hz)
      have hzval : S.inclusion.onPoints z = s := by
        change (S.pointEquiv (S.pointEquiv.symm ⟨s, hs⟩)).val = s
        rw [S.pointEquiv.apply_symm_apply]
      simpa only [map_mul, t, AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply, hzval]
        using he
  have hTc : Variety.IsConnected T.centralizer.carrierVariety :=
    subtorus_centralizer_isConnected_of_isConnected_of_isSolvable
      (carrier_connected B hB.connected) hB.solvable hT
  have hPc : Variety.IsConnected
      (B.inclusion.closedSubgroupPreimage S.centralizer).carrierVariety := by
    rw [heq]
    exact hTc
  refine ⟨set_connected _ ((algebraicGroupIso_isConnected_iff
    (intersectionSwap B S.centralizer)).mp hPc), ?_⟩
  let f := S.centralizer.inclusion.preimageRestriction B
  have hf : Function.Injective f.onPoints := by
    intro x y hxy
    apply (S.centralizer.inclusion.closedSubgroupPreimage B).inclusion_injective
    apply S.centralizer.inclusion_injective
    have he := congrArg B.inclusion.onPoints hxy
    simpa only [f, AlgebraicGroup.Morphism.preimageRestriction_inclusion_apply] using he
  let : Group.IsSolvable (Variety.Point B.carrierVariety) := hB.solvable
  exact Group.isSolvable_of_isSolvable_injective hf

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
