module

public import Theory.AlgebraicGroup.Borel.Commutator

public import Theory.AlgebraicGroup.Borel.Defs

public import Theory.AlgebraicGroup.Borel.SemisimpleCenter

public import Theory.AlgebraicGroup.Morphism.Connected

public import Theory.AlgebraicGroup.Morphism.Injectivity

public import Theory.AlgebraicGroup.Reductive.Defs

public import Theory.AlgebraicGroup.Semisimple.Versions

public import Theory.AlgebraicGroup.Tori.Extension

/-!
The radical of the identity component has ambient image equal to the radical
of the full algebraic group, even when the latter is disconnected. Ambient
conjugation restricts to an automorphism of the identity component, so it
preserves its radical by normality, connectedness, solvability, and radical
maximality. The two ambient images are then compared using maximality once in
the full group and once inside the identity component.

This is the checked staging module for
`ag-radical-identity-component-ambient-image`.
-/

set_option warningAsError false

namespace Theory.AlgebraicGroup

set_option allowUnsafeReducibility true in
attribute [local semireducible] ClosedSubgroup.carrierVariety
attribute [-instance] ClosedSubgroup.carrierAlgebraicGroup
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

public theorem radical_identityComponent_ambientImage_eq
    {k : Type*} [Field k] [IsAlgClosed k]
    {G : Variety k} [AlgebraicGroup G]
    (R : ClosedSubgroup G) (hR : IsRadicalSubgroup R) :
    let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
    let _ : AlgebraicGroup G0.carrierVariety := G0.carrierAlgebraicGroup
    ∀ R0 : ClosedSubgroup G0.carrierVariety,
      IsRadicalSubgroup R0 →
      (G0.inclusion.comp R0.inclusion).imageClosedSubgroup = R := by
  dsimp only
  let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
  letI : AlgebraicGroup G0.carrierVariety := G0.carrierAlgebraicGroup
  intro R0 hR0
  letI : AlgebraicGroup R0.carrierVariety := R0.carrierAlgebraicGroup
  let q : AlgebraicGroup.Morphism R0.carrierVariety G :=
    G0.inclusion.comp R0.inclusion
  change q.imageClosedSubgroup = R
  let I := q.imageClosedSubgroup
  have hR0var : Variety.IsConnected R0.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph R0.isZariskiClosed
    let : ConnectedSpace
        {x : Variety.Point G0.carrierVariety //
          x ∈ (R0 : Set (Variety.Point G0.carrierVariety))} :=
      Subtype.connectedSpace hR0.connected
    let : ConnectedSpace (Variety.Point R0.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  have hIconnected : _root_.IsConnected
      (I : Set (Variety.Point G)) :=
    q.imageClosedSubgroup_isConnected hR0var
  have hIsolvable : Group.IsSolvable
      (Variety.Point I.carrierVariety) :=
    q.imageClosedSubgroup_isSolvable hR0.solvable
  have hG0normal : G0.toSubgroup.Normal := by
    simpa [G0] using
      AlgebraicGroup.identityComponentClosedSubgroup_isNormal G
  have hInormal : I.toSubgroup.Normal := by
    constructor
    intro x hx g
    change x ∈ q.image at hx
    rcases hx with ⟨z, rfl⟩
    let c : AlgebraicGroup.Morphism G0.carrierVariety G0.carrierVariety :=
      G0.conjugationRestriction hG0normal g
    have hcsurj : Function.Surjective c.onPoints := by
      intro y
      refine ⟨(G0.conjugationRestriction hG0normal g⁻¹).onPoints y, ?_⟩
      apply G0.inclusion_injective
      change G0.inclusion.onPoints
          ((G0.conjugationRestriction hG0normal g).onPoints
            ((G0.conjugationRestriction hG0normal g⁻¹).onPoints y)) =
        G0.inclusion.onPoints y
      rw [G0.conjugationRestriction_inclusion_apply hG0normal,
        G0.conjugationRestriction_inclusion_apply hG0normal]
      group
    let j : AlgebraicGroup.Morphism R0.carrierVariety G0.carrierVariety :=
      c.comp R0.inclusion
    let J := j.imageClosedSubgroup
    letI : AlgebraicGroup J.carrierVariety := J.carrierAlgebraicGroup
    have hJmap : J.toSubgroup = R0.toSubgroup.map c.onPoints := by
      ext y
      constructor
      · intro hy
        change y ∈ j.image at hy
        rcases hy with ⟨w, hw⟩
        exact ⟨R0.inclusion.onPoints w, (R0.pointEquiv w).property, hw⟩
      · rintro ⟨y, hy, rfl⟩
        change c.onPoints y ∈ j.image
        let w : Variety.Point R0.carrierVariety :=
          R0.pointEquiv.symm ⟨y, hy⟩
        refine ⟨w, ?_⟩
        change c.onPoints (R0.inclusion.onPoints w) = c.onPoints y
        apply congrArg c.onPoints
        change (R0.pointEquiv w).val = y
        dsimp only [w]
        rw [R0.pointEquiv.apply_symm_apply]
    have hJnormal : J.toSubgroup.Normal := by
      rw [hJmap]
      exact Subgroup.Normal.map hR0.normal c.onPoints hcsurj
    have hJconnected : _root_.IsConnected
        (J : Set (Variety.Point G0.carrierVariety)) :=
      j.imageClosedSubgroup_isConnected hR0var
    have hJsolvable : Group.IsSolvable
        (Variety.Point J.carrierVariety) :=
      j.imageClosedSubgroup_isSolvable hR0.solvable
    have hJR0 : J ≤ R0 :=
      hR0.maximal J hJnormal hJconnected hJsolvable
    change g * q.onPoints z * g⁻¹ ∈ q.image
    have hczJ : c.onPoints (R0.inclusion.onPoints z) ∈ J := by
      change c.onPoints (R0.inclusion.onPoints z) ∈ j.image
      exact ⟨z, rfl⟩
    have hczR0 := hJR0 hczJ
    let w : Variety.Point R0.carrierVariety :=
      R0.pointEquiv.symm ⟨c.onPoints (R0.inclusion.onPoints z), hczR0⟩
    refine ⟨w, ?_⟩
    change G0.inclusion.onPoints (R0.inclusion.onPoints w) =
      g * G0.inclusion.onPoints (R0.inclusion.onPoints z) * g⁻¹
    calc
      G0.inclusion.onPoints (R0.inclusion.onPoints w) =
          G0.inclusion.onPoints
            (c.onPoints (R0.inclusion.onPoints z)) := by
        apply congrArg G0.inclusion.onPoints
        change (R0.pointEquiv w).val =
          c.onPoints (R0.inclusion.onPoints z)
        dsimp only [w]
        rw [R0.pointEquiv.apply_symm_apply]
      _ = g * G0.inclusion.onPoints (R0.inclusion.onPoints z) * g⁻¹ :=
        G0.conjugationRestriction_inclusion_apply hG0normal g _
  have hIR : I ≤ R :=
    hR.maximal I hInormal hIconnected hIsolvable
  have hRG0 : R ≤ G0 := by
    intro x hx
    exact connected_closedSubgroup_subset_identityComponent G hR.connected hx
  let rG0 : AlgebraicGroup.Morphism R.carrierVariety G0.carrierVariety :=
    R.inclusion.codRestrictClosedSubgroup G0
      (fun x => hRG0 (R.pointEquiv x).property)
  let K := rG0.imageClosedSubgroup
  letI : AlgebraicGroup K.carrierVariety := K.carrierAlgebraicGroup
  have hRvar : Variety.IsConnected R.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
    let : ConnectedSpace
        {x : Variety.Point G // x ∈ (R : Set (Variety.Point G))} :=
      Subtype.connectedSpace hR.connected
    let : ConnectedSpace (Variety.Point R.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  have hKconnected : _root_.IsConnected
      (K : Set (Variety.Point G0.carrierVariety)) :=
    rG0.imageClosedSubgroup_isConnected hRvar
  have hKsolvable : Group.IsSolvable
      (Variety.Point K.carrierVariety) :=
    rG0.imageClosedSubgroup_isSolvable hR.solvable
  have hKnormal : K.toSubgroup.Normal := by
    constructor
    intro x hx g0
    change x ∈ rG0.image at hx
    rcases hx with ⟨z, rfl⟩
    have hamb : G0.inclusion.onPoints
        (g0 * rG0.onPoints z * g0⁻¹) ∈ R := by
      rw [map_mul, map_mul, map_inv]
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
      exact hR.normal.conj_mem (R.inclusion.onPoints z)
        (R.pointEquiv z).property (G0.inclusion.onPoints g0)
    let w : Variety.Point R.carrierVariety :=
      R.pointEquiv.symm
        ⟨G0.inclusion.onPoints (g0 * rG0.onPoints z * g0⁻¹), hamb⟩
    change g0 * rG0.onPoints z * g0⁻¹ ∈ rG0.image
    refine ⟨w, ?_⟩
    apply G0.inclusion_injective
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    change (R.pointEquiv w).val =
      G0.inclusion.onPoints (g0 * rG0.onPoints z * g0⁻¹)
    dsimp only [w]
    rw [R.pointEquiv.apply_symm_apply]
  have hKR0 : K ≤ R0 :=
    hR0.maximal K hKnormal hKconnected hKsolvable
  have hRI : R ≤ I := by
    intro x hx
    have hxG0 := hRG0 hx
    let x0 : Variety.Point G0.carrierVariety :=
      G0.pointEquiv.symm ⟨x, hxG0⟩
    have hxK : x0 ∈ K := by
      change x0 ∈ rG0.image
      let z : Variety.Point R.carrierVariety :=
        R.pointEquiv.symm ⟨x, hx⟩
      refine ⟨z, ?_⟩
      apply G0.inclusion_injective
      rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
      change (R.pointEquiv z).val = (G0.pointEquiv x0).val
      dsimp only [z, x0]
      rw [R.pointEquiv.apply_symm_apply, G0.pointEquiv.apply_symm_apply]
    have hxR0 := hKR0 hxK
    let z : Variety.Point R0.carrierVariety :=
      R0.pointEquiv.symm ⟨x0, hxR0⟩
    change x ∈ q.image
    refine ⟨z, ?_⟩
    change G0.inclusion.onPoints (R0.inclusion.onPoints z) = x
    change (G0.pointEquiv (R0.inclusion.onPoints z)).val = x
    change (G0.pointEquiv ((R0.pointEquiv z).val)).val = x
    dsimp only [z, x0]
    rw [R0.pointEquiv.apply_symm_apply, G0.pointEquiv.apply_symm_apply]
  apply SetLike.coe_injective
  exact Set.Subset.antisymm hIR hRI

end Theory.AlgebraicGroup
