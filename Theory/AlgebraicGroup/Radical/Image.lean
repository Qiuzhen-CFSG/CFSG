module

public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.Morphism.Solvable
public import Theory.AlgebraicGroup.Radical.Defs
public import Theory.AlgebraicGroup.Radical.Preimage
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Semisimple.Defs

universe u

/-! Images of radical subgroups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option warningAsError false in
public theorem theorem_1_7_2_i
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism G H) :
    (IsReductiveAlgebraicGroup G →
      IsReductiveAlgebraicGroup φ.imageClosedSubgroup.carrierVariety) ∧
    (IsSemisimpleAlgebraicGroup G →
      IsSemisimpleAlgebraicGroup φ.imageClosedSubgroup.carrierVariety) := by sorry

/-- Under a surjective morphism, the closed image of a radical subgroup is
contained in every radical subgroup of the target. -/
private lemma IsRadicalSubgroup.imageClosedSubgroup_le_of_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hf : Function.Surjective f.onPoints)
    {R : ClosedSubgroup G} (hR : IsRadicalSubgroup R)
    {S : ClosedSubgroup H} (hS : IsRadicalSubgroup S) :
    (f.comp R.inclusion).imageClosedSubgroup ≤ S := by
  let q := f.comp R.inclusion
  let Q := q.imageClosedSubgroup
  have hQmap : Q.toSubgroup = R.toSubgroup.map f.onPoints := by
    ext y
    constructor
    · intro hy
      change y ∈ q.image at hy
      rcases hy with ⟨x, rfl⟩
      exact ⟨R.inclusion.onPoints x, (R.pointEquiv x).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      change f.onPoints x ∈ q.image
      let xR : Variety.Point R.carrierVariety := R.pointEquiv.symm ⟨x, hx⟩
      refine ⟨xR, ?_⟩
      change f.onPoints (R.inclusion.onPoints xR) = f.onPoints x
      apply congrArg f.onPoints
      change (R.pointEquiv xR).val = x
      dsimp only [xR]
      rw [R.pointEquiv.apply_symm_apply]
  have hQnormal : Q.toSubgroup.Normal := by
    rw [hQmap]
    exact Subgroup.Normal.map hR.normal f.onPoints hf
  have hRvar : Variety.IsConnected R.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
    let : ConnectedSpace
        {x : Variety.Point G // x ∈ (R : Set (Variety.Point G))} :=
      Subtype.connectedSpace hR.connected
    let : ConnectedSpace (Variety.Point R.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  have hQconnected := q.imageClosedSubgroup_isConnected hRvar
  have hQsolvable := q.imageClosedSubgroup_isSolvable hR.solvable
  exact hS.maximal Q hQnormal hQconnected hQsolvable

/-- A surjective morphism maps a source radical onto a target radical when
the target-radical preimage restriction has solvable kernel. -/
private lemma IsRadicalSubgroup.imageClosedSubgroup_eq_of_surjective_of_preimageRestriction_kernel_isSolvable
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hf : Function.Surjective f.onPoints)
    {R : ClosedSubgroup G} (hR : IsRadicalSubgroup R)
    {S : ClosedSubgroup H} (hS : IsRadicalSubgroup S)
    (hker : Group.IsSolvable (f.preimageRestriction S).kernel) :
    (f.comp R.inclusion).imageClosedSubgroup = S := by
  let P := f.closedSubgroupPreimage S
  let I := P.identityComponentAmbient
  let Q := (f.comp R.inclusion).imageClosedSubgroup
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · exact hR.imageClosedSubgroup_le_of_surjective f hf hS
  · have hPsolvable : Group.IsSolvable (Variety.Point P.carrierVariety) :=
      f.closedSubgroupPreimage_isSolvable_of_kernel S hS.solvable hker
    let : Group.IsSolvable (Variety.Point P.carrierVariety) := hPsolvable
    let iP := I.inclusion.codRestrictClosedSubgroup P fun x ↦
      P.identityComponentAmbient_le (I.pointEquiv x).property
    have hiP : Function.Injective iP.onPoints := by
      intro x y hxy
      apply I.inclusion_injective
      have hxyAmbient := congrArg P.inclusion.onPoints hxy
      simpa [iP, Morphism.codRestrictClosedSubgroup_inclusion_apply] using
        hxyAmbient
    have hIsolvable : Group.IsSolvable (Variety.Point I.carrierVariety) :=
      Group.isSolvable_of_isSolvable_injective hiP
    have hInormal : I.toSubgroup.Normal :=
      P.identityComponentAmbient_normal_of_normal
        (f.closedSubgroupPreimage_normal hS.normal)
    have hIconnected : _root_.IsConnected (I : Set (Variety.Point G)) :=
      P.identityComponentAmbient_isConnected
    have hIR : I ≤ R := hR.maximal I hInormal hIconnected hIsolvable
    have hIimage : (f.comp I.inclusion).imageClosedSubgroup = S :=
      f.closedSubgroupPreimage_identityComponent_image_eq hf S hS.connected
    intro y hy
    have hyImage : y ∈ (f.comp I.inclusion).imageClosedSubgroup := by
      rw [hIimage]
      exact hy
    change y ∈ (f.comp I.inclusion).image at hyImage
    rcases hyImage with ⟨x, hx⟩
    change y ∈ (f.comp R.inclusion).image
    let xG := I.inclusion.onPoints x
    have hxR : xG ∈ R := hIR (I.pointEquiv x).property
    let xR : Variety.Point R.carrierVariety := R.pointEquiv.symm ⟨xG, hxR⟩
    refine ⟨xR, ?_⟩
    change f.onPoints (R.inclusion.onPoints xR) = y
    have hxRAmbient : R.inclusion.onPoints xR = xG := by
      change (R.pointEquiv xR).val = xG
      dsimp only [xR]
      rw [R.pointEquiv.apply_symm_apply]
    rw [hxRAmbient]
    exact hx

/-- A surjective morphism with solvable kernel maps a source radical exactly
onto a target radical. -/
public theorem IsRadicalSubgroup.imageClosedSubgroup_eq_of_surjective_of_kernel_isSolvable
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hf : Function.Surjective f.onPoints)
    {R : ClosedSubgroup G} (hR : IsRadicalSubgroup R)
    {S : ClosedSubgroup H} (hS : IsRadicalSubgroup S)
    (hker : Group.IsSolvable f.kernel) :
    (f.comp R.inclusion).imageClosedSubgroup = S :=
  hR.imageClosedSubgroup_eq_of_surjective_of_preimageRestriction_kernel_isSolvable
    f hf hS (f.preimageRestriction_kernel_isSolvable_of_kernel S hker)

end Theory.AlgebraicGroup
