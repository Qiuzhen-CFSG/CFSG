module
public import Theory.AlgebraicGroup.Borel.SurjectiveImageMaximalTorus
public import Theory.AlgebraicGroup.Borel.Existence
public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.Morphism.Solvable
public import Theory.AlgebraicGroup.Tori.Maximal.theorem_1_4_3_b

/-!
# Maximal tori under a morphism with solvable kernel

Let `f` be a surjective algebraic-group morphism with solvable point kernel.
The connected preimage of a target torus is solvable and maps onto that torus.
Enlarge this preimage to a Borel. The torus–unipotent decomposition inside that
Borel proves that the image of the original maximal torus is already maximal.

This is the solvable-kernel case of Borel, *Linear Algebraic Groups*, IV,
§11.20, used for the actual radical quotient in §13.11. It does not invoke the
legacy general maximal-torus image theorem.
-/

public section
namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]

/-- A surjective morphism with solvable kernel sends maximal tori to maximal tori. -/
theorem maximalTorus_image_of_solvable_kernel
    (f : AlgebraicGroup.Morphism G H) (hf : Function.Surjective f.onPoints)
    (hk : Group.IsSolvable f.kernel) {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    IsMaximalTorus (f.comp T.inclusion).imageClosedSubgroup := by
  refine ⟨morphism_image_isTorus (f.comp T.inclusion) hT.1, ?_⟩
  intro A hA hTA
  let P := f.closedSubgroupPreimage A
  let I := P.identityComponentAmbient
  have hAc : _root_.IsConnected (A : Set (Variety.Point H)) := by
    let : ConnectedSpace (Variety.Point A.carrierVariety) :=
      connectedSpace_iff_univ.mpr hA.isConnected
    change _root_.IsConnected (A.toSubgroup : Set (Variety.Point H))
    rw [← A.range_inclusion]
    exact isConnected_range A.inclusion.toVariety.continuous
  have hPs : Group.IsSolvable (Variety.Point P.carrierVariety) :=
    f.closedSubgroupPreimage_isSolvable_of_kernel A
      (Group.isSolvable_of_comm (isMulCommutative_iff.mp hA.isMulCommutative))
      (f.preimageRestriction_kernel_isSolvable_of_kernel A hk)
  let iP := I.inclusion.codRestrictClosedSubgroup P
    (fun x => P.identityComponentAmbient_le (I.pointEquiv x).property)
  have hiP : Function.Injective iP.onPoints := by
    intro x y hxy
    apply I.inclusion_injective
    simpa [iP, Morphism.codRestrictClosedSubgroup_inclusion_apply] using
      congrArg P.inclusion.onPoints hxy
  have hIs : Group.IsSolvable (Variety.Point I.carrierVariety) := by
    let := hPs
    exact Group.isSolvable_of_isSolvable_injective hiP
  obtain ⟨B, hB, hIB⟩ := exists_borelSubgroup_containing_connected_solvable
    I P.identityComponentAmbient_isConnected hIs
  have hTP : T ≤ P := by
    intro t ht
    apply hTA
    exact ⟨T.pointEquiv.symm ⟨t,ht⟩, rfl⟩
  have hTB : T ≤ B := fun x hx =>
    hIB (maximalTorus_le_identityComponentAmbient_of_le T P hT hTP hx)
  have hIA := f.closedSubgroupPreimage_identityComponent_image_eq hf A hAc
  have hAB : A ≤ (f.comp B.inclusion).imageClosedSubgroup := by
    rw [← hIA]
    rintro y ⟨x,rfl⟩
    exact ⟨B.pointEquiv.symm ⟨I.inclusion.onPoints x,hIB (I.pointEquiv x).property⟩,rfl⟩
  exact (image_maximalTorusIn_image_of_borel f hf B T hB hT hTB).2.2 A hA hAB hTA

end Theory.AlgebraicGroup
