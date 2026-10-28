module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity.Marking
public import Theory.GroupTheory.QuaternionSwapModel.MarkedSylow.Transport

/-!
# The actual marked Aut(M₁₂) pair

Transport the split movement subgroup through the whole overlap of the concrete
pair.  Its quaternion core and central mark are identified with the original
first-parabolic wreath data, so the second-parabolic geometry remains on the
same source pair.  This supplies the marked normalizer argument in 14.2.21.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
open SourceModel.Transport
open Sporadic.Mathieu.M12ExceptionalExtension FirstParabolic
open QuaternionSwapModel.MarkedSylow
variable {G : Type*} [Group G] {H X : Subgroup G}
variable (r : RankTwoAmalgam.Iso
  (RankTwoAmalgam.ofSubgroups H (H ⊓ X) X inf_le_left inf_le_right)
  ChapterF.GreenBook.AutMathieuTwelve.autAmalgam)

private def modelMovement : QuaternionSwapModel.QH →* overlap :=
  SecondCoordinates.movement.codRestrict overlap SecondCoordinates.movement_mem_overlap

/-- The movement subgroup is embedded through the original whole overlap. -/
def movement : QuaternionSwapModel.QH →* G := by
  exact (H ⊓ X).subtype.comp ((pairIso r).middle.symm.toMonoidHom.comp
    (SecondCoordinates.movement.codRestrict overlap SecondCoordinates.movement_mem_overlap))

theorem movement_injective : Function.Injective (movement r) :=
  (H ⊓ X).subtype_injective.comp ((pairIso r).middle.symm.injective.comp
    (fun _ _ h => SecondCoordinates.movement_injective (congrArg Subtype.val h)))

theorem movement_mem (q : QuaternionSwapModel.QH) : movement r q ∈ H ⊓ X :=
  ((pairIso r).middle.symm (modelMovement q)).property

theorem movement_left (q : QuaternionSwapModel.QH) :
    ((pairIso r).left ⟨movement r q,(movement_mem r q).1⟩ : Carrier) =
      SecondCoordinates.movement q := by
  have hh := pair_left r ((pairIso r).middle.symm (modelMovement q))
  rw [MulEquiv.apply_symm_apply] at hh
  exact hh

theorem movement_right (q : QuaternionSwapModel.QH) :
    ((pairIso r).right ⟨movement r q,(movement_mem r q).2⟩ : Carrier) =
      SecondCoordinates.movement q := by
  have hh := pair_right r ((pairIso r).middle.symm (modelMovement q))
  rw [MulEquiv.apply_symm_apply] at hh
  exact hh

/-- All whole-overlap normal forms and second-parabolic generator equations
hold on the actual source pair. -/
theorem movement_geometry : Nonempty (SecondGeometry (movement r) (H ⊓ X) X) := by
  let j : secondParabolic →* G := X.subtype.comp (pairIso r).right.symm.toMonoidHom
  have hj : Function.Injective j := X.subtype_injective.comp (pairIso r).right.symm.injective
  have hf : j.comp VerifiedPair.secondGeometry.into = movement r := by
    apply MonoidHom.ext
    intro q
    change (((pairIso r).right.symm (VerifiedPair.secondGeometry.into q) : X) : G) = movement r q
    change X.subtype ((pairIso r).right.symm (VerifiedPair.secondGeometry.into q)) =
      X.subtype ⟨movement r q,(movement_mem r q).2⟩
    apply congrArg X.subtype
    apply (pairIso r).right.injective
    apply Subtype.ext
    rw [MulEquiv.apply_symm_apply,movement_right]
    rfl
  have hU : (overlap.subgroupOf secondParabolic).map j = H ⊓ X := by
    ext g
    constructor
    · rintro ⟨a,ha,rfl⟩
      let b : overlap := ⟨a,ha⟩
      have he := congrArg Subtype.val ((pairIso r).symm.right_commutes b)
      change j a = (((pairIso r).middle.symm b : (H ⊓ X : Subgroup G)) : G) at he
      rw [he]
      exact ((pairIso r).middle.symm b).property
    · intro hg
      let b := (pairIso r).middle ⟨g,hg⟩
      refine ⟨⟨b, b.property.2⟩,b.property,?_⟩
      have he := congrArg Subtype.val ((pairIso r).symm.right_commutes b)
      change j ⟨b,b.property.2⟩ = (((pairIso r).middle.symm b : (H ⊓ X : Subgroup G)) : G) at he
      rw [he]
      exact congrArg Subtype.val ((pairIso r).middle.symm_apply_apply ⟨g,hg⟩)
  have hr : j.range = X := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ((pairIso r).right.symm a).property
    · intro hx
      exact ⟨(pairIso r).right ⟨x,hx⟩,congrArg Subtype.val
        ((pairIso r).right.symm_apply_apply ⟨x,hx⟩)⟩
  have hd := VerifiedPair.secondGeometry.transport j hj
  rw [hf,hU,hr] at hd
  exact hd

/-- The split movement core and the nonsplit first-core quotient have the
same literal quaternion base in the original group. -/
theorem movement_core : QuaternionSwapModel.QK.map (movement r) =
    (FourWreathTwo.base.comap (wreathMap r)).map (H.subtype.comp (pCore 2 H).subtype) := by
  ext x
  constructor
  · rintro ⟨q,hq,rfl⟩
    have hmod : SecondCoordinates.movement q ∈ quaternionCore := by
      have hm := mem_map_of_mem SecondCoordinates.movement hq
      rw [VerifiedPair.movement_residual_image,mapped_pCore_residual_commutator innerModel] at hm
      exact hm
    let a : H := ⟨movement r q,(movement_mem r q).1⟩
    have hac : (pairIso r).left a ∈ pCore 2 firstParabolic := by
      have hm : ((pairIso r).left a : Carrier) ∈ outerCore := by
        change ((pairIso r).left ⟨movement r q,_⟩ : Carrier) ∈ outerCore
        rw [movement_left]
        exact (show quaternionCore ≤ outerCore from le_sup_left) hmod
      have he : (pCore 2 firstParabolic).map firstParabolic.subtype = outerCore :=
        mapped_pCore_eq_outerCore innerModel
      rw [←he] at hm
      exact (mem_map_iff_mem firstParabolic.subtype_injective).mp hm
    have ha : a ∈ pCore 2 H := by
      have hm := hac
      rw [←pCore_map_iso 2 (pairIso r).left] at hm
      exact (mem_map_iff_mem (pairIso r).left.injective).mp hm
    refine ⟨⟨a,ha⟩,?_,rfl⟩
    apply (wreathMap_mem_base r _).mpr
    change ((pairIso r).left ⟨movement r q,_⟩ : Carrier) ∈ quaternionCore
    rwa [movement_left]
  · rintro ⟨a,ha,rfl⟩
    have hm := (wreathMap_mem_base r a).mp ha
    rw [←mapped_pCore_residual_commutator innerModel,←VerifiedPair.movement_residual_image] at hm
    obtain ⟨q,hq,he⟩ := hm
    refine ⟨q,hq,?_⟩
    change H.subtype ⟨movement r q,(movement_mem r q).1⟩ = H.subtype (a : H)
    apply congrArg H.subtype
    apply (pairIso r).left.injective
    apply Subtype.ext
    rw [movement_left]
    exact he

/-- The split movement mark is exactly the kernel mark of the original
first-core wreath quotient. -/
theorem movement_mark [Finite G] : QuaternionSwapModel.Z.map (movement r) =
    (markedCore r).map (H.subtype.comp (pCore 2 H).subtype) := by
  have hmem (q : QuaternionSwapModel.QH) (hq : q ∈ QuaternionSwapModel.Z) :
      movement r q ∈ (markedCore r).map (H.subtype.comp (pCore 2 H).subtype) := by
    have hqc := QuaternionSwapModel.Z_le_QK hq
    obtain ⟨a,ha,he⟩ := movement_core r ▸ (mem_map_of_mem (movement r) hqc)
    refine ⟨a,?_,he⟩
    change (coreEquiv r a).val ∈ distinguished
    rw [coreEquiv_val]
    have he' : (a : H) = ⟨movement r q,(movement_mem r q).1⟩ := Subtype.ext he
    rw [he',movement_left,SourceModel.distinguished_movement]
    exact mem_map_of_mem SecondCoordinates.movement hq
  apply eq_of_le_of_card_ge
  · rintro _ ⟨q,hq,rfl⟩
    exact hmem q hq
  · have hk : Function.Injective (H.subtype.comp (pCore 2 H).subtype) :=
      H.subtype_injective.comp (pCore 2 H).subtype_injective
    rw [card_map_of_injective (movement_injective r),card_map_of_injective hk,
      QuaternionSwapModel.card_Z,Nat.card_congr (markedEquiv r).toEquiv,card_distinguished]

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
end
