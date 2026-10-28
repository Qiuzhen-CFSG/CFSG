module

public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricExtraction
public import Stellmacher.LaterDefs
public import Theory.GroupAction.Defs

/-!
# The actual neighbor center moves only inside its action support

Let a genuine geometric extraction have its residual image inside D in the
literal action on the local module modulo its center. The extracted neighbor
center then maps into the join of D's commutator support and the original
neighbor-center image. The action formula and its exact normality instance
are explicit; no alternate quotient action is substituted.

The recorded residual conjugator lies in the local stabilizer and maps into
D. Center covariance writes every extracted-center element as the conjugate
of an original-center element by that same conjugator. The exact action
formula identifies their quotient images. Their action difference is a
generator of the commutator support, and multiplying by the original point
gives the claimed join containment.

This is the geometric support assertion in Stellmacher (9.10), printed p.57,
following (3)--(4). The later canonical factor is a supplied instance of D;
no factor theorem, dimension count, or identification of extraction groups is
assumed in this action-formula bridge.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

public theorem nine_ten_conjugated_center_image_le_support_join
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (vertex neighbor : Γ.Vertex)
    (hneighbor : neighbor ∈ neighborhood Γ vertex)
    (V E A0 : Subgroup G) (actor : G)
    (data : NineThreeGeometricData Γ vertex neighbor V E A0 actor)
    [hN : ((ZAt Γ vertex).subgroupOf (VAt Γ vertex)).Normal]
    (action : GAt Γ vertex →* MulAut
      (VAt Γ vertex ⧸ (ZAt Γ vertex).subgroupOf (VAt Γ vertex)))
    (hformula : ∀ mover : GAt Γ vertex, ∀ point : VAt Γ vertex,
      action mover (QuotientGroup.mk' ((ZAt Γ vertex).subgroupOf (VAt Γ vertex)) point) =
        QuotientGroup.mk' ((ZAt Γ vertex).subgroupOf (VAt Γ vertex))
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp
              (stabilizer_le_normalizer_v Γ vertex mover.property) point).mp point.property⟩)
    (D : Subgroup action.range)
    (hresidual : ((twoResidualIn E).subgroupOf (GAt Γ vertex)).map
      action.rangeRestrict ≤ D) :
    ((ZAt Γ (Γ.act data.x⁻¹ neighbor)).subgroupOf (VAt Γ vertex)).map
        (QuotientGroup.mk' ((ZAt Γ vertex).subgroupOf (VAt Γ vertex))) ≤
      commutatorAction D (VAt Γ vertex ⧸ (ZAt Γ vertex).subgroupOf (VAt Γ vertex)) ⊔
        ((ZAt Γ neighbor).subgroupOf (VAt Γ vertex)).map
          (QuotientGroup.mk' ((ZAt Γ vertex).subgroupOf (VAt Γ vertex))) := by
  let P := GAt Γ vertex
  let U := VAt Γ vertex
  let Z := (ZAt Γ vertex).subgroupOf U
  let quotient := QuotientGroup.mk' Z
  let W := U ⧸ Z
  let support := commutatorAction D W
  let oldCenter := ((ZAt Γ neighbor).subgroupOf U).map quotient
  have hxP : data.x ∈ P := data.group_le ((twoResidualIn_le E) data.residual_mem)
  let mover : P := ⟨data.x, hxP⟩
  have hmover : action.rangeRestrict mover ∈ D :=
    hresidual (Subgroup.mem_map_of_mem action.rangeRestrict data.residual_mem)
  have hZU : ZAt Γ neighbor ≤ U := by
    change ZAt Γ neighbor ≤ VAt Γ vertex
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hcenter : ZAt Γ (Γ.act data.x⁻¹ neighbor) =
      (ZAt Γ neighbor).map (MulAut.conj data.x).toMonoidHom := by
    change z Γ (Γ.act data.x⁻¹ neighbor) = (z Γ neighbor).map _
    rw [z_act, inv_inv]
  rintro value ⟨point, hpoint, rfl⟩
  change (point : G) ∈ ZAt Γ (Γ.act data.x⁻¹ neighbor) at hpoint
  rw [hcenter] at hpoint
  obtain ⟨original, horiginal, hpoint⟩ := hpoint
  let originalU : U := ⟨original, hZU horiginal⟩
  have hpointImage : action mover (quotient originalU) = quotient point := by
    rw [hformula]
    apply congrArg quotient
    apply Subtype.ext
    exact hpoint
  have horiginalImage : quotient originalU ∈ oldCenter :=
    Subgroup.mem_map_of_mem quotient horiginal
  have hdisplacement : (quotient originalU)⁻¹ * action mover (quotient originalU) ∈ support := by
    change (quotient originalU)⁻¹ * action mover (quotient originalU) ∈ commutatorAction D W
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure
      ⟨⟨action.rangeRestrict mover, hmover⟩, quotient originalU, rfl⟩
  have hmem := (support ⊔ oldCenter).mul_mem
    ((show oldCenter ≤ support ⊔ oldCenter from le_sup_right) horiginalImage)
    ((show support ≤ support ⊔ oldCenter from le_sup_left) hdisplacement)
  simpa only [mul_inv_cancel_left, hpointImage] using hmem

end Stellmacher.SectionNine
