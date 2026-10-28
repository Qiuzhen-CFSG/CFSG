module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.NativeModel.IntersectionCoordinates
public import Theory.GroupTheory.Recognition.UnitaryFourThree.IntersectionTransfer
/-!
# All fused core intersections in the actual native PSU₄(3)

The crossing-coordinate certificate identifies the inverse image of one
intersection in Q₈ × Q₈: it has order eight and the actual projective kernel
has order two. Thus the intersection has order four. The residual orbit
from the original centralizer hypothesis transfers this equality to every
right conjugate of the marked involution in the core outside its line.

Source: Aschbacher, *Sporadic Groups* (1994), definition on printed p.244.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
open RepresentativeCore
open RepresentativeCore.QuotientCore.Blocks
open Theory.GroupTheory.Recognition.UnitaryFourThree (core conjugate)

def ambientPair : QuaternionGroup 2 × QuaternionGroup 2 →* Carrier 4 :=
  standardCentralizer.subtype.comp quaternionPair

theorem ambientPair_range : ambientPair.range=nativeCore := MonoidHom.range_comp _ _

theorem project_mem_nativeCore_iff (g : SU) : project 4 g ∈ nativeCore ↔
    ∃(q : QuaternionGroup 2 × QuaternionGroup 2) (u : FiniteField.Nineˣ),
      g.val.val=u.val • RepresentativeCore.block (quaternionMatrix q.1) (quaternionMatrix q.2) := by
  constructor
  · intro hg
    have hgC : project 4 g∈standardCentralizer := map_subtype_le _ hg
    exact (mem_core_iff g hgC).mp ((mem_map_iff_mem standardCentralizer.subtype_injective).mp hg)
  · rintro ⟨q,u,hu⟩
    have he : ambientPair q=project 4 g := by
      apply Subtype.ext
      change ProjGenLinGroup.mk (quaternionPairSU q).val=ProjGenLinGroup.mk g.val
      apply ProjGenLinGroup.mk_eq_mk_iff.mpr
      refine ⟨u,Units.ext ?_⟩
      change RepresentativeCore.block (quaternionMatrix q.1) (quaternionMatrix q.2) * Matrix.scalar (Fin 4) u.val=g.val.val
      simpa only [Matrix.scalar_apply,← Matrix.smul_eq_mul_diagonal] using hu.symm
    exact he ▸ ambientPair_range ▸ (show ambientPair q ∈ ambientPair.range from ⟨q,rfl⟩)

theorem fusion_inv : fusion⁻¹=fusion := by
  change (project 4 fusionSU)⁻¹=project 4 fusionSU
  rw [← map_inv,fusionSU_inv]

theorem crossed_mem_iff (q : QuaternionGroup 2 × QuaternionGroup 2) :
    fusion * ambientPair q * fusion⁻¹ ∈ nativeCore ↔ crossedCondition q := by
  change project 4 fusionSU * project 4 (quaternionPairSU q) * (project 4 fusionSU)⁻¹ ∈ nativeCore ↔ _
  rw [← map_inv,← map_mul,← map_mul,project_mem_nativeCore_iff]
  have hm : (fusionSU * quaternionPairSU q * fusionSU⁻¹).val.val=crossedQuaternion q := by
    rw [fusionSU_inv]
    rfl
  rw [hm]
  constructor
  · rintro ⟨r,u,hu⟩
    exact crossedCondition_of_scalar q r u.val u.ne_zero hu
  · intro hq
    obtain ⟨r,u,hu,he⟩ := crossedCondition_suffices q hq
    exact ⟨r,Units.mk0 u hu,he⟩

def nativeIntersection : Subgroup (Carrier 4) := nativeCore ⊓ conjugate nativeCore fusion

def intersectionPreimage : Subgroup (QuaternionGroup 2 × QuaternionGroup 2) :=
  nativeIntersection.comap ambientPair

theorem intersectionPreimage_iff (q : QuaternionGroup 2 × QuaternionGroup 2) :
    q∈intersectionPreimage ↔ crossedCondition q := by
  change ambientPair q∈nativeCore ∧ ambientPair q∈nativeCore.map (MulAut.conj fusion⁻¹).toMonoidHom ↔ _
  have hq : ambientPair q∈nativeCore := ambientPair_range ▸ ⟨q,rfl⟩
  rw [and_iff_right hq,mem_map_equiv]
  change fusion * ambientPair q * fusion⁻¹ ∈ nativeCore ↔ _
  exact crossed_mem_iff q

theorem intersectionPreimage_card : Nat.card intersectionPreimage=8 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight intersectionPreimage_iff),Nat.card_eq_fintype_card]
  exact crossedCondition_card

def intersectionProjection : intersectionPreimage →* nativeIntersection :=
  (ambientPair.comp intersectionPreimage.subtype).codRestrict _ (fun q=>q.property)

theorem intersectionProjection_surjective : Function.Surjective intersectionProjection := by
  intro x
  obtain ⟨q,hq⟩ := ambientPair_range.symm ▸ x.property.1
  refine ⟨⟨q,?_⟩,Subtype.ext hq⟩
  change ambientPair q∈nativeIntersection
  rw [hq]
  exact x.property

theorem intersectionProjection_kernel_card : Nat.card intersectionProjection.ker=2 := by
  have hker : intersectionProjection.ker=ambientPair.ker.subgroupOf intersectionPreimage := by
    ext q
    change intersectionProjection q=1 ↔ ambientPair q.val=1
    exact Subtype.ext_iff
  have hamb : ambientPair.ker=quaternionPair.ker := MonoidHom.ker_comp_of_injective _ _ standardCentralizer.subtype_injective
  rw [hker,Nat.card_congr (subgroupOfEquivOfLe (show ambientPair.ker ≤ intersectionPreimage from
    ker_le_comap ambientPair nativeIntersection)).toEquiv,hamb]
  exact quaternionPair_kernel_card

theorem nativeIntersection_card : Nat.card nativeIntersection=4 := by
  have hc := intersectionProjection.ker.card_mul_index
  rw [index_ker,intersectionProjection_kernel_card,intersectionPreimage_card,
    MonoidHom.range_eq_top_of_surjective _ intersectionProjection_surjective,card_top] at hc
  omega

theorem native_intersection_card : ∀g : Carrier 4,
    g⁻¹ * standardInvolution * g ∈ core standardInvolution →
    g⁻¹ * standardInvolution * g ∉ zpowers standardInvolution →
    Nat.card (core standardInvolution ⊓ conjugate (core standardInvolution) g : Subgroup (Carrier 4))=4 := by
  have hg : fusion⁻¹*standardInvolution*fusion ∈ core standardInvolution := by
    rw [fusion_conjugate,native_core_eq]
    exact mem_map_of_mem standardCentralizer.subtype (quaternionPair_mem _)
  have hz : fusion⁻¹*standardInvolution*fusion ∉ zpowers standardInvolution := by
    rw [fusion_conjugate]; exact quaternion_fused_not_line
  apply native_centralizerHypothesis.intersection_card_of_representative fusion hg hz
  rw [native_core_eq]
  exact nativeIntersection_card
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
