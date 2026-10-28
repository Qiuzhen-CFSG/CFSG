module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondQuotient.CubicLift
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.BinaryIndexThreeOrbitSpan

/-!
# The literal binary action on R₂/S₂

The original second quotient acts by conjugation on its elementary core.
The lifted cubic supplied by the preceding module has cube acting trivially
and has no nonzero fixed vector. Both assertions retain the original quotient
projection, giving the actual input to the index-three orbit-span argument.

Source: Aschbacher–Smith, J.4.4(2), printed p.441.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)

instance Plane.secondCoreNormal : (p.secondBar p.R₂).Normal := by
  let : (p.R₂.subgroupOf p.parabolic).Normal :=
    normal_subgroupOf_of_le_normalizer p.R₂_normalized
  exact Subgroup.Normal.map inferInstance p.secondMap (QuotientGroup.mk'_surjective _)

instance Plane.secondCoreElementary : IsElementaryAbelian 2 (p.secondBar p.R₂) :=
  p.secondBar_R₂_elementary

/-- The actual conjugation representation, with no replacement quotient. -/
def Plane.secondAction : Representation (ZMod 2) p.SecondQuotient
    (Additive (p.secondBar p.R₂)) where
  toFun h := (MulAut.conjNormal h : MulAut (p.secondBar p.R₂)).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (MulAut.conjNormal 1 v.toMul)=v
    rw [map_one]
    rfl
  map_mul' h k := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (MulAut.conjNormal (h*k) v.toMul)=_
    rw [map_mul]
    rfl

theorem Plane.secondAction_apply (h:p.SecondQuotient) (v:Additive (p.secondBar p.R₂)) :
    ((p.secondAction h v).toMul:p.SecondQuotient)=h*(v.toMul:p.SecondQuotient)*h⁻¹ := by
  rfl

/-- The actual quotient action has a fixed-free cubic operator. -/
theorem Plane.exists_second_cubic_action :
    ∃ c:p.SecondQuotient,
      (∀ v,p.secondAction c (p.secondAction c (p.secondAction c v))=v) ∧
      ∀ v,p.secondAction c v=v → v=0 := by
  obtain ⟨c,ho,hf⟩ := p.exists_second_cubic_lift
  refine ⟨p.secondMap c,?_,?_⟩
  · intro v
    have hcS : ((c^3:p.parabolic):G)∈d.toTypeRuSetup.S := by
      have he : c^3∈p.parabolicMap.ker := by
        change p.parabolicMap (c^3)=1
        rw [map_pow]
        simpa only [ho] using pow_orderOf_eq_one (p.parabolicMap c)
      rw [p.parabolicMap_kernel] at he
      exact he
    have hcbar : p.secondMap (c^3)∈p.secondBar d.toTypeRuSetup.S := ⟨c^3,hcS,rfl⟩
    have hcent := p.secondBar_S_centralizes_R₂ hcbar v.toMul v.toMul.property
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [p.secondAction_apply,p.secondAction_apply,p.secondAction_apply]
    have he : p.secondMap c*(p.secondMap c*(p.secondMap c*(v.toMul:p.SecondQuotient)*
      (p.secondMap c)⁻¹)*(p.secondMap c)⁻¹)*(p.secondMap c)⁻¹=
      p.secondMap (c^3)*(v.toMul:p.SecondQuotient)*(p.secondMap (c^3))⁻¹ := by
      rw [map_pow,pow_succ,pow_two];group
    rw [he,← hcent,mul_inv_cancel_right]
  · intro v hv
    have he := congrArg (fun w:Additive (p.secondBar p.R₂) => (w.toMul:p.SecondQuotient)) hv
    rw [p.secondAction_apply] at he
    obtain ⟨a,ha,hea⟩ := v.toMul.property
    have hcomm : ((⁅c,a⁆:p.parabolic):G)∈p.S₂ := by
      apply (p.secondMap_eq_one _).mp
      rw [map_commutatorElement,commutatorElement_def,hea,he,mul_inv_cancel]
    have hzero : (v.toMul:p.SecondQuotient)=1 := by
      rw [← hea]
      exact (p.secondMap_eq_one a).mpr (hf a ha hcomm)
    exact Additive.toMul.injective (Subtype.ext hzero)

end CFSG.Quasithin.ChapterJ.RuSubgroup
