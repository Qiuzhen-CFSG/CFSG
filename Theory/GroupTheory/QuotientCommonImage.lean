module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index

/-!
# The common quotient of two group images

For maps p : M -> N and a surjection q : M -> C with C abelian,
C/q(ker p) is the quotient of p(M) by p(ker q). The construction keeps
both original maps: its representative equation is part of the API.
The common quotient's order divides the order of p(M).

This is the two-projection form of the isomorphism theorems. The chief-section
consumer uses the section projection and the original local two-core
quotient, so that neither section endpoint nor either kernel is replaced.
Source application: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.763--764.
-/

open Subgroup
namespace QuotientGroup.CommonImage
@[expose] public noncomputable section
variable {M N C : Type*} [Group M] [Group N] [CommGroup C]
    (p : M →* N) (q : M →* C) (hq : Function.Surjective q)

/-- The part of the target killed by the second projection. -/
def kernelImage : Subgroup C := p.ker.map q

/-- The common quotient reached from the actual image of the second map. -/
def map : p.range →* C ⧸ kernelImage p q :=
  (QuotientGroup.lift p.ker ((QuotientGroup.mk' (kernelImage p q)).comp q)
    (by
      intro x hx
      change QuotientGroup.mk' (kernelImage p q) (q x) = 1
      exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem q hx))).comp
    (QuotientGroup.quotientKerEquivRange p).symm.toMonoidHom

@[simp] theorem map_apply (x : M) :
    map p q (p.rangeRestrict x) = QuotientGroup.mk' (kernelImage p q) (q x) := by
  have he : (QuotientGroup.quotientKerEquivRange p).symm (p.rangeRestrict x) =
      QuotientGroup.mk' p.ker x := by
    apply (QuotientGroup.quotientKerEquivRange p).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  unfold map
  dsimp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
  rw [he]
  rfl

include hq in
theorem map_surjective : Function.Surjective (map p q) := by
  intro w
  obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective (kernelImage p q) w
  obtain ⟨x,rfl⟩ := hq c
  exact ⟨p.rangeRestrict x,map_apply p q x⟩

/-- The denominator is precisely the image of the first kernel. -/
theorem map_ker : (map p q).ker = q.ker.map p.rangeRestrict := by
  ext y
  obtain ⟨x,rfl⟩ := p.rangeRestrict_surjective y
  rw [MonoidHom.mem_ker,map_apply,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨z,hz,hzx⟩
    refine ⟨z⁻¹*x,?_,?_⟩
    · change q (z⁻¹*x) = 1
      rw [map_mul,map_inv,hzx,inv_mul_cancel]
    · apply Subtype.ext
      change p (z⁻¹*x) = p x
      rw [map_mul,map_inv,show p z = 1 from hz,inv_one,one_mul]
  · rintro ⟨z,hz,hzx⟩
    refine ⟨x*z⁻¹,?_,?_⟩
    · change p (x*z⁻¹) = 1
      have hpz : p z = p x := congrArg Subtype.val hzx
      rw [map_mul,map_inv,hpz,mul_inv_cancel]
    · rw [map_mul,map_inv,show q z = 1 from hz,inv_one,mul_one]

instance imageKernel_normal : (q.ker.map p.rangeRestrict).Normal :=
  Subgroup.Normal.map inferInstance p.rangeRestrict p.rangeRestrict_surjective

/-- Both sides are quotients of the original maps, with no replacement of
any selected section endpoint. -/
def equiv : (p.range ⧸ q.ker.map p.rangeRestrict) ≃* (C ⧸ kernelImage p q) :=
  (QuotientGroup.quotientMulEquivOfEq (map_ker p q).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (map p q) (map_surjective p q hq))

@[simp] theorem equiv_mk (x : M) :
    equiv p q hq (QuotientGroup.mk' (q.ker.map p.rangeRestrict) (p.rangeRestrict x)) =
      QuotientGroup.mk' (kernelImage p q) (q x) := by
  change map p q (p.rangeRestrict x) = _
  exact map_apply p q x

include hq in
/-- The common quotient's order divides the order of the actual second image. -/
theorem card_quotient_dvd : Nat.card (C ⧸ kernelImage p q) ∣ Nat.card p.range :=
  Subgroup.card_dvd_of_surjective (map p q) (map_surjective p q hq)

end
end QuotientGroup.CommonImage
