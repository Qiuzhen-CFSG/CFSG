module
public import Theory.GroupTheory.ExtraspecialSquare
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Fixed and displacement spaces on an extraspecial central quotient

If an automorphism fixes one generating seed modulo the center and has
no noncentral fixed lifts in the other, its full fixed space is exactly
the first seed image. For a binary involution this is also the displacement
space when the fixed dimension is half the total dimension.

These statements retain the literal central quotient and conjugation
coordinates. Their source consumer is the rank-four generator calculation
in Aschbacher--Smith F.9.5(6.ii), printed pp.319--320.
-/

public section
namespace Theory.GroupTheory.ExtraspecialSquare
open Subgroup
variable {Q : Type*} [Group Q] [IsExtraspecial 2 Q]

/-- A central-quotient vector is fixed precisely when its displacement lift is central. -/
theorem linearAction_mk_fixed_iff (a : MulAut Q) (x : Q) :
    linearAction Q a (Additive.ofMul (QuotientGroup.mk' (center Q) x)) =
      Additive.ofMul (QuotientGroup.mk' (center Q) x) ↔ a x / x ∈ center Q := by
  rw [linearAction_apply, quotientAut_apply_mk]
  exact Additive.ofMul.injective.eq_iff.trans QuotientGroup.eq_iff_div_mem

/-- A fixed generating seed and separation on the other seed identify the full fixed space. -/
theorem fixed_ker_eq_imageSpace (a : MulAut Q) (A B : Subgroup Q)
    (hgen : A ⊔ B = ⊤)
    (hA : ∀ x ∈ A, a x / x ∈ center Q)
    (hB : ∀ x ∈ B, a x / x ∈ center Q → x ∈ center Q) :
    LinearMap.ker ((linearAction Q a).toLinearMap - LinearMap.id) = imageSpace Q A := by
  let f := (linearAction Q a).toLinearMap - LinearMap.id
  have hAK : imageSpace Q A ≤ f.ker := by
    rintro v ⟨x,hx,he⟩
    have hv : v = Additive.ofMul (QuotientGroup.mk' (center Q) x) := congrArg Additive.ofMul he.symm
    rw [hv]
    apply sub_eq_zero.mpr
    exact (linearAction_mk_fixed_iff a x).mpr (hA x hx)
  have hBK : Disjoint (imageSpace Q B) f.ker := by
    apply Submodule.disjoint_def.mpr
    rintro v ⟨x,hx,he⟩ hv
    have he' : v = Additive.ofMul (QuotientGroup.mk' (center Q) x) := congrArg Additive.ofMul he.symm
    rw [he'] at hv ⊢
    apply congrArg Additive.ofMul
    exact (QuotientGroup.eq_one_iff x).mpr
      (hB x hx ((linearAction_mk_fixed_iff a x).mp (sub_eq_zero.mp hv)))
  have hsum : imageSpace Q A ⊔ imageSpace Q B = ⊤ := by
    rw [←imageSpace_sup,hgen,imageSpace_top]
  apply le_antisymm _ hAK
  intro v hv
  obtain ⟨x,hx,y,hy,he⟩ := Submodule.mem_sup.mp (hsum.symm ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) (Space Q))))
  have hyK : y ∈ f.ker := by
    have hxy : x+y ∈ f.ker := he.symm ▸ hv
    simpa only [add_sub_cancel_left] using f.ker.sub_mem hxy (hAK hx)
  have hy0 := Submodule.disjoint_def.mp hBK y hy hyK
  rw [hy0,add_zero] at he
  exact he ▸ hx

/-- A binary involution with a half-dimensional fixed space has that same displacement space. -/
theorem range_eq_imageSpace_of_half_fixed [Finite Q]
    (a : MulAut Q) (ha : a^2=1) (A : Subgroup Q) (n : ℕ)
    (hd : Module.finrank (ZMod 2) (Space Q) = 2*n)
    (hA : Module.finrank (ZMod 2) (imageSpace Q A) = n)
    (hk : LinearMap.ker ((linearAction Q a).toLinearMap - LinearMap.id) = imageSpace Q A) :
    LinearMap.range ((linearAction Q a).toLinearMap - LinearMap.id) = imageSpace Q A := by
  let e := linearAction Q a
  let f := e.toLinearMap - LinearMap.id
  have hsq : e^2=1 := by rw [←map_pow,ha,map_one]
  have he (v : Space Q) : e (e v) = v := by
    simpa only [pow_two,LinearEquiv.mul_apply,LinearEquiv.coe_one, id_eq] using
      congrArg (fun t : Space Q ≃ₗ[ZMod 2] Space Q => t v) hsq
  have hneg (v : Space Q) : -v=v := by
    have hh := congrArg (fun r : ZMod 2 => r • v) (show (-1 : ZMod 2) = 1 by decide)
    simpa only [neg_one_smul,one_smul] using hh
  have hle : f.range ≤ f.ker := by
    rintro _ ⟨v,rfl⟩
    change e (e v-v)-(e v-v)=0
    calc e (e v-v)-(e v-v) = (v-e v)-(e v-v) := by rw [map_sub,he]
      _ = -(e v-v)-(e v-v) := by rw [neg_sub]
      _ = 0 := by rw [hneg,sub_self]
  apply Submodule.eq_of_le_of_finrank_eq (hle.trans hk.le)
  have hr := LinearMap.finrank_range_add_finrank_ker f
  rw [hk,hA,hd] at hr
  rw [hA]
  omega

end Theory.GroupTheory.ExtraspecialSquare
