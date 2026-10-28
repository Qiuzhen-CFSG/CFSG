module

public import Theory.GroupTheory.QuaternionCentralProductInvolutionProducts.Model
public import Theory.GroupTheory.QuaternionCentralProductC2Rank
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Products of involutions and outer quaternion actions

For an involutive automorphism outer on both factors of Q₈ ◦ Q₈, a square-one
element has trivial norm whenever its norm is central. Exactly eight
square-one elements have norm whose square is nonidentity.

Multiplication of the actual embedded quaternion factors gives a surjection
Q₈ × Q₈ → Q. The intersection of order two identifies the two central
involutions; the order of Q then proves that the kernel is exactly their
diagonal. Restricting the given automorphism to each factor intertwines this
map with the two quaternion actions, so the finite norm calculation applies
to the original group and automorphism.

Source: Aschbacher, *A 2-local characterization of M12*, Lemma 2.3 and the
product calculation in Lemma 4.3, printed pp.33–34 and 39–40. For conjugation
by an involution b, the norm α(t)t is the actual product square (bt)².
-/

namespace Subgroup.QuaternionCentralProductData
open QuaternionInvolutionProducts

private theorem norm_product_map {G : Type*} [Group G] [Finite G]
    (d : QuaternionCentralProductData G)
    (eB : d.left ≃* QuaternionGroup 2) (eC : d.right ≃* QuaternionGroup 2) :
    ∃ f : Pair →* G, Function.Surjective f ∧
      (∀ x : Pair, f x=1 ↔ diagonalKernel x) ∧
      ∀ x : Pair, f x = (eB.symm x.1 : G)*(eC.symm x.2 : G) := by
  let B := d.left
  let C := d.right
  have hjoin := d.span
  have hinter := d.intersection_card
  have hcomm := d.commute
  let fB : Q8 →* G := B.subtype.comp eB.symm.toMonoidHom
  let fC : Q8 →* G := C.subtype.comp eC.symm.toMonoidHom
  let f : Pair →* G := fB.noncommCoprod fC (fun a b =>
    show Commute (fB a) (fC b) from hcomm _ (eB.symm a).property _ (eC.symm b).property)
  have hfB : fB.range = B := by
    dsimp [fB]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eB.symm.surjective,
      ← MonoidHom.range_eq_map, B.range_subtype]
  have hfC : fC.range = C := by
    dsimp [fC]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eC.symm.surjective,
      ← MonoidHom.range_eq_map, C.range_subtype]
  have hfrange : f.range = B ⊔ C := by
    dsimp [f]
    rw [MonoidHom.noncommCoprod_range, hfB, hfC]
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp (hfrange.trans hjoin)
  have hGcard : Nat.card G = 32 := d.card
  obtain ⟨w, hwne, _⟩ :=
    (Nat.card_eq_two_iff' (1 : (B ⊓ C : Subgroup G))).mp hinter
  have hw2 : (w : G) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := w)
    rw [hinter] at hh
    exact congrArg Subtype.val hh
  let wb : B := ⟨w, w.property.1⟩
  let wc : C := ⟨w, w.property.2⟩
  have hwb2 : wb ^ 2 = 1 := Subtype.ext hw2
  have hwc2 : wc ^ 2 = 1 := Subtype.ext hw2
  have hwbne : wb ≠ 1 := fun h => hwne (Subtype.ext
    (congrArg (fun b : B => (b : G)) h))
  have hwcne : wc ≠ 1 := fun h => hwne (Subtype.ext
    (congrArg (fun c : C => (c : G)) h))
  have heB : eB wb = QuaternionGroup.a 2 :=
    QuaternionGroup.eq_a_two_of_orderOf_eq_two _ (by
      rw [eB.orderOf_eq]
      exact orderOf_eq_prime hwb2 hwbne)
  have heC : eC wc = QuaternionGroup.a 2 :=
    QuaternionGroup.eq_a_two_of_orderOf_eq_two _ (by
      rw [eC.orderOf_eq]
      exact orderOf_eq_prime hwc2 hwcne)
  have hfb : fB (QuaternionGroup.a 2) = w := by
    change ((eB.symm (QuaternionGroup.a 2) : B) : G) = w
    rw [← heB, eB.symm_apply_apply]
  have hfc : fC (QuaternionGroup.a 2) = w := by
    change ((eC.symm (QuaternionGroup.a 2) : C) : G) = w
    rw [← heC, eC.symm_apply_apply]
  have hzz : f (centralInvolution,centralInvolution) = 1 := by
    change fB (QuaternionGroup.a 2) * fC (QuaternionGroup.a 2) = 1
    rw [hfb, hfc, ← pow_two, hw2]
  have hkerCard : Nat.card f.ker = 2 := by
    have hh := f.ker.card_mul_index
    rw [Subgroup.index_ker, hfrange, hjoin, Nat.card_congr Subgroup.topEquiv.toEquiv, hGcard,
      show Nat.card Pair = 64 by rw [Nat.card_eq_fintype_card]; decide] at hh
    omega
  have hker : ∀ p : Pair, f p = 1 ↔ diagonalKernel p := by
    obtain ⟨k, hk, huniq⟩ := (Nat.card_eq_two_iff' (1 : f.ker)).mp hkerCard
    have hzker : (⟨(centralInvolution,centralInvolution), hzz⟩ : f.ker) ≠ 1 := by
      intro he
      exact (by decide : (centralInvolution,centralInvolution) ≠ 1) (congrArg Subtype.val he)
    have hkz := huniq ⟨(centralInvolution,centralInvolution), hzz⟩ hzker
    intro p
    constructor
    · intro hp
      by_cases hp1 : p = 1
      · exact Or.inl hp1
      · right
        have hpk : (⟨p, hp⟩ : f.ker) ≠ 1 := fun h => hp1 (congrArg Subtype.val h)
        exact congrArg Subtype.val ((huniq ⟨p,hp⟩ hpk).trans hkz.symm)
    · rintro (rfl | rfl)
      · exact map_one f
      · exact hzz

  exact ⟨f,hf,hker,fun _ => rfl⟩

private theorem norm_factor_action {G : Type*} [Group G]
    (B : Subgroup G) (model : B ≃* QuaternionGroup 2)
    (α : MulAut G) (hα : α^2=1) (hm : B.map α.toMonoidHom=B)
    (ho : ¬ ∃ b : B, ∀ x : B, α (x:G)=(b:G)*x*(b:G)⁻¹) :
    ∃ a : MulAut Q8, a^2=1 ∧
      (¬ ∃ b : Q8, ∀ x : Q8, a x=b*x*b⁻¹) ∧
      ∀ x : Q8, (model.symm (a x) : G)=α (model.symm x : G) := by
  let e : MulAut B := (B.equivMapOfInjective α.toMonoidHom α.injective).trans
    (MulEquiv.subgroupCongr hm)
  have he2 : e^2=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change α (α (x:G))=(x:G)
    simpa [pow_two] using DFunLike.congr_fun hα (x:G)
  let a : MulAut Q8 := MulAut.congr model e
  have ha (x : Q8) : (model.symm (a x) : G)=α (model.symm x : G) := by
    simp only [a, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  refine ⟨a, ?_, ?_, ha⟩
  · dsimp [a]
    rw [← map_pow, he2, map_one]
  · rintro ⟨b,hb⟩
    apply ho
    refine ⟨model.symm b, fun x => ?_⟩
    have hh := congrArg (fun y : Q8 => (model.symm y : G)) (hb (model x))
    rw [ha, model.symm_apply_apply] at hh
    simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply,
      Subgroup.coe_mul, Subgroup.coe_inv] using hh

/-- The two norm conclusions for an involution outer on both quaternion factors. -/
public theorem involution_products {G : Type*} [Group G] [Finite G]
    (d : QuaternionCentralProductData G) (α : MulAut G) (hα : α^2=1)
    (ho : d.BothOuter α) :
    (∀ x : G, x^2=1 → α x*x ∈ Subgroup.center G → α x*x=1) ∧
    Nat.card {x : G // x^2=1 ∧ (α x*x)^2≠1}=8 := by
  obtain ⟨eB⟩ := d.left_model
  obtain ⟨eC⟩ := d.right_model
  obtain ⟨f,hf,hk,hval⟩ := norm_product_map d eB eC
  obtain ⟨a,ha,hao,hav⟩ := norm_factor_action d.left eB α hα ho.left_map ho.left_outer
  obtain ⟨b,hb,hbo,hbv⟩ := norm_factor_action d.right eC α hα ho.right_map ho.right_outer
  have he (x : Pair) : f (a x.1,b x.2)=α (f x) := by
    rw [hval,hval,map_mul]
    exact congrArg₂ (·*·) (hav x.1) (hbv x.2)
  obtain ⟨hc,hn⟩ := norms_of_diagonal_kernel f hf hk a b ha hb hao hbo α he
  exact ⟨fun x _ => hc x, hn⟩

end Subgroup.QuaternionCentralProductData
