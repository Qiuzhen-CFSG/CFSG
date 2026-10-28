module

public import Theory.Mathieu.M12.ValueBoundParabolics.CentralCovers.LocalAction
public import Mathlib.GroupTheory.Commutator.Basic
import all Theory.Mathieu.M12.Properties.Sylow3

/-!
# Central extensions of the M₁₂ Sylow three-subgroup

Lift the two marked generators of the order-27 Heisenberg group. An automorphism
inducing simultaneous inversion modulo a central three-kernel fixes their
commutator modulo that kernel. The triple commutators are therefore both fixed
and inverted; as three-elements, they vanish. The lifted commutator is central,
has order three, and generates the derived subgroup. Its image still has order
three, so the central kernel meets the derived subgroup trivially.

This local calculation supplies the three-primary multiplier exclusion in
Aschbacher–Smith E.4.3(1), printed pp.241–242 (PDF pp.252–253), using the marked
normalizer action constructed in `CentralCovers.LocalAction`. The internal
import is used only for the coordinate calculations in the marked model.
The tabulated
multiplier in GLS3 §6.1 is not a hypothesis.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.CentralCovers

private abbrev X : M12Heisenberg := ⟨1, 0, 0⟩
private abbrev Y : M12Heisenberg := ⟨0, 1, 0⟩

private theorem heisenberg_normal_form (a : M12Heisenberg) :
    X ^ a.i.val * Y ^ a.j.val * ⁅X,Y⁆ ^ a.k.val = a := by
  rcases a with ⟨i,j,k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

private theorem eq_top_of_heisenberg_lifts
    {H : Type*} [Group H] (f : H →* M12Heisenberg) (x y : H)
    (hx : f x = X) (hy : f y = Y)
    (D : Subgroup H) (hk : f.ker ≤ D) (hxd : x ∈ D) (hyd : y ∈ D) : D = ⊤ := by
  apply top_unique
  intro a _
  let b := x ^ (f a).i.val * y ^ (f a).j.val * ⁅x,y⁆ ^ (f a).k.val
  have hb : b ∈ D := D.mul_mem
    (D.mul_mem (D.pow_mem hxd _) (D.pow_mem hyd _))
    (D.pow_mem (D.mul_mem (D.mul_mem (D.mul_mem hxd hyd) (D.inv_mem hxd))
      (D.inv_mem hyd)) _)
  have hfb : f b = f a := by
    simp only [b, map_mul, map_pow, map_commutatorElement, hx, hy]
    exact heisenberg_normal_form (f a)
  have hab : a * b⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfb, mul_inv_cancel]
  simpa only [inv_mul_cancel_right] using D.mul_mem (hk hab) hb

private theorem commutator_eq_of_central_kernel
    {H B : Type*} [Group H] [Group B] (f : H →* B)
    (hk : f.ker ≤ center H) {a b c d : H}
    (hab : f a = f b) (hcd : f c = f d) : ⁅a,c⁆ = ⁅b,d⁆ := by
  have left {u v w : H} (huv : f u = f v) : ⁅u,w⁆ = ⁅v,w⁆ := by
    have hz : u * v⁻¹ ∈ center H := hk (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, huv, mul_inv_cancel])
    have hzcomm := (mem_center_iff.mp hz w).symm
    have hzero : ⁅u * v⁻¹,w⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr hzcomm
    calc
      ⁅u,w⁆ = ⁅(u * v⁻¹) * v,w⁆ := by simp
      _ = (u * v⁻¹) * ⁅v,w⁆ * (u * v⁻¹)⁻¹ * ⁅u * v⁻¹,w⁆ :=
        commutatorElement_mul_left_eq_conj_mul _ _ _
      _ = ⁅v,w⁆ := by
        rw [hzero, mul_one, ← mem_center_iff.mp hz ⁅v,w⁆, mul_inv_cancel_right]
  rw [left hab]
  have hr := left (w := b) hcd
  simpa only [commutatorElement_inv] using congrArg Inv.inv hr

private theorem commute_of_fixed_inverted_images
    {H B : Type*} [Group H] [Group B]
    (f : H →* B) (hk : f.ker ≤ center H) (hp : IsPGroup 3 f.ker)
    (α : MulAut H) (hfix : ∀ z ∈ f.ker, α z = z)
    (c x : H) (hc : f (α c) = f c) (hx : f (α x) = f x⁻¹)
    (hcx : ⁅c,x⁆ ∈ f.ker) : Commute c x := by
  have hzc : ⁅c,x⁆ ∈ center H := hk hcx
  have hinv : ⁅c,x⁆ = ⁅c,x⁆⁻¹ := by
    calc
      ⁅c,x⁆ = α ⁅c,x⁆ := (hfix _ hcx).symm
      _ = ⁅α c,α x⁆ := map_commutatorElement α c x
      _ = ⁅c,x⁻¹⁆ := commutator_eq_of_central_kernel f hk hc hx
      _ = ⁅c,x⁆⁻¹ := by
        rw [commutatorElement_inv_right, ← commutatorElement_inv]
        rw [mem_center_iff.mp ((center H).inv_mem hzc) x⁻¹]
        simp
  have hs : (⟨⁅c,x⁆,hcx⟩ : f.ker) ^ 2 = 1 := by
    apply Subtype.ext
    change ⁅c,x⁆ ^ 2 = 1
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp hinv
  have ho : (⟨⁅c,x⁆,hcx⟩ : f.ker) = 1 := by
    apply (hp.powEquiv' (by decide : ¬ 3 ∣ 2)).injective
    simpa only [IsPGroup.powEquiv_apply, one_pow] using hs
  exact commutatorElement_eq_one_iff_commute.mp (congrArg Subtype.val ho)

private theorem lift_commutator_central
    {H : Type*} [Group H] (f : H →* M12Heisenberg)
    (hk : f.ker ≤ center H) (hp : IsPGroup 3 f.ker)
    (α : MulAut H) (hfix : ∀ z ∈ f.ker, α z = z)
    (ha : ∀ x, f (α x) = heisenbergInversion (f x))
    (x y : H) (hx : f x = X) (hy : f y = Y) : ⁅x,y⁆ ∈ center H := by
  have hc : f (α ⁅x,y⁆) = f ⁅x,y⁆ := by
    rw [ha, map_commutatorElement, hx, hy]
    decide +kernel
  have comm (z : H) (hz : f z = X ∨ f z = Y) : Commute ⁅x,y⁆ z := by
    apply commute_of_fixed_inverted_images f hk hp α hfix _ _ hc
    · rw [ha, map_inv]
      rcases hz with hz | hz <;> rw [hz] <;> decide +kernel
    · rw [MonoidHom.mem_ker, map_commutatorElement, map_commutatorElement, hx, hy]
      rcases hz with hz | hz <;> rw [hz] <;> decide +kernel
  have ht : centralizer ({⁅x,y⁆} : Set H) = ⊤ := by
    apply eq_top_of_heisenberg_lifts f x y hx hy
    · intro z hz
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hk hz) ⁅x,y⁆).symm
    · exact mem_centralizer_singleton_iff.mpr (comm x (Or.inl hx)).symm.eq
    · exact mem_centralizer_singleton_iff.mpr (comm y (Or.inr hy)).symm.eq
  apply mem_center_iff.mpr
  intro z
  exact mem_centralizer_singleton_iff.mp (ht ▸ mem_top z)

private theorem commutator_pow_of_central
    {H : Type*} [Group H] (x y : H) (hc : ⁅x,y⁆ ∈ center H) (n : ℕ) :
    ⁅x ^ n,y⁆ = ⁅x,y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, commutatorElement_mul_left_eq_conj_mul, ih,
      mem_center_iff.mp hc (x ^ n), mul_inv_cancel_right, ← pow_succ']

private theorem derived_le_lift_commutator
    {H : Type*} [Group H] (f : H →* M12Heisenberg)
    (hk : f.ker ≤ center H) (x y : H) (hx : f x = X) (hy : f y = Y)
    (hc : ⁅x,y⁆ ∈ center H) : commutator H ≤ zpowers ⁅x,y⁆ := by
  let C := zpowers ⁅x,y⁆
  have hC : C ≤ center H := zpowers_le.mpr hc
  let : C.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hC hn) g, mul_inv_cancel_right]
    exact hn⟩
  let q : H →* H ⧸ C := QuotientGroup.mk' C
  have hqcomm : Commute (q x) (q y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (mem_zpowers _)
  have hqker (k : H) (h : k ∈ f.ker) : q k ∈ center (H ⧸ C) := by
    rw [mem_center_iff]
    intro z
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective C z
    simpa only [map_mul] using congrArg q (mem_center_iff.mp (hk h) w)
  have hqcentral (a : H) (hax : Commute (q a) (q x))
      (hay : Commute (q a) (q y)) : q a ∈ center (H ⧸ C) := by
    have ht : (centralizer ({q a} : Set (H ⧸ C))).comap q = ⊤ := by
      apply eq_top_of_heisenberg_lifts f x y hx hy
      · intro k h
        exact mem_centralizer_singleton_iff.mpr
          (mem_center_iff.mp (hqker k h) (q a)).symm
      · exact mem_centralizer_singleton_iff.mpr hax.symm.eq
      · exact mem_centralizer_singleton_iff.mpr hay.symm.eq
    rw [mem_center_iff]
    intro z
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective C z
    exact mem_centralizer_singleton_iff.mp (show w ∈
      (centralizer ({q a} : Set (H ⧸ C))).comap q from ht ▸ mem_top w)
  have ht : (center (H ⧸ C)).comap q = ⊤ :=
    eq_top_of_heisenberg_lifts f x y hx hy _ hqker
      (hqcentral x (Commute.refl _) hqcomm)
      (hqcentral y hqcomm.symm (Commute.refl _))
  have hab : IsMulCommutative (H ⧸ C) := by
    apply center_eq_top_iff.mp
    apply top_unique
    intro z _
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective C z
    exact (show w ∈ (center (H ⧸ C)).comap q from ht ▸ mem_top w)
  exact Normal.quotient_commutative_iff_commutator_le.mp hab

/-- A central three-kernel compatible with the marked inversion misses the derived subgroup. -/
theorem kernel_inf_commutator_eq_bot
    {H : Type*} [Group H] [Finite H] (f : H →* M12Heisenberg)
    (hf : Function.Surjective f) (hk : f.ker ≤ center H) (hp : IsPGroup 3 f.ker)
    (α : MulAut H) (hfix : ∀ z ∈ f.ker, α z = z)
    (ha : ∀ x, f (α x) = heisenbergInversion (f x)) :
    f.ker ⊓ commutator H = ⊥ := by
  obtain ⟨x,hx⟩ := hf X
  obtain ⟨y,hy⟩ := hf Y
  have hc := lift_commutator_central f hk hp α hfix ha x y hx hy
  have hd := derived_le_lift_commutator f hk x y hx hy hc
  have hx3 : x ^ 3 ∈ center H := hk (by
    rw [MonoidHom.mem_ker, map_pow, hx]
    exact m12Heisenberg_cube_eq_one X)
  have hc3 : ⁅x,y⁆ ^ 3 = 1 := by
    rw [← commutator_pow_of_central x y hc]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hx3 y).symm
  have horder : orderOf (f ⁅x,y⁆) = 3 := by
    rw [map_commutatorElement, hx, hy]
    apply m12Heisenberg_orderOf_eq_three
    decide +kernel
  apply le_bot_iff.mp
  intro z hz
  obtain ⟨n,hn⟩ := mem_zpowers_iff.mp (hd hz.2)
  have hfn : f ⁅x,y⁆ ^ n = 1 := by
    rw [← map_zpow, hn]
    exact hz.1
  have hn3 : (3 : ℤ) ∣ n := by
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr hfn
    rw [horder] at hd
    simpa only [Nat.cast_ofNat] using hd
  apply mem_bot.mpr
  rw [← hn]
  apply orderOf_dvd_iff_zpow_eq_one.mp
  exact (Int.natCast_dvd_natCast.mpr (orderOf_dvd_of_pow_eq_one hc3)).trans hn3

end Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.CentralCovers
