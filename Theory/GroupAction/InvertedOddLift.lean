module
public import Theory.GroupAction.InvertedPrimeLift
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Odd-order inversion lifts through a pointwise fixed kernel

For an equivariant surjection, an involution fixing the kernel lifts an
inverted element of any odd order to an inverted element of exactly that
order. For a lift w, the displacement a(w)w⁻¹ is inverted; its m-th power
is fixed and inverted. Squaring therefore kills the possible involutory
part. The image is the inverse fourth power of the prescribed element,
so oddness preserves its exact order. No centrality or splitting is needed.

This extends the prime-order argument in `InvertedPrimeLift` for the
full split torus used in Aschbacher--Smith 12.6.26, printed p.832.
-/

public section
open Subgroup
namespace MulAut
variable {G H : Type*} [Group G] [Group H]

/-- Lift an inverted odd-order element with the same order and prescribed inverter. -/
theorem exists_inverted_odd_of_fixed_kernel
    (a : MulAut G) (b : MulAut H) (f : G →* H)
    (hf : Function.Surjective f) (heq : ∀ x, f (a x) = b (f x))
    (ha : a ^ 2 = 1) (hker : ∀ x ∈ f.ker, a x = x)
    {p : ℕ} (ho : Odd p)
    (y : H) (hy : orderOf y = p) (hi : b y = y⁻¹) :
    ∃ x : G, orderOf x = p ∧ a x = x⁻¹ := by
  obtain ⟨w,rfl⟩ := hf y
  let d := a w * w⁻¹
  have haa : a (a w) = w := by
    have h := congrArg (fun c : MulAut G => c w) ha
    simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using h
  have hd : a d = d⁻¹ := by
    dsimp [d]
    rw [map_mul,map_inv,haa,mul_inv_rev,inv_inv]
  have hfd : f d = (f w)⁻¹ ^ 2 := by
    dsimp [d]
    rw [map_mul,map_inv,heq,hi,pow_two]
  have hdp : d ^ p ∈ f.ker := by
    change f (d ^ p) = 1
    rw [map_pow,hfd,←pow_mul,Nat.mul_comm 2 p,pow_mul,inv_pow,
      show (f w)^p=1 from hy ▸ pow_orderOf_eq_one _,inv_one,one_pow]
  have hpow : (d ^ p) ^ 2 = 1 := by
    have h := hker _ hdp
    rw [map_pow,hd,inv_pow] at h
    calc
      (d ^ p) ^ 2 = (d ^ p)⁻¹ * d ^ p := by rw [pow_two,h]
      _ = 1 := inv_mul_cancel _
  refine ⟨d ^ 2,?_,by rw [map_pow,hd,inv_pow]⟩
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one (by
      simpa only [←pow_mul,Nat.mul_comm 2 p] using hpow)
  · have hf4 : orderOf (f (d ^ 2)) = p := by
      rw [map_pow,hfd,←pow_mul]
      have hc : (orderOf ((f w)⁻¹)).Coprime (2 * 2) := by
        rw [orderOf_inv,hy]
        exact ho.coprime_two_right.mul_right ho.coprime_two_right
      rw [hc.orderOf_pow,orderOf_inv,hy]
    rw [←hf4]
    exact orderOf_map_dvd f (d ^ 2)
end MulAut
