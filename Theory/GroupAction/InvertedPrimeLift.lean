module
public import Theory.GroupAction.PerfectCentralQuotient
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Prime-order inversion lifts through a pointwise fixed kernel

For an equivariant surjection, an involution fixing the kernel lifts any
inverted odd-prime element to an inverted element of that same order.
For a lift w, the displacement a(w)w⁻¹ is inverted. Its p-th power is both
fixed and inverted, so squaring the displacement kills its possible
involutory part. Its image remains nontrivial because p is odd.

No splitting or centrality of the kernel is required. The application is
the original component action in Aschbacher--Smith 12.6.26, printed p.832.
-/

public section
open Subgroup
namespace MulAut
variable {G H : Type*} [Group G] [Group H]

/-- Lift an inverted odd-prime element without changing the prescribed inverter. -/
theorem exists_inverted_prime_of_fixed_kernel
    (a : MulAut G) (b : MulAut H) (f : G →* H)
    (hf : Function.Surjective f) (heq : ∀ x, f (a x) = b (f x))
    (ha : a ^ 2 = 1) (hker : ∀ x ∈ f.ker, a x = x)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (y : H) (hy : orderOf y = p) (hi : b y = y⁻¹) :
    ∃ x : G, orderOf x = p ∧ a x = x⁻¹ := by
  let : Fact p.Prime := ⟨hp⟩
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
  refine ⟨d ^ 2,orderOf_eq_prime ?_ ?_,?_⟩
  · simpa only [←pow_mul,Nat.mul_comm 2 p] using hpow
  · intro hx
    have hh := congrArg f hx
    rw [map_pow,hfd,←pow_mul,inv_pow,map_one] at hh
    have h4 : (f w) ^ 4 = 1 := inv_eq_one.mp hh
    have hdvd : p ∣ 4 := hy ▸ orderOf_dvd_of_pow_eq_one h4
    have hp2 : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hdvd))).resolve_left hp.ne_one
    have hodd := Nat.odd_iff.mp ho
    omega
  · rw [map_pow,hd,inv_pow]
end MulAut
