module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod

/-!
# An order-four operator fixing a binary line

On a binary four-space, suppose an order-four operator has square with no
rank-one displacement. The squared displacement has rank two. If the original
kernel also had dimension two, stabilization of kernels would contradict
nilpotence of the fourth power. Its fixed space therefore has dimension one.

This supplies the C₄ fixed-line calculation for the genuine natural SL₂(4)
section in Aschbacher–Smith J.4.5, without a permutation-module substitute.
-/

public section
namespace LinearMap
open Module
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem order_four_fixed_line (hd : finrank (ZMod 2) V=4)
    (x : Module.End (ZMod 2) V) (h4 : x^4=1) (h2 : x^2≠1)
    (hrank : finrank (ZMod 2) (x^2-1).range≠1) :
    finrank (ZMod 2) (x-1).ker=1 := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0<finrank (ZMod 2) V)
  let : CharP (Module.End (ZMod 2) V) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (Module.End (ZMod 2) V)).injective 2
  let N := x-1
  have hN2 : N^2=x^2-1 := by
    simpa only [one_pow] using sub_pow_char_of_commute 2 (Commute.one_right x)
  have hN4 : N^4=0 := by
    have hh := sub_pow_char_pow_of_commute 2 2 (Commute.one_right x)
    simpa only [show 2^2=4 by decide,one_pow,h4,sub_self] using hh
  have hq : (N^2)^2=0 := by rw [←pow_mul]; exact hN4
  have hinc : (N^2).range≤(N^2).ker := by
    rintro v ⟨w,rfl⟩
    exact LinearMap.congr_fun hq w
  have hdim := (N^2).finrank_range_add_finrank_ker
  rw [hd] at hdim
  have hr0 : finrank (ZMod 2) (N^2).range≠0 := by
    intro hz
    have he := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
    rw [hN2] at he
    exact h2 (sub_eq_zero.mp he)
  have hr1 : finrank (ZMod 2) (N^2).range≠1 := by rwa [hN2]
  have hbound := Submodule.finrank_mono hinc
  have hk2 : finrank (ZMod 2) (N^2).ker=2 := by omega
  have hker : N.ker≤(N^2).ker := by
    intro v hv
    change N (N v)=0
    change N v=0 at hv
    rw [hv,map_zero]
  have hkd := Submodule.finrank_mono hker
  have hpos : 0<finrank (ZMod 2) N.ker := by
    by_contra hn
    have hz : N.ker=⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hstable : LinearMap.ker (N^0)=LinearMap.ker (N^1) := by simpa only [pow_zero,pow_one,Module.End.one_eq_id,LinearMap.ker_id] using hz.symm
    have he := Module.End.ker_pow_constant hstable 4
    have hbad : (⊥ : Submodule (ZMod 2) V)=⊤ := by simpa only [pow_zero,zero_add,hN4,LinearMap.ker_zero,Module.End.one_eq_id,LinearMap.ker_id] using he
    exact bot_ne_top hbad
  have hlt : finrank (ZMod 2) N.ker<2 := by
    by_contra hn
    have he : N.ker=(N^2).ker := Submodule.eq_of_le_of_finrank_eq hker (by omega)
    have hstable : LinearMap.ker (N^1)=LinearMap.ker (N^2) := by simpa only [pow_one] using he
    have htop : N.ker=⊤ := by simpa [hN4] using Module.End.ker_pow_constant hstable 3
    have hdimN : finrank (ZMod 2) N.ker=4 := by rw [htop,finrank_top,hd]
    omega
  change finrank (ZMod 2) N.ker=1
  omega

end LinearMap
