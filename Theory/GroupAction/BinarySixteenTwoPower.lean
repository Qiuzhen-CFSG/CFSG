module
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Two-power automorphisms of binary sixteen

An automorphism of an elementary abelian group of order sixteen whose order
is a power of two has fourth power one. On the associated four-dimensional
binary vector space, its displacement is nilpotent. Stabilization of kernels
bounds its nilpotence index by four.

This is the small linear-algebra step used in Parrott (1972), pp.674–676,
for the action on the intersection of the two elementary subgroups.
-/

open scoped IsMulCommutative
namespace MulAut

/-- A binary automorphism on sixteen elements with two-power order has fourth power one. -/
public theorem fourth_power_eq_one_of_card_sixteen_of_two_power
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (a : MulAut V) (n : ℕ) (ha : a ^ (2 ^ n) = 1) :
    a ^ 4 = 1 := by
  have hdim : Module.finrank (ZMod 2) (Additive V) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    change Nat.card V = _ at hc
    simpa only [Nat.card_zmod, hV] using hc.symm
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : CharP (Module.End (ZMod 2) (Additive V)) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) _).injective 2
  let f : Module.End (ZMod 2) (Additive V) :=
    a.toAdditive.toAddMonoidHom.toZModLinearMap 2
  have hpow (k : ℕ) (v : Additive V) : (f ^ k) v = (a ^ k) v.toMul := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ']
      change f ((f ^ k) v) = a ((a ^ k) v.toMul)
      rw [ih]
      rfl
  have hf : f ^ (2 ^ n) = 1 := by
    ext v
    rw [hpow, ha]
    rfl
  have hn : (f - 1) ^ (2 ^ n) = 0 := by
    rw [sub_pow_char_pow_of_commute 2 n (Commute.one_right f), hf, one_pow, sub_self]
  have hfour : (f - 1) ^ 4 = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    have hh := Module.End.ker_pow_le_ker_pow_finrank (f - 1) (2 ^ n)
    rwa [hn, hdim, LinearMap.ker_zero] at hh
  have hf4 : f ^ 4 = 1 := by
    have hh := sub_pow_char_pow_of_commute (R := Module.End (ZMod 2) (Additive V))
      2 2 (Commute.one_right f)
    norm_num only [show (2 : ℕ) ^ 2 = 4 by decide, one_pow] at hh
    rw [hfour] at hh
    exact sub_eq_zero.mp hh.symm
  ext v
  have hh := congrArg (fun u : Module.End (ZMod 2) (Additive V) => u (Additive.ofMul v)) hf4
  rw [hpow] at hh
  exact hh
end MulAut
