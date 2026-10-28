module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Mathlib.Data.Nat.GCD.Basic
public import Theory.NumberTheory.BinaryMinusPrimeRestriction

/-!
# Field degrees of binary rank-one sections in PSL₃ parabolics

A perfect subgroup of a parabolic lies in its affine solvable residual.
The odd part of its section order divides the SL₂ quotient order: the
parabolic two-core contributes only powers of two. Divisibility of the
Mersenne factors then forces the original binary degree to divide the
coefficient-field degree. This uses the actual parabolic embedding and
requires no assumption that its rank-one section is the whole Levi factor.

Source: Aschbacher--Smith 4.3.16, printed p.618; F.1.12(I)(1), pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.PerfectSubgroups
universe u

private theorem degree_dvd_of_local_order
    {F : Type u} [Field F] [Finite F] [CharP F 2]
    {C : Type u} [Group C] [Finite C]
    (e : (C ⧸ pCore 2 C) ≃* SL(2,F)) {f n : ℕ}
    (hF : Nat.card F=2^f) (hn : 0<n)
    (hd : (2^n)^2-1 ∣ Nat.card C) : n ∣ f := by
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p:=2) (G:=C)).exists_card_eq
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 C),
    Nat.card_congr e.toEquiv,Atlas.card_sl_two,hF,hk] at hd
  have ho : Odd ((2^n)^2-1) := by
    simpa only [←pow_mul] using
      Nat.BinarySignedTorus.odd_of_dvd_sub (by omega : 0<n*2)
        (dvd_refl (2^(n*2)-1))
  have hc := ho.coprime_two_right
  have hd' : (2^n)^2-1 ∣ (2^f)^2-1 :=
    (hc.pow_right f).dvd_of_dvd_mul_left ((hc.pow_right k).dvd_of_dvd_mul_right hd)
  have hh : 2^(2*n)-1 ∣ 2^(2*f)-1 := by
    simpa only [←pow_mul,Nat.mul_comm] using hd'
  have hz := Nat.mod_eq_zero_of_dvd hh
  rw [Nat.pow_sub_one_mod_pow_sub_one] at hz
  have he : (2*f)%(2*n)=0 := by
    by_contra he
    have hpow := Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
      (by omega : 1≤(2*f)%(2*n))
    norm_num at hpow
    omega
  exact (Nat.mul_dvd_mul_iff_left (by decide : 0<2)).mp (Nat.dvd_of_mod_eq_zero he)

/-- The field degree of a binary rank-one section divides the coefficient
field degree of either parabolic containing its perfect preimage. -/
theorem degree_dvd_of_perfect_parabolic
    {F : Type u} [Field F] [Finite F] [CharP F 2]
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    {f n : ℕ} (hF : Nat.card F=2^f) (hf : 2≤f) (hn : 0<n)
    (hd : (2^n)^2-1 ∣ Nat.card B)
    (j : B →* PSL(3,F)) (hj : Function.Injective j)
    (hl : j.range ≤ pointParabolic F ∨ j.range ≤ lineParabolic F) : n ∣ f := by
  have hcard : 4≤Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hf
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  rcases hl with hl | hl
  · have hl' : j.range ≤ pointLocal F := by
      rw [←pointParabolic_residual F hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ hl
    let k := j.codRestrict _ (fun b => hl' ⟨b,rfl⟩)
    exact degree_dvd_of_local_order (pointLocalCoreQuotientEquiv F) hF hn
      (hd.trans (card_dvd_of_injective k (fun x y he => hj (congrArg Subtype.val he))))
  · have hl' : j.range ≤ lineLocal F := by
      rw [←lineParabolic_residual F hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ hl
    let k := j.codRestrict _ (fun b => hl' ⟨b,rfl⟩)
    exact degree_dvd_of_local_order (lineLocalCoreQuotientEquiv F) hF hn
      (hd.trans (card_dvd_of_injective k (fun x y he => hj (congrArg Subtype.val he))))
end Matrix.PSL3.LinearThree.PerfectSubgroups
