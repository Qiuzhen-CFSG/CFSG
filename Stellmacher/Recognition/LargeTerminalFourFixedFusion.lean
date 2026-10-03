module

public import Stellmacher.Recognition.LargeTerminalFiveFixedInvolution
public import Stellmacher.Recognition.LargeTerminalDerivedInvolutionClasses
public import Stellmacher.Recognition.LargeTerminalFourFixedDerivedFusion

/-!
# Assembling the four-fixed fusion alternative

The noncyclic fixed subgroup supplies an involution outside the first
residual. Two geometric inputs suffice for the desired alternative: that
involution fuses into the residual's derived subgroup, and involutions there
either fuse to the omega-central involution or have centralizer order
divisible by three. Centralizer orders are preserved by conjugation, and
the original five-subgroup supplies the factor five.

This module first isolates the assembly with those geometric inputs explicit,
then applies their proved forms to obtain the alternative from the large
terminal context. The retained context suffices without further ambient
simplicity or N-group hypotheses.

Source: Thompson VI, printed pp.629--630, the coset census and ensuing fusion
argument. No ambient Sylow-five status is used in this assembly.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven Subgroup

universe u

private theorem centralizer_card_eq_of_isConj
    {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set G)) =
      Nat.card (centralizer ({y} : Set G)) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  let f : centralizer ({x} : Set G) ≃ centralizer ({e x} : Set G) := {
    toFun a := ⟨e a, by
      rw [mem_centralizer_singleton_iff]
      simpa only [map_mul] using
        congrArg e (mem_centralizer_singleton_iff.mp a.property)⟩
    invFun a := ⟨e.symm a, by
      rw [mem_centralizer_singleton_iff]
      apply e.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using
        mem_centralizer_singleton_iff.mp a.property⟩
    left_inv a := Subtype.ext (e.symm_apply_apply a)
    right_inv a := Subtype.ext (e.apply_symm_apply a) }
  exact Nat.card_congr f

/-- The original five-subgroup supplies the factor five, independently of
whether it is an ambient Sylow subgroup. -/
private theorem fifteen_dvd_centralizer_of_three_dvd
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (hA : Nat.card A = 5)
    (y : G) (hy : y ∈ centralizer (A : Set G))
    (hthree : 3 ∣ Nat.card (centralizer ({y} : Set G))) :
    15 ∣ Nat.card (centralizer ({y} : Set G)) := by
  have hAC : A ≤ centralizer ({y} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hy a ha)
  have hfive : 5 ∣ Nat.card (centralizer ({y} : Set G)) :=
    hA ▸ card_dvd_of_le hAC
  exact (show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd hthree hfive

/-- Reduction to the geometric fusion of five-fixed involutions into the
derived residual and the involution alternatives in that derived subgroup. -/
public theorem LargeTerminalContext.exists_five_fixed_fusion_of_derived_fusion
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (z : G)
    (hfusion : ∀ y : G, y ∈ twoCoreIn ctx.second →
      y ∈ centralizer (A : Set G) → y ∉ ctx.firstResidual → orderOf y = 2 →
      ∃ t : G, t ∈ DerivedAmbient ctx.firstResidual ∧ IsConj y t)
    (hderived : ∀ t : G, t ∈ DerivedAmbient ctx.firstResidual → orderOf t = 2 →
      IsConj z t ∨ 3 ∣ Nat.card (centralizer ({t} : Set G))) :
    ∃ y : G, y ∈ twoCoreIn ctx.second ∧ y ∈ centralizer (A : Set G) ∧
      y ∉ ctx.firstResidual ∧ orderOf y = 2 ∧
      (IsConj z y ∨ 15 ∣ Nat.card (centralizer ({y} : Set G))) := by
  obtain ⟨y, hyQ, hyA, hyR, hy⟩ :=
    ctx.exists_five_fixed_involution_of_not_cyclic A hcard hfixed hncyc
  obtain ⟨t, htD, hyt⟩ := hfusion y hyQ hyA hyR hy
  have ht : orderOf t = 2 := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hyt
    exact ((MulAut.conj g).orderOf_eq y).trans hy
  refine ⟨y, hyQ, hyA, hyR, hy, ?_⟩
  rcases hderived t htD ht with hzt | hthree
  · exact Or.inl (hzt.trans hyt.symm)
  · apply Or.inr
    apply fifteen_dvd_centralizer_of_three_dvd A hA y hyA
    rwa [centralizer_card_eq_of_isConj hyt]

/-- If the actual five-fixed subgroup of the second core is noncyclic, it
contains an involution outside the first residual which either fuses to the
omega-central involution or has ambient centralizer order divisible by fifteen.
The retained large terminal context supplies both geometric fusion inputs;
neither ambient Sylow-five status nor additional ambient group hypotheses
are needed. -/
public theorem LargeTerminalContext.exists_five_fixed_fusion_of_not_cyclic
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ y : G, y ∈ twoCoreIn ctx.second ∧ y ∈ centralizer (A : Set G) ∧
      y ∉ ctx.firstResidual ∧ orderOf y = 2 ∧
      (IsConj z y ∨ 15 ∣ Nat.card (centralizer ({y} : Set G))) :=
  ctx.exists_five_fixed_fusion_of_derived_fusion A hA hcard hfixed hncyc z
    (ctx.five_fixed_derived_fusion hS A hA hAN hcard hfixed hncyc)
    (ctx.derived_involution_alternative z hz hgen)

end Stellmacher.Recognition
