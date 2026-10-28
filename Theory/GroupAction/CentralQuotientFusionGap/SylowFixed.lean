module

public import Theory.GroupAction.CentralQuotientFusionGap
public import Mathlib.GroupTheory.Sylow

/-!
# Fixed points detected modulo the center

An involutory automorphism fixing the center and a Sylow two-subgroup
pointwise has no nontrivial central displacement. On the inverse image of
the fixed subgroup in the central quotient, displacement is a homomorphism
of exponent two. Its kernel contains a Sylow two-subgroup, so its image
is trivial by the Sylow image theorem.

This argument retains arbitrary central extensions. It supplies the lifting
step for the actual inner omega-center actions in Aschbacher–Smith, E.6.7
and E.6.23 (combined manuscript, 1 March 2004, printed pp.246 and 254).
-/

public section

namespace MulAut.CentralQuotientFusionGap
open Subgroup

/-- Fixedness modulo the center lifts when an involutory automorphism fixes
the center and a Sylow two-subgroup pointwise. -/
theorem eq_of_central_displacement_of_fixed_sylow
    {D : Type*} [Group D] [Finite D] (a : MulAut D) (S : Sylow 2 D)
    (ha : a ^ 2 = 1) (hZ : center D ≤ a.fixedSubgroup)
    (hS : (S : Subgroup D) ≤ a.fixedSubgroup)
    (x : D) (hx : a x * x⁻¹ ∈ center D) : a x = x := by
  let F := fixedPreimage (center D) a
  let f := displacement (center D) a le_rfl
  have hSF : (S : Subgroup D) ≤ F := by
    intro s hs
    apply (mem_fixedPreimage (center D) a s).mpr
    rw [(MulAut.mem_fixedSubgroup a s).mp (hS hs), mul_inv_cancel]
    exact one_mem _
  have hi (y : D) : a (a y) = y := by
    have hh := DFunLike.congr_fun ha y
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have hp : IsPGroup 2 f.range := isPGroup_iff_pow_pow_eq_one.mpr (by
    rintro ⟨_, y, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (a y * (y : D)⁻¹) ^ (2 ^ 1) = 1
    have hfy : a (a y * (y : D)⁻¹) = a y * (y : D)⁻¹ :=
      (MulAut.mem_fixedSubgroup a _).mp (hZ ((mem_fixedPreimage (center D) a y).mp y.property))
    rw [map_mul, map_inv, hi] at hfy
    have he : (a y * (y : D)⁻¹)⁻¹ = a y * (y : D)⁻¹ := by
      simpa only [mul_inv_rev, inv_inv] using hfy
    rw [pow_one, pow_two]
    exact (congrArg (fun d : D => d * (a y * (y : D)⁻¹)) he).symm.trans (inv_mul_cancel _))
  let P := S.subtype hSF
  let I := P.mapSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have htop : (I : Subgroup f.range) = ⊤ :=
    (I.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  let y : F := ⟨x, (mem_fixedPreimage (center D) a x).mpr hx⟩
  have hy : f.rangeRestrict y ∈ (P : Subgroup F).map f.rangeRestrict := by
    change _ ∈ (I : Subgroup f.range)
    rw [htop]
    trivial
  obtain ⟨s, hs, he⟩ := hy
  have hfs : f s = 1 := by
    change a s * (s : D)⁻¹ = 1
    have hss : a (s : D) = s := (MulAut.mem_fixedSubgroup a _).mp (hS hs)
    rw [hss, mul_inv_cancel]
  apply mul_inv_eq_one.mp
  exact (congrArg Subtype.val he).symm.trans hfs

/-- Commuting with the inner automorphism of an element already means fixing
that element under the same center and Sylow hypotheses. -/
theorem eq_of_commute_conj_of_fixed_sylow
    {D : Type*} [Group D] [Finite D] (a : MulAut D) (S : Sylow 2 D)
    (ha : a ^ 2 = 1) (hZ : center D ≤ a.fixedSubgroup)
    (hS : (S : Subgroup D) ≤ a.fixedSubgroup)
    (x : D) (hx : Commute (MulAut.conj x) a) : a x = x := by
  apply eq_of_central_displacement_of_fixed_sylow a S ha hZ hS x
  have he : MulAut.conj (a x * x⁻¹) = 1 := by
    rw [map_mul, map_inv]
    apply mul_inv_eq_one.mpr
    ext y
    have hh := DFunLike.congr_fun hx.eq (a.symm y)
    change x * a (a.symm y) * x⁻¹ = a (x * a.symm y * x⁻¹) at hh
    simpa only [map_mul, map_inv, a.apply_symm_apply, MulAut.conj_apply] using hh.symm
  apply mem_center_iff.mpr
  intro y
  have hh := DFunLike.congr_fun he y
  change (a x * x⁻¹) * y * (a x * x⁻¹)⁻¹ = y at hh
  exact ((mul_inv_eq_iff_eq_mul).mp hh).symm

end MulAut.CentralQuotientFusionGap
