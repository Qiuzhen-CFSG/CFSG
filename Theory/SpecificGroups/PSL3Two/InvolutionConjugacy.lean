module

public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Transvections
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# The involution class in PSL₃(2)

Every nonidentity involution on the three-dimensional binary space is a
transvection. Its displacement N = t - 1 satisfies N² = 0, so its image lies
in its kernel; rank-nullity bounds its rank by one. The existing conjugacy
theorem for binary transvections then supplies an actual conjugating linear
automorphism. Transport through the canonical SL/GL/PSL equivalences retains
an actual conjugator in the projective special linear group.

This is the concrete quotient fact used in the nonsplit-block argument for
Aschbacher–Smith 14.4.5, printed p.1008 of `refs/quasithin.pdf`. The passage
from rank-one displacement to a transvection follows the proof in
`BinaryLinear.TransvectionCubicCentralizer`.
-/

namespace Matrix.PSL3Two

open BinaryLinear.OuterCyclic

private theorem involution_displacement_rank_le_one
    (t : LinearGroup 3) (ht : t ^ 2 = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1 := by
  let N := t.toLinearMap - LinearMap.id
  have htt (x : Space 3) : t (t x) = x := by
    have h := congrArg (fun g : LinearGroup 3 => g x) ht
    simpa [pow_two] using h
  have hN (x : Space 3) : N (N x) = 0 := by
    change t (t x - x) - (t x - x) = 0
    rw [map_sub, htt]
    simp only [ZModModule.sub_eq_add]
    calc
      (x + t x) + (t x + x) = (x + x) + (t x + t x) := by abel
      _ = 0 := by simp only [ZModModule.add_self]
  have hle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro x ⟨y, rfl⟩
    exact hN y
  have hdim := N.finrank_range_add_finrank_ker
  have hmono := Submodule.finrank_mono hle
  have hthree : Module.finrank (ZMod 2) (Space 3) = 3 := by simp [Space]
  rw [hthree] at hdim
  change Module.finrank (ZMod 2) (LinearMap.range N) ≤ 1
  omega

private theorem isTransvection_of_orderOf_eq_two
    (t : LinearGroup 3) (ht : orderOf t = 2) : IsTransvection t := by
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr
    (involution_displacement_rank_le_one t ht2)
  have hact (w : Space 3) : t w = w + f w • v := LinearMap.congr_fun he w
  have hf : f ≠ 0 := by
    intro h
    apply ht1
    apply LinearEquiv.ext
    intro w
    simpa [h] using hact w
  have hv : v ≠ 0 := by
    intro h
    apply ht1
    apply LinearEquiv.ext
    intro w
    simpa [h] using hact w
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with h | h
    · exact h
    · have htv : t v = 0 := by
        rw [hact, h, one_smul, ZModModule.add_self]
      exact (hv (t.map_eq_zero_iff.mp htv)).elim
  exact ⟨v, f, hv, hf, hfv, LinearEquiv.ext hact⟩

/-- All involutions of the actual PSL₃(2) are conjugate, with a conjugator
in that same projective group. -/
public theorem involutions_conjugate (a b : PSL)
    (ha : orderOf a = 2) (hb : orderOf b = 2) :
    ∃ g : PSL, MulAut.conj g a = b := by
  let e : PSL ≃* LinearGroup 3 :=
    equiv.symm.trans (equivGL.trans (matrixEquivLinear 3))
  obtain ⟨g, hg⟩ := transvections_conjugate
    (isTransvection_of_orderOf_eq_two (e a) ((e.orderOf_eq a).trans ha))
    (isTransvection_of_orderOf_eq_two (e b) ((e.orderOf_eq b).trans hb))
  refine ⟨e.symm g, e.injective ?_⟩
  simpa only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply] using hg

/-- The unique involution class, in the form used by quotient lifting. -/
public theorem isConj_of_orderOf_eq_two (a b : PSL)
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b :=
  isConj_iff.mpr (involutions_conjugate a b ha hb)

end Matrix.PSL3Two
