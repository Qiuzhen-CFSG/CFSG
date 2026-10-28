module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra

/-!
# Fixed vectors of an element of order four in dimension three

In characteristic two, an operator of order four has nilpotent displacement
whose square is nonzero. A nilpotent map of rank at most one has square
zero: restrict it to its image and use stabilization of kernels. Rank-nullity
therefore bounds the fixed space by one in dimension three.

This field-independent calculation is used over F₄ for Aschbacher–Smith,
K.1.3, printed p.453, and the triple-six exclusion in 15.4.18, printed p.1163.
-/

public section
namespace Representation.TripleSixFixedSpace
open Module LinearMap

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

private theorem square_zero_of_nilpotent_rank_one (f : Module.End F V)
    (h4 : f ^ 4 = 0) (hr : finrank F f.range ≤ 1) : f ^ 2 = 0 := by
  let g : Module.End F f.range := f.restrict (fun v _ => ⟨v, rfl⟩)
  have hg4 : g ^ 4 = 0 := Module.End.submodule_pow_eq_zero_of_pow_eq_zero rfl h4
  have hk := Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := g) hr
  have hk4 := Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := g) (hr.trans (by decide : 1 ≤ 4))
  have hg : g = 0 := by
    apply LinearMap.ker_eq_top.mp
    simpa only [pow_one, hg4, LinearMap.ker_zero] using hk.trans hk4.symm
  ext v
  exact congrArg Subtype.val (LinearMap.congr_fun hg ⟨f v, ⟨v, rfl⟩⟩)

/-- An order-four operator on a three-space in characteristic two fixes at most a line. -/
theorem fixed_rank_le_one [CharP F 2]
    (hd : finrank F V = 3) (g : Module.End F V) (h4 : g ^ 4 = 1) (h2 : g ^ 2 ≠ 1) :
    finrank F (g - 1).ker ≤ 1 := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank F V)
  let : CharP (Module.End F V) 2 := charP_of_injective_algebraMap
    (algebraMap F (Module.End F V)).injective 2
  let f : Module.End F V := g - 1
  have hnil : f ^ 4 = 0 := by
    have hh := sub_pow_char_pow_of_commute 2 2 (Commute.one_right g)
    simpa only [show 2 ^ 2 = 4 by decide, one_pow, h4, sub_self] using hh
  by_contra hn
  have hr : finrank F f.range ≤ 1 := by
    have hh := f.finrank_range_add_finrank_ker
    change ¬ finrank F f.ker ≤ 1 at hn
    rw [hd] at hh
    omega
  have hsq : f ^ 2 = 0 := square_zero_of_nilpotent_rank_one f hnil hr
  have hh := sub_pow_char_of_commute 2 (Commute.one_right g)
  have he : g ^ 2 = 1 := by
    rw [one_pow] at hh
    exact sub_eq_zero.mp (hh.symm.trans hsq)
  apply h2
  exact he

end Representation.TripleSixFixedSpace
