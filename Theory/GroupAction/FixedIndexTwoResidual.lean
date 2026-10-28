module

public import Theory.GroupTheory.PResidual.PerfectCover
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# Two-perfect actors fixing a subgroup of index at most two

An automorphism fixing an index-two subgroup fixes each displacement
x⁻¹a(x). Iteration expresses aᵐ(x) as x times the m-th power of that
displacement. A uniform two-power exponent therefore makes the whole
action image a two-group. Two-perfectness kills this image.

Neither elementary abelianness nor a coprime actor order is required.
This supplies the corrected residual-action step in Aschbacher–Smith,
Lemma 12.8.10(5), printed p.854 (PDF p.871), where the actor is the new
minimal-parabolic two-residual, rather than the accumulated group.
-/

open Subgroup

namespace MulAut
variable {V : Type*} [Group V] [Finite V]

omit [Finite V] in
private theorem fixed_index_two_pow (D : Subgroup V) (hi : D.index = 2)
    (a : MulAut V) (hf : ∀ x ∈ D, a x = x) (x : V) (m : ℕ) :
    (a ^ m) x = x * (x⁻¹ * a x) ^ m := by
  have hmem (y : V) : a y ∈ D ↔ y ∈ D := by
    constructor
    · intro hy
      have he : a y = y := a.injective (hf (a y) hy)
      exact he ▸ hy
    · intro hy
      rw [hf y hy]
      exact hy
  have hd : x⁻¹ * a x ∈ D := by
    rw [D.mul_mem_iff_of_index_two hi]
    simp only [D.inv_mem_iff, hmem]
  have hfix := hf _ hd
  induction m with
  | zero => simp
  | succ m hm =>
    rw [pow_succ', MulAut.mul_apply, hm, map_mul, map_pow, hfix, pow_succ']
    simp only [← mul_assoc, mul_inv_cancel, one_mul]

/-- Fixing a subgroup of index at most two pointwise gives a two-group image.
The group acted on need not be abelian. -/
public theorem isPGroup_range_of_fixed_index_le_two {A : Type*} [Group A]
    (ρ : A →* MulAut V) (hV : IsPGroup 2 V)
    (D : Subgroup V) (hi : D.index ≤ 2)
    (hf : ∀ a : A, ∀ x ∈ D, ρ a x = x) : IsPGroup 2 ρ.range := by
  have hpos : 0 < D.index := by rw [Subgroup.index_eq_card]; exact Nat.card_pos
  by_cases htop : D.index = 1
  · have hD := index_eq_one.mp htop
    intro a
    obtain ⟨b, hb⟩ := a.property
    refine ⟨0, ?_⟩
    apply Subtype.ext
    change a.val ^ (2 ^ 0) = 1
    simp only [pow_zero, pow_one]
    rw [← hb]
    ext x
    exact hf b x (hD ▸ mem_top x)
  · have htwo : D.index = 2 := by omega
    obtain ⟨m, hm⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp hV
    intro a
    obtain ⟨b, hb⟩ := a.property
    refine ⟨m, ?_⟩
    apply Subtype.ext
    change a.val ^ (2 ^ m) = 1
    rw [← hb]
    ext x
    rw [fixed_index_two_pow D htwo (ρ b) (hf b) x, hm, mul_one]
    rfl

/-- A two-perfect group acts trivially if it fixes a subgroup of index at most two. -/
public theorem eq_one_of_pPerfect_of_fixed_index_le_two {A : Type*} [Group A]
    (ρ : A →* MulAut V) (hA : IsPPerfect 2 A) (hV : IsPGroup 2 V)
    (D : Subgroup V) (hi : D.index ≤ 2)
    (hf : ∀ a : A, ∀ x ∈ D, ρ a x = x) (a : A) : ρ a = 1 := by
  have hp := isPGroup_range_of_fixed_index_le_two ρ hV D hi hf
  have hk := hA ρ.ker inferInstance
    (hp.of_equiv (QuotientGroup.quotientKerEquivRange ρ).symm)
  exact (show a ∈ ρ.ker from hk ▸ mem_top a)
end MulAut
