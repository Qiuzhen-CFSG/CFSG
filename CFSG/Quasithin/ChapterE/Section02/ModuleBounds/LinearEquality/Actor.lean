module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearCubic

/-!
# Equality-range actor rank from the original linear-two ratio

If the actual actor ratio is at least two, its fixed codimension is at
least twice its rank. The exact source star count bounds that same
codimension by the actor rank plus m. Therefore the actor rank is at
most m. This retains the original action and exact kernel coordinates,
and is the numerical step before natural-module recognition in
Aschbacher–Smith E.2.15, printed p.228.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}
  {D Q : Type*} [Group D] [Finite D] [Group Q] [Finite Q]
  [IsElementaryAbelian 2 Q]

theorem linear_two_actor_rank_le_of_two_le_ratio
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* SL(2,F))
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (hratio : 2 ≤ actionRatio ρ f.range) :
    Nat.log 2 ((Z V g).relIndex (A V M g)) ≤ m := by
  have hk := h.actor_kernel e ρ hρ f ha
  have he := h.actor_elementary hproper hfit f hk
  have hb := h.actor_fixed_bound_add_star_dimension e ρ f hk he ha m
    (h.star_card_le_linear_two m hcard ξ)
  have hr : rank f.range = Nat.log 2 ((Z V g).relIndex (A V M g)) := by
    change Nat.log 2 (Nat.card f.range) = _
    rw [← index_ker,hk]
    rfl
  have h0 : (rank f.range : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he.rank_pos)
  have hl : 2*rank f.range ≤ fixedCodim ρ f.range := by
    have hh := (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl (by simp))).mp hratio
    exact_mod_cast hh
  omega
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
