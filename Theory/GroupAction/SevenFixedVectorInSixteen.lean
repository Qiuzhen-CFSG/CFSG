module
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.PGroup

/-!
# A seven-action fixes a vector in a subgroup of order sixteen

A group of order seven normalizing an abelian group W of order16 or32
has a fixed subgroup of order congruent to |W| modulo7. It therefore
has at least two or four elements, respectively. Any subgroup V of W
of order16 intersects it nontrivially, by the commuting-product formula.
The statement retains the original ambient centralizer.

This orbit-counting input is used for the actual upper A₇ quotient in
the normal A₆ case of Aschbacher–Smith13.3.2 and13.5.15. It requires no
representation classification or chosen coordinates.
-/


public section
open Subgroup
open scoped IsMulCommutative

namespace Subgroup

theorem seven_fixed_vector_in_sixteen
    {G : Type*} [Group G] [Finite G] (V W A : Subgroup G)
    [IsMulCommutative W] (hVW : V ≤ W) (hV : Nat.card V = 16)
    (hW : Nat.card W = 16 ∨ Nat.card W = 32)
    (hA : Nat.card A = 7) (hn : A ≤ normalizer (W : Set G)) :
    ∃ v ∈ V, v ≠ 1 ∧ v ∈ centralizer (A : Set G) := by
  let : MulDistribMulAction A W := conjMulDistribMulActionOfLeNormalizer A W hn
  let F := (FixedPoints.subgroup A W).map W.subtype
  have hFW : F ≤ W := map_subtype_le _
  have hFc : Nat.card F = Nat.card (FixedPoints.subgroup A W) :=
    card_map_of_injective W.subtype_injective
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hmod := (IsPGroup.of_card (p := 7) (n := 1)
    (show Nat.card A = 7 ^ 1 by simpa using hA)).card_modEq_card_fixedPoints W
  change Nat.card W % 7 = Nat.card (FixedPoints.subgroup A W) % 7 at hmod
  rw [← hFc] at hmod
  have hFV : F ≤ normalizer (V : Set G) :=
    (hFW.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hVW))).trans (centralizer_le_normalizer _)
  have hne : V ⊓ F ≠ ⊥ := by
    intro hz
    have hp := card_sup_eq_mul_of_normalizes_of_disjoint V F hFV
      (disjoint_iff.mpr hz)
    have hb := card_le_of_le (sup_le hVW hFW)
    rw [hp,hV] at hb
    rcases hW with hw | hw <;> rw [hw] at hmod hb <;> omega
  obtain ⟨v,hv⟩ := ne_bot_iff_exists_ne_one.mp hne
  refine ⟨v, v.property.1, fun he => hv (Subtype.ext he), ?_⟩
  obtain ⟨w,hw,hwv⟩ := v.property.2
  intro a ha
  have he := congrArg (fun x : W => (x : G)) (hw ⟨a,ha⟩)
  change a * (w : G) * a⁻¹ = (w : G) at he
  change (w : G) = (v : G) at hwv
  rw [hwv] at he
  exact mul_inv_eq_iff_eq_mul.mp he

end Subgroup