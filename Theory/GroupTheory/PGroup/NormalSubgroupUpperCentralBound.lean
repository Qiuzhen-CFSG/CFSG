module

public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Mathlib.GroupTheory.Nilpotent

/-!
# Upper central bounds for normal subgroups of finite p-groups

A normal subgroup of order p^n lies in the nth upper central term. Quotienting
by the ambient center strictly decreases the order of every nontrivial normal
subgroup, since such a subgroup meets the center nontrivially. Induction on
its p-power order and the central-quotient formula prove the bound.

This is the elementary finite-p-group argument used to reduce the normal-eight
calculation in the J₄ Sylow group to its third upper central term. It requires
neither commutativity nor an automorphism-group comparison.
-/

public section

namespace Subgroup

/-- A normal subgroup of order p^n in a finite p-group is contained in Z_n. -/
theorem le_upperCentralSeries_of_card_eq_prime_pow {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hp : IsPGroup p G) (A : Subgroup G) [A.Normal] {n : ℕ}
    (hcard : Nat.card A = p ^ n) : A ≤ upperCentralSeries G n := by
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hA : A = ⊥
    · simp [hA]
    have hmeet := center_inf_ne_bot_of_normal hp A hA
    obtain ⟨⟨x, hx⟩, hx1⟩ := ne_bot_iff_exists_ne_one.mp hmeet
    let q := QuotientGroup.mk' (center G)
    let B := A.map q
    let f : A →* B := q.subgroupMap A
    have hf : Function.Surjective f := q.subgroupMap_surjective A
    have hxker : (⟨x, hx.2⟩ : A) ∈ f.ker := by
      change (⟨q x, _⟩ : B) = 1
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff x).mpr hx.1
    have hk : f.ker ≠ ⊥ := by
      intro h
      have h1 : (⟨x, hx.2⟩ : A) = 1 := by simpa [h] using hxker
      exact hx1 (Subtype.ext (congrArg (fun t : A => (t : G)) h1))
    have hkc : 1 < Nat.card f.ker := by
      let : Nontrivial f.ker := (nontrivial_iff_ne_bot _).mpr hk
      exact Finite.one_lt_card
    have hmul : Nat.card f.ker * Nat.card B = Nat.card A := by
      simpa only [index_ker, MonoidHom.range_eq_top.mpr hf, card_top] using
        f.ker.card_mul_index
    have hbpos : 0 < Nat.card B := Nat.card_pos
    obtain ⟨m, hm⟩ := (hp.to_quotient (center G)).to_subgroup B |>.exists_card_eq
    have hlt : p ^ m < p ^ n := by
      rw [← hm, ← hcard]
      nlinarith
    have hmn : m < n := (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp hlt
    have : B.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    have hb := ih m hmn (hp.to_quotient (center G)) B hm
    have ha : A ≤ upperCentralSeries G (m + 1) := by
      rw [← comap_upperCentralSeries_quotient_center]
      exact (map_le_iff_le_comap.mp hb)
    exact ha.trans (upperCentralSeries_mono G hmn)

end Subgroup
