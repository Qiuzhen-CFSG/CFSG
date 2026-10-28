module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.Triality.Parameters

/-!
# Rank-one quotient constraints for the triality block calculation

A χ₀ block whose two-core quotient is PSL₂(2ⁿ) must have n > 1 and
module order 2^(2n). This follows by comparing the three actual quotient
orders in C.1.12; the polynomial x(x²-1) is strictly increasing for x ≥ 2.
The statement includes n = 1, when PSL₂(2) has order six and cannot be
the quotient of a χ₀ block. A short subgroup with quotient of order three
at that parameter still needs a separate calculation.

We also record the structural obstruction when [O₂(B),B] = O₂(B) and
that core is nonabelian. Both tests concern the intrinsic short subgroup B,
not an identification of a whole parabolic with an escaping block.

These are necessary-condition tests for the remaining relative subgroup
calculations in Aschbacher–Smith 2.3.9(7), printed p.526. They do not
establish those calculations or the Levi identifications of F.1.12(I)(4).
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase

open Subgroup ChapterC
open scoped MatrixGroups

private theorem rankOneOrder_strictMono {x y : ℕ} (hx : 2 ≤ x) (hxy : x < y) :
    x * (x ^ 2 - 1) < y * (y ^ 2 - 1) := by
  have hx2 : 1 < x ^ 2 := by nlinarith
  have hsq : x ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt hxy) 2
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hxy (Nat.sub_pos_of_lt hx2))
    (Nat.mul_le_mul_left y (Nat.sub_le_sub_right hsq 1))

private theorem rankOneOrder_injective {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (h : x * (x ^ 2 - 1) = y * (y ^ 2 - 1)) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact (ne_of_lt (rankOneOrder_strictMono hx hlt) h).elim
  · exact heq
  · exact (ne_of_lt (rankOneOrder_strictMono hy hgt) h.symm).elim

variable {K : Type*} [Group K]

/-- The quotient order fixes the only possible χ₀ module order. This is
only a necessary condition and does not identify the two A₅ representations. -/
theorem chiZero_rankOne_order (h : IsChiZeroBlock K) (n : ℕ) (hn : 0 < n)
    (hq : Nat.card (K ⧸ pCore 2 K) = 2 ^ n * (2 ^ (2 * n) - 1)) :
    1 < n ∧ Nat.card (BlockModule K) = 2 ^ (2 * n) := by
  have htwo : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  rcases chiZero_order_module h with ⟨m, hm, he, hv⟩ | ⟨he, _⟩ | ⟨he, hv⟩
  · have hm2 : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
    have heq : 2 ^ n = 2 ^ m := rankOneOrder_injective htwo hm2 (by
      simpa [← pow_mul, Nat.mul_comm _ 2] using hq.symm.trans he)
    have hnm : n = m := Nat.pow_right_injective (by decide : 1 < 2) heq
    simpa [hnm] using And.intro hm hv
  · have hl := Nat.mul_le_mul htwo
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left htwo 2) 1)
    have hq3 : 2 ^ n * ((2 ^ n) ^ 2 - 1) = 3 := by
      simpa [← pow_mul, Nat.mul_comm _ 2] using hq.symm.trans he
    rw [hq3] at hl
    norm_num at hl
  · have heq : 2 ^ n = 4 := rankOneOrder_injective htwo (by decide) (by
      simpa [← pow_mul, Nat.mul_comm _ 2] using hq.symm.trans he)
    have hn2 : n = 2 := Nat.pow_right_injective (by decide : 1 < 2) heq
    norm_num [hn2, hv]

/-- A supplied genuine projective quotient gives the same necessary condition;
the characteristic-two SL₂/PSL₂ equivalence is proved independently. -/
theorem chiZero_projective_quotient_module {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : IsChiZeroBlock K) (n : ℕ) (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K ⧸ pCore 2 K) ≃* PSL(2, F)) :
    1 < n ∧ Nat.card (BlockModule K) = 2 ^ (2 * n) := by
  apply chiZero_rankOne_order h n hn
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).toEquiv,
    Atlas.card_sl_two, hF]
  simp only [← pow_mul, Nat.mul_comm n 2]

/-- A quotient of order six is never an allowed χ₀ quotient. -/
theorem not_chiZero_of_quotient_six
    (hq : Nat.card (K ⧸ pCore 2 K) = 6) : ¬ IsChiZeroBlock K := by
  intro h
  have hn := (chiZero_rankOne_order h 1 (by decide) (by simpa using hq)).1
  omega

/-- A wrong module order rules out the allowed natural rank-one blocks,
including the alternating alternatives with the same quotient order. -/
theorem not_chiZero_of_rankOne_module (n : ℕ) (hn : 0 < n)
    (hq : Nat.card (K ⧸ pCore 2 K) = 2 ^ n * (2 ^ (2 * n) - 1))
    (hv : Nat.card (BlockModule K) ≠ 2 ^ (2 * n)) : ¬ IsChiZeroBlock K :=
  fun h => hv (chiZero_rankOne_order h n hn hq).2

/-- The A₃ exception requires its actual two-dimensional binary module. -/
theorem not_chiZero_of_quotient_three_module
    (hq : Nat.card (K ⧸ pCore 2 K) = 3)
    (hv : Nat.card (BlockModule K) ≠ 4) : ¬ IsChiZeroBlock K := by
  intro h
  have he := chiZero_quotient_square h hv
  have hm := chiZero_module_card h
  obtain ⟨n, hn, hcard⟩ := hm
  have hl : 4 ≤ Nat.card (BlockModule K) := by
    rw [hcard]
    change 2 ^ 2 ≤ 2 ^ (2 * n)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hl' : 3 ≤ Nat.card (BlockModule K) - 1 := by omega
  have hbound := Nat.mul_le_mul hl (Nat.pow_le_pow_left hl' 2)
  rw [← he, hq] at hbound
  norm_num at hbound

/-- If the whole two-core is moved and is nonabelian, C.1.7's centrality
clause fails. Use this on an identified subnormal subgroup, not merely its
containing parabolic. -/
theorem not_short_of_moved_nonabelian_core
    (hm : blockU K = pCore 2 K)
    (hn : ⁅pCore 2 K, pCore 2 K⁆ ≠ ⊥) : ¬ IsShort K := by
  intro h
  apply hn
  apply commutator_eq_bot_iff_le_centralizer.mpr
  simpa only [hm] using h.central

/-- For the three-arm Levi quotient, the necessary module order is q⁶,
because its coefficient field is the cubic extension. The quotient
isomorphism is an explicit input to this test, not a claimed Levi theorem. -/
theorem chiZero_cubic_quotient_module (P : _root_.Triality.Standard.Parameters)
    (hp : P.prime = 2) (h : IsChiZeroBlock K)
    (e : (K ⧸ pCore 2 K) ≃* PSL(2, _root_.Triality.Standard.ExtensionField P)) :
    Nat.card (BlockModule K) = P.q ^ 6 := by
  let : CharP (_root_.Triality.Standard.ExtensionField P) 2 :=
    hp ▸ inferInstanceAs (CharP (_root_.Triality.Standard.ExtensionField P) P.prime)
  have hF : Nat.card (_root_.Triality.Standard.ExtensionField P) =
      2 ^ (3 * P.exponent) := by
    rw [_root_.Triality.Standard.card_extensionField,
      _root_.Triality.Standard.Parameters.q, hp, ← pow_mul, Nat.mul_comm P.exponent 3]
  have hm := (chiZero_projective_quotient_module h (3 * P.exponent)
    (by have := P.exponent_pos; omega) hF e).2
  simpa only [_root_.Triality.Standard.Parameters.q, hp, ← pow_mul,
    show 2 * (3 * P.exponent) = P.exponent * 6 by omega] using hm

/-- For the central-vertex Levi quotient the field is the base field.
At q = 2 this condition is impossible; subnormal C₃ quotients still require
the separate module test above. -/
theorem chiZero_base_quotient_module (P : _root_.Triality.Standard.Parameters)
    (hp : P.prime = 2) (h : IsChiZeroBlock K)
    (e : (K ⧸ pCore 2 K) ≃* PSL(2, GaloisField P.prime P.exponent)) :
    1 < P.exponent ∧ Nat.card (BlockModule K) = P.q ^ 2 := by
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  have hF : Nat.card (GaloisField P.prime P.exponent) = 2 ^ P.exponent := by
    rw [GaloisField.card P.prime P.exponent (Nat.ne_of_gt P.exponent_pos), hp]
  have hm := chiZero_projective_quotient_module h P.exponent P.exponent_pos hF e
  simpa only [_root_.Triality.Standard.Parameters.q, hp, ← pow_mul,
    Nat.mul_comm P.exponent 2] using hm

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase

end
