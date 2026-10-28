module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import Theory.GroupTheory.TwoPerfectCyclicQuotient
public import Theory.GroupTheory.TwoLayerCentralizer

/-!
# The mutually normalizing cubic-block dichotomy

Two-perfect actors fix a normalized core quotient of order three. Thus the
commutator of two mutually normalizing cubic blocks lies in both embedded
four-element cores. Its order divides four. A commutator of order two is
central in the second block; two-layer residual centralization and
two-perfection then kill it. A nontrivial commutator therefore has order
four and equals both embedded cores.

This isolates the shared-core obstruction in the cubic branch of C.1.9.
The hypotheses here do not assert the upper-core guard, and the conclusion
retains that obstruction. The guard must exclude shared cores for distinct
blocks, and the general subnormal case must still establish normalization.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, C.1.7--9,
printed p.123; C.1.9 cites Aschbacher, A factorization theorem for
2-constrained groups, Proc. London Math. Soc. (3) 43 (1981), §3.4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.BlockCommutation
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizes_commutator_of_card_two (X Y : Subgroup G)
    (hn : X ≤ normalizer Y) (hc : Nat.card (⁅X, Y⁆ : Subgroup G) = 2) :
    Y ≤ centralizer ((⁅X, Y⁆ : Subgroup G) : Set G) := by
  let W := ⁅X, Y⁆
  have hWY : W ≤ Y := le_normalizer_iff_commutator_le_right.mp hn
  let : (W.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_right X Y)
  have hcard : Nat.card (W.subgroupOf Y) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWY).toEquiv).trans hc
  have hcenter := central_of_normal_card_two (W.subgroupOf Y) hcard
  intro y hy w hw
  exact congrArg Subtype.val (mem_center_iff.mp
    (hcenter (show (⟨w, hWY hw⟩ : Y) ∈ W.subgroupOf Y from hw)) ⟨y, hy⟩) |>.symm

/-- A nonzero commutator of mutually normalizing cubic blocks is both four-element cores. -/
theorem cubic_normalizing_dichotomy (X Y : Subgroup G)
    (hX : IsBlock X) (hY : IsBlock Y)
    (hqX : Nat.card (X ⧸ pCore 2 X) = 3)
    (hqY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hnX : Y ≤ normalizer X) (hnY : X ≤ normalizer Y) :
    ⁅X, Y⁆ = ⊥ ∨ (⁅X, Y⁆ = X.pCoreIn 2 ∧ X.pCoreIn 2 = Y.pCoreIn 2) := by
  have hcX : ⁅X, Y⁆ ≤ X.pCoreIn 2 := by
    rw [commutator_comm]
    exact commutator_le_pCoreIn_of_twoPerfect_of_normalizes_of_quotient_card_three
      X Y hY.short.twoPerfect hnX hqX
  have hcY : ⁅X, Y⁆ ≤ Y.pCoreIn 2 :=
    commutator_le_pCoreIn_of_twoPerfect_of_normalizes_of_quotient_card_three
      Y X hX.short.twoPerfect hnY hqY
  have hcardX : Nat.card (X.pCoreIn 2) = 4 :=
    (card_map_of_injective X.subtype_injective).trans
      (hX.short.core_card_four_of_quotient_three hqX)
  have hcardY : Nat.card (Y.pCoreIn 2) = 4 :=
    (card_map_of_injective Y.subtype_injective).trans
      (hY.short.core_card_four_of_quotient_three hqY)
  have hdiv : Nat.card (⁅X, Y⁆ : Subgroup G) ∣ 4 :=
    hcardX ▸ card_dvd_of_le hcX
  have hcards : Nat.card (⁅X, Y⁆ : Subgroup G) = 1 ∨
      Nat.card (⁅X, Y⁆ : Subgroup G) = 2 ∨ Nat.card (⁅X, Y⁆ : Subgroup G) = 4 := by
    obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card (⁅X, Y⁆ : Subgroup G) ∣ 2 ^ 2 from hdiv)
    interval_cases n <;> simp_all
  rcases hcards with h1 | h2 | h4
  · exact Or.inl (Subgroup.card_eq_one.mp h1)
  · left
    have hcent := centralizes_commutator_of_card_two X Y hnY h2
    have hr := residual_centralizes_of_two_layer Y X ⁅X, Y⁆
      ((isPGroup_pCoreIn 2 X).to_le hcX) hcent (by rw [commutator_comm])
    rw [(pResidual_eq_top_iff 2 Y).mpr hY.short.twoPerfect,
      ← MonoidHom.range_eq_map, range_subtype] at hr
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hr
  · have heX := eq_of_le_of_card_ge hcX (by rw [h4, hcardX])
    have heY := eq_of_le_of_card_ge hcY (by rw [h4, hcardY])
    exact Or.inr ⟨heX, heX.symm.trans heY⟩
end CFSG.Quasithin.ChapterC.BlockCommutation
