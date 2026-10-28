module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.Models
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.LinearThreeExclusion.Orders

/-!
# Eliminating every ordinary even linear-three central cover

For an ordinary escaping component, O(K)=1 makes Z(K)=O₂(K). The source
congruence and p>3 exclude the exceptional fields two and four. The proved
SL₃ central-cover theorem then bounds |Z(K)| by three, whereas it is a
power of two, so Z(K)=1. Thus a model for K/O₂(K) supplies an isomorphism
of the whole K with PSL₃. The existing actual-Sylow unipotent argument
excludes it. Both SL₃ and PSL₃ quotient alternatives are treated through
their central quotients; no cover is silently discarded.

Source: Aschbacher–Smith 13.1.12(3), final paragraph on printed p.875;
A.2.12 and A.2.18 for the central-cover bound.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.LinearThreeExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- In an ordinary source component, a linear-three two-core quotient away
from fields two and four identifies the whole component with PSL₃. -/
theorem Escape.ordinary_linear_three_model {u : G} {K : Subgroup G}
    (e : Escape T L p u K) (hq : IsQuasisimple K) {q : ℕ}
    (h2 : q ≠ 2) (h4 : q ≠ 4) (hm : LinearThreeModel q (XiQuotient K)) :
    ClassicalGroup.IsPSL K 3 q := by
  let := hq
  have hz := e.ordinary_center hq
  let jQ : (K ⧸ center K) ≃* XiQuotient K := QuotientGroup.quotientMulEquivOfEq hz
  have hzQ : center (XiQuotient K) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hxC : jQ.symm x ∈ center (K ⧸ center K) :=
      (centerCongr jQ.symm ⟨x,hx⟩).property
    have hx1 : jQ.symm x = 1 := (Group.IsPerfect.center_quotient_center_eq_bot K).le hxC
    exact mem_bot.mpr (jQ.symm.map_eq_one_iff.mp hx1)
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := linearThree_center_model hm
  let j : (K ⧸ center K) ≃* PSL(3,F) :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans
      (((QuotientGroup.quotientMulEquivOfEq hzQ).trans QuotientGroup.quotientBot).symm.trans f)
  have hd3 : Nat.card (center K) ∣ 3 :=
    (Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd
      (by simpa only [hF] using h2) (by simpa only [hF] using h4) j).trans (Nat.gcd_dvd_left 3 _)
  have hcop : Nat.Coprime 3 (Nat.card (center K)) := by
    rw [hz]
    obtain ⟨a,ha⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [ha]
    exact (by decide : Nat.Coprime 3 2).pow_right a
  have hzbot : center K = ⊥ :=
    (center K).eq_bot_of_card_eq (Nat.eq_one_of_dvd_coprimes hcop hd3 dvd_rfl)
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨((QuotientGroup.quotientMulEquivOfEq hzbot).trans QuotientGroup.quotientBot).symm.trans j⟩⟩

/-- The even quotient row is impossible for every ordinary escaping component,
including all possible central covers of that quotient. -/
theorem Context.not_ordinary_even_linear_three (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hq : IsQuasisimple K)
    {n : ℕ} (hn : 2 ≤ n) (he : Even n) (hc : Nat.ModEq p (2 ^ n) 1) :
    ¬ LinearThreeModel (2 ^ n) (XiQuotient K) := by
  intro hm
  have hn4 := h.binary_degree_ge_four hn he hc
  have hq16 : 16 ≤ 2 ^ n :=
    show 2 ^ 4 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) hn4
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := e.ordinary_linear_three_model hq (by omega) (by omega) hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact h.not_projective_linear_three s e hi F hn hF ⟨f⟩

/-- Applying the full even-cover exclusion to the source model list leaves
only its odd-characteristic row in the ordinary branch. -/
theorem Context.ordinary_model_odd (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) (hq : IsQuasisimple K)
    (hm : IrreducibleComponentModels p K) : LinearThreeModel p (XiQuotient K) := by
  rcases hm with hm | ⟨n,hn,he,hc,hm⟩
  · exact hm
  · exact (h.not_ordinary_even_linear_three s e hi hq hn he hc hm).elim

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
