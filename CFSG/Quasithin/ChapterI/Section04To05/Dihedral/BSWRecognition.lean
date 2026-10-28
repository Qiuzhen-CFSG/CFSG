module

public import GorensteinWalter.BrauerSuzukiWallCardFour
public import GorensteinWalter.BrauerSuzukiWallOrderCases
public import GorensteinWalter.BrauerSuzukiWallStructure

/-!
# Concrete PSL₂ recognition from Brauer–Suzuki–Wall

For a BSW configuration with rotation subgroup of order at least four,
Bender's two order-four cases or his general order calculation supply the
structural conclusion. Its Zassenhaus recognition retains a concrete finite
field and a group isomorphism, including the cardinality of that field.

Sources: `refs/bender-bsw.tex`; Aschbacher–Smith, *The Classification of
Quasithin Groups*, I.4.1, printed p. 415.
-/

namespace CFSG.Quasithin

open GorensteinWalter

/-- The structural conclusion in all BSW branches with `|K| ≥ 4`. -/
public theorem bsw_conclusion_of_four_le_card_K
    {G : Type*} [Group G] [Finite G] (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 ≤ Nat.card h.K) : Nonempty (BrauerSuzukiWallConclusion G) := by
  by_cases hkFour : Nat.card h.K = 4
  · obtain ⟨V, X, hV, hCentV, hNcard, hXle, hXcard, hcase⟩ :=
      h.exists_bender_case_split_of_card_K_eq_four hkFour
    rcases hcase with hcaseOne | hcaseTwo
    · exact brauerSuzukiWallConclusion_nonempty_of_card_K_eq_four_of_bender_case_one
        h hkFour ⟨V, X, hV, hCentV, hNcard, hXle, hXcard, hcaseOne⟩
    · have hGcard : Nat.card G = 168 :=
        h.card_eq_168_of_card_K_eq_four_of_bender_case_two
          hkFour V X hV hCentV hNcard hXle hXcard hcaseTwo
      exact h.conclusion_nonempty_of_card_K_eq_four_of_bender_case_two_of_card_eq_168
        hkFour V X hV hCentV hNcard hXle hXcard hcaseTwo hGcard
  · have hkHigh : 4 < Nat.card h.K := by omega
    exact brauerSuzukiWallConclusion_nonempty_of_order_cases h hkHigh (h.order_cases hkHigh)

/-- The concrete odd-characteristic PSL₂ model needed by I.4.1. -/
public theorem exists_field_mulEquiv_psl2_of_bsw_four_le_card_K
    {G : Type*} [Group G] [Finite G] (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 ≤ Nat.card h.K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      IsOddPrimePower (Nat.card F) ∧ Nonempty (G ≃* PSL2 F) := by
  obtain ⟨c⟩ := bsw_conclusion_of_four_le_card_K h hk
  obtain ⟨F, hF, hFin, _, hOdd, e⟩ := c.exists_field_mulEquiv_psl2
  exact ⟨F, hF, hFin, hOdd, e⟩

end CFSG.Quasithin
