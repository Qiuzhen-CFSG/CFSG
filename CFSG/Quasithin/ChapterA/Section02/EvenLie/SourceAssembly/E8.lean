module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections.Source.E8
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.Exceptional

/-!
# The E8 source branch of A.2.18

The actual binary symplectic section of a proper root normalizer contradicts
proper-section induction. This supplies both the simple and central-quotient
branches, including field order two.
Source: Aschbacher--Smith A.2.15 and A.2.18, printed pp.37--40.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- Every binary E8 central-quotient model contradicts the genuine source induction. -/
theorem not_e8_center_quotient (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G) {a : ℕ}
    (iso : ExceptionalGroup.IsE8 (G ⧸ center G) (2 ^ a)) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  exact ExceptionalSections.false_of_e8 ih hG hK e

/-- The full binary E8 Case I is impossible, including q=2. -/
theorem caseI_not_e8 [IsSimpleGroup G] (ih : TheoremAOnProperSections K G)
    (hna : ¬ IsMulCommutative G) (hG : IsQuasithin G) (hK : IsKGroup K G) {a : ℕ}
    (iso : ExceptionalGroup.IsE8 G (2 ^ a)) : False := by
  have hz : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (hna (center_eq_top_iff.mp ht)).elim
  let ec : (G ⧸ center G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact not_e8_center_quotient ih hG hK (iso.of_mulEquiv ec)

/-- The E8 model is excluded at the actual simultaneous minimum. -/
theorem not_minimalCounterexample_e8 [IsSimpleGroup G]
    (h : MinimalCounterexample K G) {a : ℕ} (iso : ExceptionalGroup.IsE8 G (2 ^ a)) : False := by
  obtain ⟨hna, hqt, hk, _⟩ := h.simple_case inferInstance
  exact caseI_not_e8 h.2.theoremA hna hqt hk iso

/-- The E8 Case II exclusion uses the original counterexample and proper-section induction alone. -/
theorem caseII_e8_of_source {S : Type u} [Group S] [Finite S] {p a : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : ExceptionalGroup.IsE8 (G ⧸ center G) (2 ^ a)) : False :=
  not_e8_center_quotient ih h.1 h.2.1 iso

end CFSG.Quasithin.ChapterA.Section02.EvenLie
