module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ExceptionalSections.Source
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.Models
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.SimpleCase

/-!
# The actual F4, E6, E7 and twisted E6 branches in both A.2.18 cases

The root-word Sp6(2) construction gives a section of a proper two-local of the
literal exceptional central quotients over every field of characteristic two, including
field order two. Applying proper-section induction to the original group
excludes its actual model predicate. In Case I the original nonabelian simple
group has trivial center; in Case II the original quotient is already marked.
No model-order, multiplier or quotient-quasithinness premise is inserted.
Source: Aschbacher--Smith A.2.15(2) and A.2.18, printed pp.37--40.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- Every binary F4 central-quotient model contradicts the genuine source induction. -/
theorem not_f4_center_quotient (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G) {a : ℕ}
    (iso : ExceptionalGroup.IsF4 (G ⧸ center G) (2 ^ a)) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  exact ExceptionalSections.false_of_f4 ih hG hK e

/-- The full binary F4 Case I is impossible, including q=2. -/
theorem caseI_not_f4 [IsSimpleGroup G] (ih : TheoremAOnProperSections K G)
    (hna : ¬ IsMulCommutative G) (hG : IsQuasithin G) (hK : IsKGroup K G) {a : ℕ}
    (iso : ExceptionalGroup.IsF4 G (2 ^ a)) : False := by
  have hz : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (hna (center_eq_top_iff.mp ht)).elim
  let ec : (G ⧸ center G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact not_f4_center_quotient ih hG hK (iso.of_mulEquiv ec)

/-- The F4 model is excluded at the actual simultaneous minimum. -/
theorem not_minimalCounterexample_f4 [IsSimpleGroup G]
    (h : MinimalCounterexample K G) {a : ℕ} (iso : ExceptionalGroup.IsF4 G (2 ^ a)) : False := by
  obtain ⟨hna, hqt, hk, _⟩ := h.simple_case inferInstance
  exact caseI_not_f4 h.2.theoremA hna hqt hk iso

/-- The F4 Case II exclusion uses the original counterexample and proper-section induction alone. -/
theorem caseII_f4_of_source {S : Type u} [Group S] [Finite S] {p a : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : ExceptionalGroup.IsF4 (G ⧸ center G) (2 ^ a)) : False :=
  not_f4_center_quotient ih h.1 h.2.1 iso

/-- Every binary E6 central-quotient model contradicts the genuine source induction. -/
theorem not_e6_center_quotient (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G) {a : ℕ}
    (iso : ExceptionalGroup.IsE6 (G ⧸ center G) (2 ^ a)) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  exact ExceptionalSections.false_of_e6 ih hG hK e

/-- The full binary E6 Case I is impossible, including q=2. -/
theorem caseI_not_e6 [IsSimpleGroup G] (ih : TheoremAOnProperSections K G)
    (hna : ¬ IsMulCommutative G) (hG : IsQuasithin G) (hK : IsKGroup K G) {a : ℕ}
    (iso : ExceptionalGroup.IsE6 G (2 ^ a)) : False := by
  have hz : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (hna (center_eq_top_iff.mp ht)).elim
  let ec : (G ⧸ center G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact not_e6_center_quotient ih hG hK (iso.of_mulEquiv ec)

/-- The E6 model is excluded at the actual simultaneous minimum. -/
theorem not_minimalCounterexample_e6 [IsSimpleGroup G]
    (h : MinimalCounterexample K G) {a : ℕ} (iso : ExceptionalGroup.IsE6 G (2 ^ a)) : False := by
  obtain ⟨hna, hqt, hk, _⟩ := h.simple_case inferInstance
  exact caseI_not_e6 h.2.theoremA hna hqt hk iso

/-- The E6 Case II exclusion uses the original counterexample and proper-section induction alone. -/
theorem caseII_e6_of_source {S : Type u} [Group S] [Finite S] {p a : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : ExceptionalGroup.IsE6 (G ⧸ center G) (2 ^ a)) : False :=
  not_e6_center_quotient ih h.1 h.2.1 iso

/-- Every binary TwistedE6 central-quotient model contradicts the genuine source induction. -/
theorem not_twisted_e6_center_quotient (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G) {a : ℕ}
    (iso : ExceptionalGroup.IsTwistedE6 (G ⧸ center G) (2 ^ a)) : False := by
  obtain ⟨p, m, hp, hc, ⟨e⟩⟩ := iso
  have hd : p ∣ 2 ^ a := by
    rw [← hc]
    exact dvd_pow_self p (by omega : m + 1 ≠ 0)
  have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
    (hp.out.dvd_of_dvd_pow hd)
  subst p
  exact ExceptionalSections.false_of_twisted_e6 ih hG hK m e

/-- The full binary TwistedE6 Case I is impossible, including q=2. -/
theorem caseI_not_twisted_e6 [IsSimpleGroup G] (ih : TheoremAOnProperSections K G)
    (hna : ¬ IsMulCommutative G) (hG : IsQuasithin G) (hK : IsKGroup K G) {a : ℕ}
    (iso : ExceptionalGroup.IsTwistedE6 G (2 ^ a)) : False := by
  have hz : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (hna (center_eq_top_iff.mp ht)).elim
  let ec : (G ⧸ center G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact not_twisted_e6_center_quotient ih hG hK (iso.of_mulEquiv ec)

/-- The TwistedE6 model is excluded at the actual simultaneous minimum. -/
theorem not_minimalCounterexample_twisted_e6 [IsSimpleGroup G]
    (h : MinimalCounterexample K G) {a : ℕ} (iso : ExceptionalGroup.IsTwistedE6 G (2 ^ a)) : False := by
  obtain ⟨hna, hqt, hk, _⟩ := h.simple_case inferInstance
  exact caseI_not_twisted_e6 h.2.theoremA hna hqt hk iso

/-- The TwistedE6 Case II exclusion uses the original counterexample and proper-section induction alone. -/
theorem caseII_twisted_e6_of_source {S : Type u} [Group S] [Finite S] {p a : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : ExceptionalGroup.IsTwistedE6 (G ⧸ center G) (2 ^ a)) : False :=
  not_twisted_e6_center_quotient ih h.1 h.2.1 iso

/-- Every binary E7 central-quotient model contradicts the genuine source induction. -/
theorem not_e7_center_quotient (ih : TheoremAOnProperSections K G)
    (hG : IsQuasithin G) (hK : IsKGroup K G) {a : ℕ}
    (iso : ExceptionalGroup.IsE7 (G ⧸ center G) (2 ^ a)) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  exact ExceptionalSections.false_of_e7 ih hG hK e

/-- The full binary E7 Case I is impossible, including q=2. -/
theorem caseI_not_e7 [IsSimpleGroup G] (ih : TheoremAOnProperSections K G)
    (hna : ¬ IsMulCommutative G) (hG : IsQuasithin G) (hK : IsKGroup K G) {a : ℕ}
    (iso : ExceptionalGroup.IsE7 G (2 ^ a)) : False := by
  have hz : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (hna (center_eq_top_iff.mp ht)).elim
  let ec : (G ⧸ center G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact not_e7_center_quotient ih hG hK (iso.of_mulEquiv ec)

/-- The E7 model is excluded at the actual simultaneous minimum. -/
theorem not_minimalCounterexample_e7 [IsSimpleGroup G]
    (h : MinimalCounterexample K G) {a : ℕ} (iso : ExceptionalGroup.IsE7 G (2 ^ a)) : False := by
  obtain ⟨hna, hqt, hk, _⟩ := h.simple_case inferInstance
  exact caseI_not_e7 h.2.theoremA hna hqt hk iso

/-- The E7 Case II exclusion uses the original counterexample and proper-section induction alone. -/
theorem caseII_e7_of_source {S : Type u} [Group S] [Finite S] {p a : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : ExceptionalGroup.IsE7 (G ⧸ center G) (2 ^ a)) : False :=
  not_e7_center_quotient ih h.1 h.2.1 iso


end CFSG.Quasithin.ChapterA.Section02.EvenLie
