module

public import Theory.SpecificGroups.LinearHigher.A02ParabolicSections.Four
public import Theory.SpecificGroups.BinaryLinear.EvenLieLevi.OddCentralSix
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SplitSections
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.RankTwoCovers

/-!
# All even-characteristic linear quotients in the original source induction

The actual four-block PSL4 embeds in a proper two-local normalizer whenever
the ambient degree exceeds four. Proper-section induction makes this
semisimple section strongly quasithin, contradicting its literal root-torus
obstruction over fields larger than two. Thus the original central quotient
has degree at most four, and the completed low-degree cover calculations
exclude every remaining nonbinary linear Case II. Over the binary field,
proper-section induction bounds the degree by six. The final degree-six
case is excluded by lifting the actual three cubic factors through the odd
central kernel, completing the entire linear Case II family.

All groups, fields and central quotient maps are the original model witnesses.
No quasithinness of the central quotient is assumed.
Source: Aschbacher--Smith A.2.15(2) and A.2.18, printed pp.37--40.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- A genuine PSL4 proper two-local section bounds all larger-field central-quotient degrees. -/
theorem nonbinary_linear_center_quotient_degree_le_four
    (ih : TheoremAOnProperSections K G) (hG : IsQuasithin G) (hK : IsKGroup K G)
    {d a : ℕ} (ha : 1 < a)
    (iso : ClassicalGroup.IsPSL (G ⧸ center G) d (2 ^ a)) : d ≤ 4 := by
  by_contra hd
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ d by omega)
  have hm : 0 < m := by omega
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hq : 2 < Nat.card F := by
    rw [hc]
    exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) ha
  exact false_of_linear_four_split_parabolic ih hG hK (by omega) hc hq e
    (Theory.SpecificGroups.LinearHigher.FourBlock.fourNormalizer_ne_top m hm)
    (Theory.SpecificGroups.LinearHigher.FourBlock.fourNormalizer_twoLocal m hm)
    (Theory.SpecificGroups.LinearHigher.FourBlock.fourToNormalizer m)
    (Theory.SpecificGroups.LinearHigher.FourBlock.fourToNormalizer_injective m hm)

/-- Every nonbinary even-characteristic linear Case II is impossible, at every catalogue degree. -/
theorem caseII_linear_nonbinary_of_source [IsQuasisimple G]
    {S : Type u} [Group S] [Finite S] {p d a : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (ha : 1 < a) (hp : KnownSimple.LinearParameters d (2 ^ a))
    (iso : ClassicalGroup.IsPSL (G ⧸ center G) d (2 ^ a)) : False := by
  have hd := nonbinary_linear_center_quotient_degree_le_four ih h.1 h.2.1 ha iso
  have hmin := hp.2.1
  have hcases : d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact caseII_linear_two_of_source h ih (by omega) iso
  · exact caseII_linear_three_of_source h ih (by omega) iso
  · exact caseII_linear_four_of_source h ih (by omega) iso

/-- The three cubic factors of PSL₆(2) lift into an actual two-local subgroup of G. -/
theorem caseII_binary_linear_six_of_source [IsQuasisimple G]
    {S : Type u} [Group S] [Finite S] {p : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : ClassicalGroup.IsPSL (G ⧸ center G) 6 2) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := iso
  let eF := Theory.SpecificGroups.SymplecticSix.fieldEquivZModTwo F hc
  exact BinaryLinear.EvenLieLevi.OddCentralSix.not_quasithin_of_odd_center
    (center_odd_of_source h ih) (e.trans (Atlas.fieldEquivPSL 6 eF)) h.1

/-- Full linear Case II, retaining the original counterexample and proper-section induction. -/
theorem caseII_linear_of_source [IsQuasisimple G]
    {S : Type u} [Group S] [Finite S] {p d a : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (ha : 0 < a) (hp : KnownSimple.LinearParameters d (2 ^ a))
    (iso : ClassicalGroup.IsPSL (G ⧸ center G) d (2 ^ a)) : False := by
  by_cases hb : a = 1
  · subst a
    have hi : ClassicalGroup.IsPSL (G ⧸ center G) d 2 := by simpa using iso
    have hd := binary_linear_center_quotient_degree_le_six ih h.1 h.2.1 hi
    have hmin := hp.2.1
    have hcases : d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · have he := hp.2.2 rfl
      norm_num at he
    · exact caseII_linear_three_of_source h ih (by decide : 0 < 1) iso
    · exact caseII_linear_four_of_source h ih (by decide : 0 < 1) iso
    · exact caseII_binary_linear_five h ih hi
    · exact caseII_binary_linear_six_of_source h ih hi
  · exact caseII_linear_nonbinary_of_source h ih (by omega) hp iso

end CFSG.Quasithin.ChapterA.Section02.EvenLie
