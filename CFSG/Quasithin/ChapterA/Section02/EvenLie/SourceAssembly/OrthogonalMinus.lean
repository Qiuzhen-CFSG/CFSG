module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.OrthogonalBinary
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.UnitaryFourCover
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.Binary

/-!
# The complete minus-type orthogonal Case I and its low-rank Case II

The exterior-square comparison now includes the binary fixed field, where
ambient SU4 perfectness supplies the previously missing image containment.
The binary parabolic restriction leaves ranks two and three, identified with
PSL2 over the quadratic extension and the actual PSU4 model. Together with
the larger-field root-normalizer restriction this completes Case I at every
catalogue parameter. The same marked comparison excludes all rank-three
central quotients in Case II and completes its binary minus family.

Source: Aschbacher--Smith A.2.18, printed p.40; GLS3 Section 2.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The exact minus-six model is the actual unitary-four model at every positive exponent. -/
theorem orthogonalMinus_three_unitary [IsSimpleGroup G] {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPOmegaMinus G 3 (2 ^ a)) :
    ClassicalGroup.IsPSU G 4 (2 ^ a) := by
  obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := iso
  let : IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F) := e.symm.isSimpleGroup
  obtain ⟨E,hE,hEfin,J,hcard,hconj,⟨f⟩⟩ :=
    ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.exists_comparison_pos a ha hc
  exact ⟨E,hE,hEfin,J,hcard,hconj,⟨e.trans f⟩⟩

/-- All minus-type classical catalogue parameters are resolved in the original simple case. -/
theorem caseI_orthogonalMinus [IsSimpleGroup G] {K : GroupClass.{u}}
    (ih : TheoremAOnProperSections K G) (hna : ¬ IsMulCommutative G)
    (hG : IsQuasithin G) (hK : IsKGroup K G)
    {r a : ℕ} (ha : 0 < a) (hp : KnownSimple.OrthogonalMinusParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPOmegaMinus G r (2 ^ a)) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  by_cases ha1 : a = 1
  · subst a
    have hi : ClassicalGroup.IsPOmegaMinus G r 2 := by simpa using iso
    have hz : center G = ⊥ := by
      rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · exact (hna (center_eq_top_iff.mp ht)).elim
    let ec : (G ⧸ center G) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    have hr := binary_minus_model_rank_le_three ih hG hK (hi.of_mulEquiv ec)
    have hmin := hp.2
    have hr' : r = 2 ∨ r = 3 := by omega
    rcases hr' with rfl | rfl
    · have hc : IsTheoremCModel G := .bender (.linear 2 (by decide)
        (by simpa using orthogonalMinus_two_linear (by decide : 0 < 1) iso))
      exact ⟨hc.toTheoremBModel,fun _ => hc⟩
    · exact caseI_unitary hG (by decide : 0 < 1)
        ⟨hp.1,by decide,by decide,by decide⟩
        (orthogonalMinus_three_unitary (by decide : 0 < 1) iso)
  · exact caseI_orthogonalMinus_nonbinary hG (by omega) hp iso

/-- The complete minus-type Case I contradicts the literal simultaneous minimum. -/
theorem not_minimalCounterexample_orthogonalMinus [IsSimpleGroup G] {K : GroupClass.{u}}
    (h : MinimalCounterexample K G) {r a : ℕ} (ha : 0 < a)
    (hp : KnownSimple.OrthogonalMinusParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPOmegaMinus G r (2 ^ a)) : False := by
  obtain ⟨hna,hqt,hk,hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb,hc⟩ := caseI_orthogonalMinus h.2.theoremA hna hqt hk ha hp iso
  rcases hfails with hn | ⟨hs,hn⟩
  · exact hn hb
  · exact hn (hc hs)

variable [IsQuasisimple G] {K : GroupClass.{u}} {S : Type u} [Group S] [Finite S] {p : ℕ}

/-- Every rank-three minus central quotient is excluded by its literal unitary-four comparison. -/
theorem caseII_orthogonalMinus_three_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPOmegaMinus (G ⧸ center G) 3 (2 ^ a)) : False := by
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  exact caseII_unitary_four_of_source h ih ha (orthogonalMinus_three_unitary ha iso)

/-- Every binary minus central quotient is excluded under the original source induction. -/
theorem caseII_orthogonalMinus_binary_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {r : ℕ} (hr : 2 ≤ r)
    (iso : ClassicalGroup.IsPOmegaMinus (G ⧸ center G) r 2) : False := by
  have hb := binary_minus_model_rank_le_three ih h.1 h.2.1 iso
  have hr' : r = 2 ∨ r = 3 := by omega
  rcases hr' with rfl | rfl
  · exact caseII_orthogonalMinus_two_of_source h ih (by decide : 0 < 1) (by simpa using iso)
  · exact caseII_orthogonalMinus_three_of_source h ih (by decide : 0 < 1) (by simpa using iso)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
