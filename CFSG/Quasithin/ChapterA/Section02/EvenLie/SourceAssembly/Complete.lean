module
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.E8

/-!
# Complete even-characteristic source dispatch

All sixteen literal carrier alternatives satisfy the simultaneous simple-case
conclusions and exclude the original quasisimple counterexample. The actual
proper-section induction is retained; no family classification, center-primary
or quotient-quasithinness premise is added.
Source: Aschbacher--Smith A.2.18, printed p.40.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {K : GroupClass.{u}} {G : Type u} [Group G] [Finite G]

/-- Complete A.2.18 Case I for the exact characteristic-two carrier catalogue. -/
theorem caseI_of_evenLieCarrier [IsSimpleGroup G]
    (ih : TheoremAOnProperSections K G) (hna : ¬ IsMulCommutative G)
    (hG : IsQuasithin G) (hK : IsKGroup K G) (model : IsEvenLieCarrier G) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  cases model with
  | linear d a ha hp iso => exact caseI_linear hG ha hp iso
  | unitary d a ha hp iso => exact caseI_unitary hG ha hp iso
  | symplectic r a ha hp iso => exact caseI_symplectic ih hna hG hK ha hp iso
  | orthogonalPlus r a ha hp iso => exact caseI_orthogonalPlus ih hna hG hK ha hp iso
  | orthogonalOdd r a ha hp iso => exact caseI_orthogonalOdd ih hna hG hK ha hp iso
  | orthogonalMinus r a ha hp iso => exact caseI_orthogonalMinus ih hna hG hK ha hp iso
  | g2 a ha iso => exact caseI_g2 ha iso
  | suzuki m hm iso => exact caseI_suzuki hm iso
  | triality a ha iso => exact caseI_triality ha iso
  | reeF4 m hm iso => exact caseI_reeF4 hm iso
  | f4 a ha iso => exact (caseI_not_f4 ih hna hG hK iso).elim
  | e6 a ha iso => exact (caseI_not_e6 ih hna hG hK iso).elim
  | e7 a ha iso => exact (caseI_not_e7 ih hna hG hK iso).elim
  | e8 a ha iso => exact (caseI_not_e8 ih hna hG hK iso).elim
  | twistedE6 a ha iso => exact (caseI_not_twisted_e6 ih hna hG hK iso).elim
  | smallDerived model => exact caseI_smallDerived model

/-- Every exact even-Lie source carrier is excluded at the simultaneous minimum. -/
theorem not_minimalCounterexample_evenLieCarrier [IsSimpleGroup G]
    (h : MinimalCounterexample K G) (model : IsEvenLieCarrier G) : False := by
  obtain ⟨hna,hqt,hk,hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb,hc⟩ := caseI_of_evenLieCarrier h.2.theoremA hna hqt hk model
  rcases hfails with hn | ⟨hs,hn⟩
  · exact hn hb
  · exact hn (hc hs)

/-- Complete A.2.18 Case II for the actual central quotient and original source induction. -/
theorem caseII_of_evenLieCarrier [IsQuasisimple G]
    {S : Type u} [Group S] [Finite S] {p : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (model : IsEvenLieCarrier (G ⧸ center G)) : False := by
  cases model with
  | linear d a ha hp iso => exact caseII_linear_of_source h ih ha hp iso
  | unitary d a ha hp iso => exact caseII_unitary_of_source h ih ha hp iso
  | symplectic r a ha hp iso => exact caseII_symplectic_of_source h ih ha hp iso
  | orthogonalPlus r a ha hp iso => exact caseII_orthogonalPlus_of_source h ih ha hp iso
  | orthogonalOdd r a ha hp iso => exact caseII_orthogonalOdd_of_source h ih ha hp iso
  | orthogonalMinus r a ha hp iso => exact caseII_orthogonalMinus_of_source h ih ha hp iso
  | g2 a ha iso => exact caseII_g2_of_source h ih ha iso
  | suzuki m hm iso => exact caseII_suzuki_of_source h ih hm iso
  | triality a ha iso => exact caseII_triality_of_source h ih ha iso
  | reeF4 m hm iso => exact caseII_reeF4_of_source h ih hm iso
  | f4 a ha iso => exact caseII_f4_of_source h ih iso
  | e6 a ha iso => exact caseII_e6_of_source h ih iso
  | e7 a ha iso => exact caseII_e7_of_source h ih iso
  | e8 a ha iso => exact caseII_e8_of_source h ih iso
  | twistedE6 a ha iso => exact caseII_twisted_e6_of_source h ih iso
  | smallDerived model => exact caseII_smallDerived_of_source h ih model
end CFSG.Quasithin.ChapterA.Section02.EvenLie
