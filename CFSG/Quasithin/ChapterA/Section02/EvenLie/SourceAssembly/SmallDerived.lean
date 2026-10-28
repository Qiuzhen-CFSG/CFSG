module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.RankTwoSimple
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.RankTwoCovers
public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv.B2ProjectiveComparison
public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv.MatrixHom

/-!
# All literal small derived carriers in the even-Lie source dispatch

The checked nine-point projective comparison and the original seven-space
Ree matrix homomorphism identify the actual commutator of Ree(3) with PSL2(8).
This supplies its exact B/C inclusion and odd-cover exclusion. Together with
the three already literal small carriers, all constructors of the complete
known-simple small-derived input are now discharged in Cases I and II.
Source: Aschbacher--Smith A.2.18, printed p.40, and GLS3 §2.2.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G]

/-- The genuine small Ree commutator, with no projective-comparison premise remaining. -/
theorem smallRee_linear
    (iso : Nonempty (G ≃* commutator (Atlas.ReeG2.Model (ZMod 3) 0))) :
    ClassicalGroup.IsPSL G 2 (2 ^ 3) := by
  obtain ⟨e⟩ := iso
  let ep := Atlas.ReeG2.TernaryDerived.equivOfPermutationModel
    Atlas.ReeG2.TernaryDerived.b2ProjectiveEquiv
    Atlas.ReeG2.TernaryDerived.toRee Atlas.ReeG2.TernaryDerived.toRee_ne_one
  exact ⟨GaloisField 2 3, inferInstance, inferInstance,
    GaloisField.card 2 3 (by decide), ⟨e.trans ep⟩⟩

/-- Every constructor of the actual small-derived catalogue belongs to the two source lists. -/
theorem caseI_smallDerived (model : KnownSimple.IsSmallDerivedCarrier G) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) := by
  cases model with
  | symplectic iso => exact caseI_symplectic_derived iso
  | g2 iso => exact caseI_g2_derived iso
  | tits iso => exact caseI_tits iso
  | ree iso =>
    have hc : IsTheoremCModel G := .bender (.linear 3 (by decide) (smallRee_linear iso))
    exact ⟨hc.toTheoremBModel, fun _ => hc⟩

variable [Finite G] {K : GroupClass.{u}}

/-- The full small-derived Case I contradicts the original simultaneous minimum. -/
theorem not_minimalCounterexample_smallDerived [IsSimpleGroup G]
    (h : MinimalCounterexample K G) (model : KnownSimple.IsSmallDerivedCarrier G) : False := by
  obtain ⟨_, _, _, hfails⟩ := h.simple_case inferInstance
  obtain ⟨hb, hc⟩ := caseI_smallDerived model
  rcases hfails with hn | ⟨hstrong, hn⟩
  · exact hn hb
  · exact hn (hc hstrong)

/-- The full small-derived Case II follows from the actual source hypotheses alone. -/
theorem caseII_smallDerived_of_source [IsQuasisimple G]
    {S : Type u} [Group S] [Finite S] {p : ℕ}
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (model : KnownSimple.IsSmallDerivedCarrier (G ⧸ center G)) : False := by
  cases model with
  | symplectic iso => exact caseII_symplectic_derived_of_source h ih iso
  | g2 iso => exact caseII_g2_derived_of_source h ih iso
  | tits iso => exact caseII_tits h ih iso
  | ree iso => exact caseII_linear_two_of_source h ih (by decide) (smallRee_linear iso)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
