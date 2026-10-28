module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.LocalActions.Action
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.LocalActions.Radical
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.LocalActions.Offender

/-!
# Local representation data for the noncentral fixed-space argument

The exact earlier identities L=[L,J(R)] and R=O₂(LR)O₂(Y_L) construct a
radical element lifting a nonidentity quotient involution. The actual residual
action commutes with the component action, so the moving-layer descriptions
give both centralizer-action alternatives, with the fixed-subgroup assertion
proved independently of full displacement. These constructions do not require
normalization of L by S or exclusion of the six-chief-factor case.

The maximum-elementary offender argument proves the FF property of the precise
component representation from these same earlier local identities. Thus
`local_actions` discharges the FF premise of `local_actions_of_FF` and supplies
all the representation data required by the parent's noncentrality calculation.
`SourceData` retains all five full C.1.34 alternatives; the offender argument
works before choosing among them. The natural coordinates, natural quotient,
exact fixed kernel, and nonsplit fixed-line description remain in the output.

Source: Aschbacher–Smith, 15.3.16(2), p.1126; 15.3.23, p.1128;
C.1.34, pp.136–137; B.4.8, pp.91–92 (1 March 2004 manuscript).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions
variable {G : Type*} [Group G] [Finite G]

/-- Construct the quotient, radical involution, and actual centralizer action
from a faithful FF component action. The source FF assertion remains explicit. -/
theorem local_actions_of_FF (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    [(actionKernel d c.L).Normal] [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (hN : overgroup d c.L ≤ normalizer (d.componentSpan c.L : Set G))
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hcoreR : c.L.pCoreIn 2 ≤ d.R)
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hJR : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hfactor : d.R = (c.L ⊔ d.R).pCoreIn 2 ⊔ (YL d c.L).pCoreIn 2)
    (hFF : IsFFModule (componentRepresentation d c.L hN
      (core_centralizes_span d c.L hcoreR (hR.le.trans inf_le_right)) e)) :
    MovingStructure (componentRepresentation d c.L hN
      (core_centralizes_span d c.L hcoreR (hR.le.trans inf_le_right)) e) ∧
    (∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Nonempty (ModuleQuotient
      (moving (componentRepresentation d c.L hN
        (core_centralizes_span d c.L hcoreR (hR.le.trans inf_le_right)) e)).toRepresentation m)) ∧
    (∃ l : c.L, (l : G) ∈ d.R ∧ e (QuotientGroup.mk l) ^ 2 = 1 ∧
      e (QuotientGroup.mk l) ≠ 1) ∧
    CentralizerActionCases d c.L hN
      (core_centralizes_span d c.L hcoreR (hR.le.trans inf_le_right)) e := by
  have hs := movingStructure_of_FF _
    (componentRepresentation_injective d c.L hN _ e c.outside hC) hFF
  exact ⟨hs, hs.quotient, radical_involution d c.L c.outside hC hR hcoreR hJR hfactor e,
    centralizerActionCases_of_movingStructure d c.L hN _ e hs⟩

/-- Construct all local representation data from the earlier radical identities.
The FF property is proved for the actual marked component action, so no
moving-layer classification, chief-case exclusion, or S-normalization is an input. -/
theorem local_actions (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    [(actionKernel d c.L).Normal] [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (hN : overgroup d c.L ≤ normalizer (d.componentSpan c.L : Set G))
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hcoreR : c.L.pCoreIn 2 ≤ d.R)
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hJR : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hfactor : d.R = (c.L ⊔ d.R).pCoreIn 2 ⊔ (YL d c.L).pCoreIn 2) :
    MovingStructure (componentRepresentation d c.L hN
      (core_centralizes_span d c.L hcoreR (hR.le.trans inf_le_right)) e) ∧
    (∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Nonempty (ModuleQuotient
      (moving (componentRepresentation d c.L hN
        (core_centralizes_span d c.L hcoreR (hR.le.trans inf_le_right)) e)).toRepresentation m)) ∧
    (∃ l : c.L, (l : G) ∈ d.R ∧ e (QuotientGroup.mk l) ^ 2 = 1 ∧
      e (QuotientGroup.mk l) ≠ 1) ∧
    CentralizerActionCases d c.L hN
      (core_centralizes_span d c.L hcoreR (hR.le.trans inf_le_right)) e := by
  exact local_actions_of_FF d c hN e hR hcoreR hC hJR hfactor
    (componentRepresentation_isFFModule d c.L hN e hR hcoreR c.outside hC hJR hfactor)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension.LocalActions
