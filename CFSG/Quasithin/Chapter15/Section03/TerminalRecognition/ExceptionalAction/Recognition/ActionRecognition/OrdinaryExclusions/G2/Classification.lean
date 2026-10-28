module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.Actor
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.NaturalSection
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.Classification.Alternatives
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.Classification.Actions

/-!
# The natural central section in the terminal G₂ case

The complete source alternatives force the quasisimple case. The actual
Fitting subgroup is the preimage of G₂(2)′ and contains the marked first
local factor. Comparing every B.5.1 action case with its order selects
the binary G₂ natural action on the original moved section modulo its
actual fixed kernel. This retains every permitted fixed summand and
requires no splitting of the original representation.

Source: Aschbacher–Smith, B.5.1 and B.5.6, printed pp.99 and 105, used in
the final proof of 15.3.1, printed p.1155 (1 March 2004 manuscript).
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- Specialization of the complete FF alternatives to the actual terminal
G₂ quotient, with no action-identification or splitting premise. -/
theorem exists_naturalSection (h : SourceAlternative d.offenderAction)
    (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) :
    Nonempty (NaturalSection d) := by
  obtain ⟨c⟩ := Classification.quasisimple_source d e h
  exact ⟨{
    sectionData := c.sectionData
    first_le := Classification.first_le_fitting d e
    natural := Or.inl (Classification.section_natural d.offenderAction
      (Classification.actor_card_le d e) (Classification.fitting_card d e) c.clause_one)
  }⟩

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2
