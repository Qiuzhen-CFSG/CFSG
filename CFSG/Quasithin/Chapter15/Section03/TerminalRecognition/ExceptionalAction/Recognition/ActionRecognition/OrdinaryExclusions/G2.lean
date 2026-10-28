module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Reduction
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.Actor
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.NaturalSection
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.Classification
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation

/-!
# Exclusion of the marked terminal G₂ branch

The complete FF alternatives identify a natural central section of the
offender action. The marked source seed has trivial intersection with its
Y_F-fixed kernel, so all four dimensions survive, including in a nonsplit
extension. The actual O₂(image Y_F), restricted to the offender actor,
therefore fixes at least four dimensions on this section.

Under its actual action equivalence with the full or derived binary G₂
natural action, the same marked core fixes at most two dimensions. This
contradiction excludes the G₂(2) full quotient without an additional action,
splitting or fixed-space premise.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, final
proof of 15.3.1, printed p.1155; B.5.1 and B.5.6, printed pp.99 and 105.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The G₂(2) branch in the final paragraph of 15.3.1 is incompatible with
the complete FF alternatives and the actual marked source configuration. -/
theorem not_g2 (h : SourceAlternative d.offenderAction)
    (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) : False := by
  obtain ⟨c⟩ := G2.exists_naturalSection d h e
  rcases c.natural with hfull | hderived
  · obtain ⟨f⟩ := hfull
    exact (Nat.not_lt_of_ge
      (c.model_firstCore_fixed_finrank_ge_four d (g2Natural (ZMod 2)) f))
      (G2.LocalCalculation.full_fixed_finrank_lt_four d e f.groupEquiv)
  · obtain ⟨f⟩ := hderived
    exact (Nat.not_lt_of_ge
      (c.model_firstCore_fixed_finrank_ge_four d (g2DerivedNatural (ZMod 2)) f))
      (G2.LocalCalculation.derived_fixed_finrank_lt_four d e f.groupEquiv)

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions
