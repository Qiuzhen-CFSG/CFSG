module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.Action

/-!
# Discharge of the original 14.3.9(2) source contract

The source theorem supplies the universally quantified Thompson-normality
input at the original LT and original invariant flag. The complete earlier
Structural1222 implication remains explicit, with producer qt-12-02; no
conclusion concerning a chosen critical path enters its construction.

Source: Aschbacher–Smith, 14.3.9(2), printed pp.992–993, used in 14.7.70.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section03.ThompsonSource
open Chapter12.Section02
open Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
universe u

/-- The genuine universal predecessor for the literal Goldschmidt consumer. -/
theorem earlierThompsonNormality
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ThompsonWitness.EarlierThompsonNormality.{u} := by
  intro X _ _ S A U _ h f hf
  exact thompson_normal h f structural hf

end CFSG.Quasithin.Chapter14.Section03.ThompsonSource
