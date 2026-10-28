module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.PoolData
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Outputs
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Prefix
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R00
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R01
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R02
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R03
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R04
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R05
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R06
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric.Ranges.R07

/-!
# Complete numeric checks for the G₂(3) cyclic certificate

The complete retained trace is represented by `definitionCode`, `facts`, and
`instructions`. `outputs` establishes its three numeric endpoints, and
`checked` certifies every instruction below the published `traceLength`.
The proof joins the checked prefix and eight adjacent ranges, including the
short final block, using the original `Pooled.check` on the complete tables.
This discharges the numeric-check premise of `Certificates.checkedTrace_of_numeric`;
the separate word-pool validity remains with the certificate assembly owner.

Source: ATLAS G23G1-P1 and G23G1-max3W1; see `Numeric/source/README.md`.
-/

namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric

/-- Every retained instruction passes the original pooled numeric checker. -/
public theorem checked : ∀ n, n < traceLength →
    Pooled.check (pool (fun _ => [])) definitionCode facts n (instructions n) (facts n) = true := by
  have h : Checked 0 1718562 :=
    checkedPrefix.append
      (((Ranges.R00.checkedRange.append Ranges.R01.checkedRange).append
          (Ranges.R02.checkedRange.append Ranges.R03.checkedRange)).append
        ((Ranges.R04.checkedRange.append Ranges.R05.checkedRange).append
          (Ranges.R06.checkedRange.append Ranges.R07.checkedRange)))
  intro n hn
  exact h n (Nat.zero_le n) hn

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Numeric
