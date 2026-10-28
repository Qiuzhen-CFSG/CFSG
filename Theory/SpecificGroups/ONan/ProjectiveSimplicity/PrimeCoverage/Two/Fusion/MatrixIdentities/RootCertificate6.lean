module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootData6

/-!
# Product obligations for the O'Nan root power witnesses

The fields below are explicit matrix equalities, all still requiring proof.
The reduction theorem establishes the odd power by repeated squaring, so a
consumer needs only check individual products against the displayed witnesses.
Data source and ATLAS attribution are recorded in `ConjugateData.lean`.
-/

namespace ONan.Simplicity.TwoCertificate.Fusion.RootData

/-- Products sufficient for the power at root 6. -/
public structure RootProducts6 : Prop where
  base : FusionData.form448 * d = r6p1
  step2 : r6p1 * r6p1 = r6p2
  step4 : r6p2 * r6p2 = r6p4
  step8 : r6p4 * r6p4 = r6p8
  step10 : r6p8 * r6p2 = r6p10
  step11 : r6p10 * r6p1 = 1

public theorem root_power_6 (h : RootProducts6) : (FusionData.form448 * d) ^ 11 = 1 := by
  rw [h.base]
  have h2 : r6p1 ^ 2 = r6p2 := by
    simpa only [pow_two] using h.step2
  have h4 : r6p1 ^ 4 = r6p4 := by
    calc
      r6p1 ^ 4 = r6p1 ^ 2 * r6p1 ^ 2 := pow_add _ 2 2
      _ = _ := by rw [h2, h.step4]
  have h8 : r6p1 ^ 8 = r6p8 := by
    calc
      r6p1 ^ 8 = r6p1 ^ 4 * r6p1 ^ 4 := pow_add _ 4 4
      _ = _ := by rw [h4, h.step8]
  have h10 : r6p1 ^ 10 = r6p10 := by
    calc
      r6p1 ^ 10 = r6p1 ^ 8 * r6p1 ^ 2 := pow_add _ 8 2
      _ = _ := by rw [h8, h2, h.step10]
  calc
    r6p1 ^ 11 = r6p1 ^ 10 * r6p1 := pow_succ _ 10
    _ = 1 := by rw [h10, h.step11]

end ONan.Simplicity.TwoCertificate.Fusion.RootData
