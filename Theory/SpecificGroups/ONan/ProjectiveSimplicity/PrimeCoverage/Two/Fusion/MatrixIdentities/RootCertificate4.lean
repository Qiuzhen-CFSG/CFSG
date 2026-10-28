module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootData4

/-!
# Product obligations for the O'Nan root power witnesses

The fields below are explicit matrix equalities, all still requiring proof.
The reduction theorem establishes the odd power by repeated squaring, so a
consumer needs only check individual products against the displayed witnesses.
Data source and ATLAS attribution are recorded in `ConjugateData.lean`.
-/

namespace ONan.Simplicity.TwoCertificate.Fusion.RootData

/-- Products sufficient for the power at root 4. -/
public structure RootProducts4 : Prop where
  base : FusionData.form56 * c = r4p1
  step2 : r4p1 * r4p1 = r4p2
  step4 : r4p2 * r4p2 = r4p4
  step8 : r4p4 * r4p4 = r4p8
  step12 : r4p8 * r4p4 = r4p12
  step14 : r4p12 * r4p2 = r4p14
  step15 : r4p14 * r4p1 = 1

public theorem root_power_4 (h : RootProducts4) : (FusionData.form56 * c) ^ 15 = 1 := by
  rw [h.base]
  have h2 : r4p1 ^ 2 = r4p2 := by
    simpa only [pow_two] using h.step2
  have h4 : r4p1 ^ 4 = r4p4 := by
    calc
      r4p1 ^ 4 = r4p1 ^ 2 * r4p1 ^ 2 := pow_add _ 2 2
      _ = _ := by rw [h2, h.step4]
  have h8 : r4p1 ^ 8 = r4p8 := by
    calc
      r4p1 ^ 8 = r4p1 ^ 4 * r4p1 ^ 4 := pow_add _ 4 4
      _ = _ := by rw [h4, h.step8]
  have h12 : r4p1 ^ 12 = r4p12 := by
    calc
      r4p1 ^ 12 = r4p1 ^ 8 * r4p1 ^ 4 := pow_add _ 8 4
      _ = _ := by rw [h8, h4, h.step12]
  have h14 : r4p1 ^ 14 = r4p14 := by
    calc
      r4p1 ^ 14 = r4p1 ^ 12 * r4p1 ^ 2 := pow_add _ 12 2
      _ = _ := by rw [h12, h2, h.step14]
  calc
    r4p1 ^ 15 = r4p1 ^ 14 * r4p1 := pow_succ _ 14
    _ = 1 := by rw [h14, h.step15]

end ONan.Simplicity.TwoCertificate.Fusion.RootData
