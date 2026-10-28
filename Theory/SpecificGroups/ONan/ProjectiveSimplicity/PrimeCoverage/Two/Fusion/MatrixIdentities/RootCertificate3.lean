module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootData3

/-!
# Product obligations for the O'Nan root power witnesses

The fields below are explicit matrix equalities, all still requiring proof.
The reduction theorem establishes the odd power by repeated squaring, so a
consumer needs only check individual products against the displayed witnesses.
Data source and ATLAS attribution are recorded in `ConjugateData.lean`.
-/

namespace ONan.Simplicity.TwoCertificate.Fusion.RootData

/-- Products sufficient for the power at root 3. -/
public structure RootProducts3 : Prop where
  base : FusionData.form8 * f = r3p1
  step2 : r3p1 * r3p1 = r3p2
  step4 : r3p2 * r3p2 = r3p4
  step8 : r3p4 * r3p4 = r3p8
  step16 : r3p8 * r3p8 = r3p16
  step18 : r3p16 * r3p2 = r3p18
  step19 : r3p18 * r3p1 = 1

public theorem root_power_3 (h : RootProducts3) : (FusionData.form8 * f) ^ 19 = 1 := by
  rw [h.base]
  have h2 : r3p1 ^ 2 = r3p2 := by
    simpa only [pow_two] using h.step2
  have h4 : r3p1 ^ 4 = r3p4 := by
    calc
      r3p1 ^ 4 = r3p1 ^ 2 * r3p1 ^ 2 := pow_add _ 2 2
      _ = _ := by rw [h2, h.step4]
  have h8 : r3p1 ^ 8 = r3p8 := by
    calc
      r3p1 ^ 8 = r3p1 ^ 4 * r3p1 ^ 4 := pow_add _ 4 4
      _ = _ := by rw [h4, h.step8]
  have h16 : r3p1 ^ 16 = r3p16 := by
    calc
      r3p1 ^ 16 = r3p1 ^ 8 * r3p1 ^ 8 := pow_add _ 8 8
      _ = _ := by rw [h8, h.step16]
  have h18 : r3p1 ^ 18 = r3p18 := by
    calc
      r3p1 ^ 18 = r3p1 ^ 16 * r3p1 ^ 2 := pow_add _ 16 2
      _ = _ := by rw [h16, h2, h.step18]
  calc
    r3p1 ^ 19 = r3p1 ^ 18 * r3p1 := pow_succ _ 18
    _ = 1 := by rw [h18, h.step19]

end ONan.Simplicity.TwoCertificate.Fusion.RootData
