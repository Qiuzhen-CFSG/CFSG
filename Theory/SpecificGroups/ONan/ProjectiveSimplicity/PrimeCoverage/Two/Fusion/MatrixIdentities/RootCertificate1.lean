module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Fusion.MatrixIdentities.RootData1

/-!
# Product obligations for the O'Nan root power witnesses

The fields below are explicit matrix equalities, all still requiring proof.
The reduction theorem establishes the odd power by repeated squaring, so a
consumer needs only check individual products against the displayed witnesses.
Data source and ATLAS attribution are recorded in `ConjugateData.lean`.
-/

namespace ONan.Simplicity.TwoCertificate.Fusion.RootData

/-- Products sufficient for the power at root 1. -/
public structure RootProducts1 : Prop where
  base : FusionData.form4 * matrixA = r1p1
  step2 : r1p1 * r1p1 = r1p2
  step4 : r1p2 * r1p2 = r1p4
  step8 : r1p4 * r1p4 = r1p8
  step16 : r1p8 * r1p8 = r1p16
  step18 : r1p16 * r1p2 = r1p18
  step19 : r1p18 * r1p1 = 1

public theorem root_power_1 (h : RootProducts1) : (FusionData.form4 * matrixA) ^ 19 = 1 := by
  rw [h.base]
  have h2 : r1p1 ^ 2 = r1p2 := by
    simpa only [pow_two] using h.step2
  have h4 : r1p1 ^ 4 = r1p4 := by
    calc
      r1p1 ^ 4 = r1p1 ^ 2 * r1p1 ^ 2 := pow_add _ 2 2
      _ = _ := by rw [h2, h.step4]
  have h8 : r1p1 ^ 8 = r1p8 := by
    calc
      r1p1 ^ 8 = r1p1 ^ 4 * r1p1 ^ 4 := pow_add _ 4 4
      _ = _ := by rw [h4, h.step8]
  have h16 : r1p1 ^ 16 = r1p16 := by
    calc
      r1p1 ^ 16 = r1p1 ^ 8 * r1p1 ^ 8 := pow_add _ 8 8
      _ = _ := by rw [h8, h.step16]
  have h18 : r1p1 ^ 18 = r1p18 := by
    calc
      r1p1 ^ 18 = r1p1 ^ 16 * r1p1 ^ 2 := pow_add _ 16 2
      _ = _ := by rw [h16, h2, h.step18]
  calc
    r1p1 ^ 19 = r1p1 ^ 18 * r1p1 := pow_succ _ 18
    _ = 1 := by rw [h18, h.step19]

end ONan.Simplicity.TwoCertificate.Fusion.RootData
