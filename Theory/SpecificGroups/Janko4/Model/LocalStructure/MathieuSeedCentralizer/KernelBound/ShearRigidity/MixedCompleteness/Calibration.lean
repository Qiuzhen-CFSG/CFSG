module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch00
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch01
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch02
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch03
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch04
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch05
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch06
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch07
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch08
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch09
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch10
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch11
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch12
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch13
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch14
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch15
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch16
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch17
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch18
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch19
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch20
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch21
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch22
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch23
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch24
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch25
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch26
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch27
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch28
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch29
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration.Batch30

/-!
# Calibration of every original exterior generator

All 1221 original exterior forms are transported by the actual shared
adapted basis. The checked rows give all 595 selected upper entries and
the entire mixed block, in the original source ordering.

Source and reproduction: `Calibration/source/README.md`.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness

attribute [local irreducible] Calibration

/-- Both calibration clauses for every original exterior generator. -/
theorem allCalibrations (i : Fin 1221) : Calibration i := by
  by_cases h0 : i.val < 40
  · have h := CalibrationProof.Batch00.all ⟨i.val - 0, by omega⟩
    have hi : (⟨0 + (i.val - 0), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 0 + (i.val - 0) = i.val
      omega
    exact hi ▸ h
  by_cases h1 : i.val < 80
  · have h := CalibrationProof.Batch01.all ⟨i.val - 40, by omega⟩
    have hi : (⟨40 + (i.val - 40), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 40 + (i.val - 40) = i.val
      omega
    exact hi ▸ h
  by_cases h2 : i.val < 120
  · have h := CalibrationProof.Batch02.all ⟨i.val - 80, by omega⟩
    have hi : (⟨80 + (i.val - 80), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 80 + (i.val - 80) = i.val
      omega
    exact hi ▸ h
  by_cases h3 : i.val < 160
  · have h := CalibrationProof.Batch03.all ⟨i.val - 120, by omega⟩
    have hi : (⟨120 + (i.val - 120), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 120 + (i.val - 120) = i.val
      omega
    exact hi ▸ h
  by_cases h4 : i.val < 200
  · have h := CalibrationProof.Batch04.all ⟨i.val - 160, by omega⟩
    have hi : (⟨160 + (i.val - 160), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 160 + (i.val - 160) = i.val
      omega
    exact hi ▸ h
  by_cases h5 : i.val < 240
  · have h := CalibrationProof.Batch05.all ⟨i.val - 200, by omega⟩
    have hi : (⟨200 + (i.val - 200), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 200 + (i.val - 200) = i.val
      omega
    exact hi ▸ h
  by_cases h6 : i.val < 280
  · have h := CalibrationProof.Batch06.all ⟨i.val - 240, by omega⟩
    have hi : (⟨240 + (i.val - 240), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 240 + (i.val - 240) = i.val
      omega
    exact hi ▸ h
  by_cases h7 : i.val < 320
  · have h := CalibrationProof.Batch07.all ⟨i.val - 280, by omega⟩
    have hi : (⟨280 + (i.val - 280), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 280 + (i.val - 280) = i.val
      omega
    exact hi ▸ h
  by_cases h8 : i.val < 360
  · have h := CalibrationProof.Batch08.all ⟨i.val - 320, by omega⟩
    have hi : (⟨320 + (i.val - 320), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 320 + (i.val - 320) = i.val
      omega
    exact hi ▸ h
  by_cases h9 : i.val < 400
  · have h := CalibrationProof.Batch09.all ⟨i.val - 360, by omega⟩
    have hi : (⟨360 + (i.val - 360), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 360 + (i.val - 360) = i.val
      omega
    exact hi ▸ h
  by_cases h10 : i.val < 440
  · have h := CalibrationProof.Batch10.all ⟨i.val - 400, by omega⟩
    have hi : (⟨400 + (i.val - 400), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 400 + (i.val - 400) = i.val
      omega
    exact hi ▸ h
  by_cases h11 : i.val < 480
  · have h := CalibrationProof.Batch11.all ⟨i.val - 440, by omega⟩
    have hi : (⟨440 + (i.val - 440), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 440 + (i.val - 440) = i.val
      omega
    exact hi ▸ h
  by_cases h12 : i.val < 520
  · have h := CalibrationProof.Batch12.all ⟨i.val - 480, by omega⟩
    have hi : (⟨480 + (i.val - 480), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 480 + (i.val - 480) = i.val
      omega
    exact hi ▸ h
  by_cases h13 : i.val < 560
  · have h := CalibrationProof.Batch13.all ⟨i.val - 520, by omega⟩
    have hi : (⟨520 + (i.val - 520), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 520 + (i.val - 520) = i.val
      omega
    exact hi ▸ h
  by_cases h14 : i.val < 600
  · have h := CalibrationProof.Batch14.all ⟨i.val - 560, by omega⟩
    have hi : (⟨560 + (i.val - 560), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 560 + (i.val - 560) = i.val
      omega
    exact hi ▸ h
  by_cases h15 : i.val < 640
  · have h := CalibrationProof.Batch15.all ⟨i.val - 600, by omega⟩
    have hi : (⟨600 + (i.val - 600), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 600 + (i.val - 600) = i.val
      omega
    exact hi ▸ h
  by_cases h16 : i.val < 680
  · have h := CalibrationProof.Batch16.all ⟨i.val - 640, by omega⟩
    have hi : (⟨640 + (i.val - 640), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 640 + (i.val - 640) = i.val
      omega
    exact hi ▸ h
  by_cases h17 : i.val < 720
  · have h := CalibrationProof.Batch17.all ⟨i.val - 680, by omega⟩
    have hi : (⟨680 + (i.val - 680), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 680 + (i.val - 680) = i.val
      omega
    exact hi ▸ h
  by_cases h18 : i.val < 760
  · have h := CalibrationProof.Batch18.all ⟨i.val - 720, by omega⟩
    have hi : (⟨720 + (i.val - 720), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 720 + (i.val - 720) = i.val
      omega
    exact hi ▸ h
  by_cases h19 : i.val < 800
  · have h := CalibrationProof.Batch19.all ⟨i.val - 760, by omega⟩
    have hi : (⟨760 + (i.val - 760), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 760 + (i.val - 760) = i.val
      omega
    exact hi ▸ h
  by_cases h20 : i.val < 840
  · have h := CalibrationProof.Batch20.all ⟨i.val - 800, by omega⟩
    have hi : (⟨800 + (i.val - 800), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 800 + (i.val - 800) = i.val
      omega
    exact hi ▸ h
  by_cases h21 : i.val < 880
  · have h := CalibrationProof.Batch21.all ⟨i.val - 840, by omega⟩
    have hi : (⟨840 + (i.val - 840), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 840 + (i.val - 840) = i.val
      omega
    exact hi ▸ h
  by_cases h22 : i.val < 920
  · have h := CalibrationProof.Batch22.all ⟨i.val - 880, by omega⟩
    have hi : (⟨880 + (i.val - 880), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 880 + (i.val - 880) = i.val
      omega
    exact hi ▸ h
  by_cases h23 : i.val < 960
  · have h := CalibrationProof.Batch23.all ⟨i.val - 920, by omega⟩
    have hi : (⟨920 + (i.val - 920), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 920 + (i.val - 920) = i.val
      omega
    exact hi ▸ h
  by_cases h24 : i.val < 1000
  · have h := CalibrationProof.Batch24.all ⟨i.val - 960, by omega⟩
    have hi : (⟨960 + (i.val - 960), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 960 + (i.val - 960) = i.val
      omega
    exact hi ▸ h
  by_cases h25 : i.val < 1040
  · have h := CalibrationProof.Batch25.all ⟨i.val - 1000, by omega⟩
    have hi : (⟨1000 + (i.val - 1000), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 1000 + (i.val - 1000) = i.val
      omega
    exact hi ▸ h
  by_cases h26 : i.val < 1080
  · have h := CalibrationProof.Batch26.all ⟨i.val - 1040, by omega⟩
    have hi : (⟨1040 + (i.val - 1040), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 1040 + (i.val - 1040) = i.val
      omega
    exact hi ▸ h
  by_cases h27 : i.val < 1120
  · have h := CalibrationProof.Batch27.all ⟨i.val - 1080, by omega⟩
    have hi : (⟨1080 + (i.val - 1080), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 1080 + (i.val - 1080) = i.val
      omega
    exact hi ▸ h
  by_cases h28 : i.val < 1160
  · have h := CalibrationProof.Batch28.all ⟨i.val - 1120, by omega⟩
    have hi : (⟨1120 + (i.val - 1120), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 1120 + (i.val - 1120) = i.val
      omega
    exact hi ▸ h
  by_cases h29 : i.val < 1200
  · have h := CalibrationProof.Batch29.all ⟨i.val - 1160, by omega⟩
    have hi : (⟨1160 + (i.val - 1160), by omega⟩ : Fin 1221) = i := by
      apply Fin.ext
      change 1160 + (i.val - 1160) = i.val
      omega
    exact hi ▸ h
  have h := CalibrationProof.Batch30.all ⟨i.val - 1200, by omega⟩
  have hi : (⟨1200 + (i.val - 1200), by omega⟩ : Fin 1221) = i := by
    apply Fin.ext
    change 1200 + (i.val - 1200) = i.val
    omega
  exact hi ▸ h

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness
