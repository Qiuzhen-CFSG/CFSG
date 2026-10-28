module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps
import Mathlib.Tactic.FinCases

/-!
# Rudvalis dense transition 65

Certify row 65 of `FactorWords.row` on all 4060 points using 203 slices
of twenty points and the certified factor cache. The representative words
come from `OrderLevel0Data`, as decoded in the saved Batch13.lean witness
`point13_1_6`; their decoding is checked below in the kernel.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense2.Row65
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000

private theorem repWord : L0RepWord (FactorWords.row 65).2 = [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] := by
  decide +kernel

private theorem targetWord :
    L0RepWord (L0Act ((FactorWords.row 65).1.castLE (by decide))
      (FactorWords.row 65).2) = [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] := by
  decide +kernel

private theorem slice0 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 0 = true := by
  decide +kernel

private theorem slice1 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 1 = true := by
  decide +kernel

private theorem slice2 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 2 = true := by
  decide +kernel

private theorem slice3 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 3 = true := by
  decide +kernel

private theorem slice4 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 4 = true := by
  decide +kernel

private theorem slice5 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 5 = true := by
  decide +kernel

private theorem slice6 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 6 = true := by
  decide +kernel

private theorem slice7 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 7 = true := by
  decide +kernel

private theorem slice8 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 8 = true := by
  decide +kernel

private theorem slice9 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 9 = true := by
  decide +kernel

private theorem slice10 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 10 = true := by
  decide +kernel

private theorem slice11 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 11 = true := by
  decide +kernel

private theorem slice12 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 12 = true := by
  decide +kernel

private theorem slice13 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 13 = true := by
  decide +kernel

private theorem slice14 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 14 = true := by
  decide +kernel

private theorem slice15 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 15 = true := by
  decide +kernel

private theorem slice16 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 16 = true := by
  decide +kernel

private theorem slice17 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 17 = true := by
  decide +kernel

private theorem slice18 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 18 = true := by
  decide +kernel

private theorem slice19 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 19 = true := by
  decide +kernel

private theorem slice20 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 20 = true := by
  decide +kernel

private theorem slice21 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 21 = true := by
  decide +kernel

private theorem slice22 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 22 = true := by
  decide +kernel

private theorem slice23 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 23 = true := by
  decide +kernel

private theorem slice24 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 24 = true := by
  decide +kernel

private theorem slice25 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 25 = true := by
  decide +kernel

private theorem slice26 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 26 = true := by
  decide +kernel

private theorem slice27 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 27 = true := by
  decide +kernel

private theorem slice28 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 28 = true := by
  decide +kernel

private theorem slice29 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 29 = true := by
  decide +kernel

private theorem slice30 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 30 = true := by
  decide +kernel

private theorem slice31 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 31 = true := by
  decide +kernel

private theorem slice32 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 32 = true := by
  decide +kernel

private theorem slice33 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 33 = true := by
  decide +kernel

private theorem slice34 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 34 = true := by
  decide +kernel

private theorem slice35 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 35 = true := by
  decide +kernel

private theorem slice36 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 36 = true := by
  decide +kernel

private theorem slice37 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 37 = true := by
  decide +kernel

private theorem slice38 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 38 = true := by
  decide +kernel

private theorem slice39 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 39 = true := by
  decide +kernel

private theorem slice40 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 40 = true := by
  decide +kernel

private theorem slice41 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 41 = true := by
  decide +kernel

private theorem slice42 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 42 = true := by
  decide +kernel

private theorem slice43 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 43 = true := by
  decide +kernel

private theorem slice44 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 44 = true := by
  decide +kernel

private theorem slice45 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 45 = true := by
  decide +kernel

private theorem slice46 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 46 = true := by
  decide +kernel

private theorem slice47 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 47 = true := by
  decide +kernel

private theorem slice48 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 48 = true := by
  decide +kernel

private theorem slice49 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 49 = true := by
  decide +kernel

private theorem slice50 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 50 = true := by
  decide +kernel

private theorem slice51 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 51 = true := by
  decide +kernel

private theorem slice52 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 52 = true := by
  decide +kernel

private theorem slice53 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 53 = true := by
  decide +kernel

private theorem slice54 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 54 = true := by
  decide +kernel

private theorem slice55 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 55 = true := by
  decide +kernel

private theorem slice56 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 56 = true := by
  decide +kernel

private theorem slice57 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 57 = true := by
  decide +kernel

private theorem slice58 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 58 = true := by
  decide +kernel

private theorem slice59 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 59 = true := by
  decide +kernel

private theorem slice60 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 60 = true := by
  decide +kernel

private theorem slice61 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 61 = true := by
  decide +kernel

private theorem slice62 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 62 = true := by
  decide +kernel

private theorem slice63 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 63 = true := by
  decide +kernel

private theorem slice64 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 64 = true := by
  decide +kernel

private theorem slice65 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 65 = true := by
  decide +kernel

private theorem slice66 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 66 = true := by
  decide +kernel

private theorem slice67 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 67 = true := by
  decide +kernel

private theorem slice68 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 68 = true := by
  decide +kernel

private theorem slice69 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 69 = true := by
  decide +kernel

private theorem slice70 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 70 = true := by
  decide +kernel

private theorem slice71 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 71 = true := by
  decide +kernel

private theorem slice72 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 72 = true := by
  decide +kernel

private theorem slice73 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 73 = true := by
  decide +kernel

private theorem slice74 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 74 = true := by
  decide +kernel

private theorem slice75 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 75 = true := by
  decide +kernel

private theorem slice76 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 76 = true := by
  decide +kernel

private theorem slice77 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 77 = true := by
  decide +kernel

private theorem slice78 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 78 = true := by
  decide +kernel

private theorem slice79 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 79 = true := by
  decide +kernel

private theorem slice80 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 80 = true := by
  decide +kernel

private theorem slice81 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 81 = true := by
  decide +kernel

private theorem slice82 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 82 = true := by
  decide +kernel

private theorem slice83 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 83 = true := by
  decide +kernel

private theorem slice84 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 84 = true := by
  decide +kernel

private theorem slice85 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 85 = true := by
  decide +kernel

private theorem slice86 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 86 = true := by
  decide +kernel

private theorem slice87 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 87 = true := by
  decide +kernel

private theorem slice88 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 88 = true := by
  decide +kernel

private theorem slice89 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 89 = true := by
  decide +kernel

private theorem slice90 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 90 = true := by
  decide +kernel

private theorem slice91 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 91 = true := by
  decide +kernel

private theorem slice92 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 92 = true := by
  decide +kernel

private theorem slice93 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 93 = true := by
  decide +kernel

private theorem slice94 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 94 = true := by
  decide +kernel

private theorem slice95 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 95 = true := by
  decide +kernel

private theorem slice96 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 96 = true := by
  decide +kernel

private theorem slice97 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 97 = true := by
  decide +kernel

private theorem slice98 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 98 = true := by
  decide +kernel

private theorem slice99 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 99 = true := by
  decide +kernel

private theorem slice100 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 100 = true := by
  decide +kernel

private theorem slice101 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 101 = true := by
  decide +kernel

private theorem slice102 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 102 = true := by
  decide +kernel

private theorem slice103 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 103 = true := by
  decide +kernel

private theorem slice104 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 104 = true := by
  decide +kernel

private theorem slice105 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 105 = true := by
  decide +kernel

private theorem slice106 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 106 = true := by
  decide +kernel

private theorem slice107 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 107 = true := by
  decide +kernel

private theorem slice108 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 108 = true := by
  decide +kernel

private theorem slice109 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 109 = true := by
  decide +kernel

private theorem slice110 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 110 = true := by
  decide +kernel

private theorem slice111 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 111 = true := by
  decide +kernel

private theorem slice112 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 112 = true := by
  decide +kernel

private theorem slice113 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 113 = true := by
  decide +kernel

private theorem slice114 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 114 = true := by
  decide +kernel

private theorem slice115 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 115 = true := by
  decide +kernel

private theorem slice116 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 116 = true := by
  decide +kernel

private theorem slice117 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 117 = true := by
  decide +kernel

private theorem slice118 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 118 = true := by
  decide +kernel

private theorem slice119 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 119 = true := by
  decide +kernel

private theorem slice120 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 120 = true := by
  decide +kernel

private theorem slice121 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 121 = true := by
  decide +kernel

private theorem slice122 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 122 = true := by
  decide +kernel

private theorem slice123 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 123 = true := by
  decide +kernel

private theorem slice124 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 124 = true := by
  decide +kernel

private theorem slice125 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 125 = true := by
  decide +kernel

private theorem slice126 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 126 = true := by
  decide +kernel

private theorem slice127 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 127 = true := by
  decide +kernel

private theorem slice128 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 128 = true := by
  decide +kernel

private theorem slice129 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 129 = true := by
  decide +kernel

private theorem slice130 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 130 = true := by
  decide +kernel

private theorem slice131 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 131 = true := by
  decide +kernel

private theorem slice132 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 132 = true := by
  decide +kernel

private theorem slice133 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 133 = true := by
  decide +kernel

private theorem slice134 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 134 = true := by
  decide +kernel

private theorem slice135 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 135 = true := by
  decide +kernel

private theorem slice136 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 136 = true := by
  decide +kernel

private theorem slice137 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 137 = true := by
  decide +kernel

private theorem slice138 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 138 = true := by
  decide +kernel

private theorem slice139 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 139 = true := by
  decide +kernel

private theorem slice140 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 140 = true := by
  decide +kernel

private theorem slice141 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 141 = true := by
  decide +kernel

private theorem slice142 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 142 = true := by
  decide +kernel

private theorem slice143 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 143 = true := by
  decide +kernel

private theorem slice144 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 144 = true := by
  decide +kernel

private theorem slice145 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 145 = true := by
  decide +kernel

private theorem slice146 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 146 = true := by
  decide +kernel

private theorem slice147 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 147 = true := by
  decide +kernel

private theorem slice148 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 148 = true := by
  decide +kernel

private theorem slice149 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 149 = true := by
  decide +kernel

private theorem slice150 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 150 = true := by
  decide +kernel

private theorem slice151 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 151 = true := by
  decide +kernel

private theorem slice152 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 152 = true := by
  decide +kernel

private theorem slice153 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 153 = true := by
  decide +kernel

private theorem slice154 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 154 = true := by
  decide +kernel

private theorem slice155 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 155 = true := by
  decide +kernel

private theorem slice156 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 156 = true := by
  decide +kernel

private theorem slice157 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 157 = true := by
  decide +kernel

private theorem slice158 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 158 = true := by
  decide +kernel

private theorem slice159 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 159 = true := by
  decide +kernel

private theorem slice160 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 160 = true := by
  decide +kernel

private theorem slice161 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 161 = true := by
  decide +kernel

private theorem slice162 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 162 = true := by
  decide +kernel

private theorem slice163 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 163 = true := by
  decide +kernel

private theorem slice164 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 164 = true := by
  decide +kernel

private theorem slice165 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 165 = true := by
  decide +kernel

private theorem slice166 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 166 = true := by
  decide +kernel

private theorem slice167 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 167 = true := by
  decide +kernel

private theorem slice168 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 168 = true := by
  decide +kernel

private theorem slice169 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 169 = true := by
  decide +kernel

private theorem slice170 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 170 = true := by
  decide +kernel

private theorem slice171 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 171 = true := by
  decide +kernel

private theorem slice172 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 172 = true := by
  decide +kernel

private theorem slice173 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 173 = true := by
  decide +kernel

private theorem slice174 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 174 = true := by
  decide +kernel

private theorem slice175 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 175 = true := by
  decide +kernel

private theorem slice176 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 176 = true := by
  decide +kernel

private theorem slice177 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 177 = true := by
  decide +kernel

private theorem slice178 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 178 = true := by
  decide +kernel

private theorem slice179 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 179 = true := by
  decide +kernel

private theorem slice180 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 180 = true := by
  decide +kernel

private theorem slice181 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 181 = true := by
  decide +kernel

private theorem slice182 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 182 = true := by
  decide +kernel

private theorem slice183 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 183 = true := by
  decide +kernel

private theorem slice184 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 184 = true := by
  decide +kernel

private theorem slice185 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 185 = true := by
  decide +kernel

private theorem slice186 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 186 = true := by
  decide +kernel

private theorem slice187 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 187 = true := by
  decide +kernel

private theorem slice188 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 188 = true := by
  decide +kernel

private theorem slice189 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 189 = true := by
  decide +kernel

private theorem slice190 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 190 = true := by
  decide +kernel

private theorem slice191 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 191 = true := by
  decide +kernel

private theorem slice192 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 192 = true := by
  decide +kernel

private theorem slice193 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 193 = true := by
  decide +kernel

private theorem slice194 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 194 = true := by
  decide +kernel

private theorem slice195 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 195 = true := by
  decide +kernel

private theorem slice196 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 196 = true := by
  decide +kernel

private theorem slice197 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 197 = true := by
  decide +kernel

private theorem slice198 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 198 = true := by
  decide +kernel

private theorem slice199 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 199 = true := by
  decide +kernel

private theorem slice200 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 200 = true := by
  decide +kernel

private theorem slice201 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 201 = true := by
  decide +kernel

private theorem slice202 : FactorMaps.slice 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] 202 = true := by
  decide +kernel

/-- The cached checks certify the original transition on the whole domain. -/
public theorem checked : stepCheck (FactorWords.row 65).1 (FactorWords.row 65).2 := by
  apply FactorMaps.ofSlices 65 [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1] [3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 3, 0, 3] repWord targetWord
  intro b
  fin_cases b
  · exact slice0
  · exact slice1
  · exact slice2
  · exact slice3
  · exact slice4
  · exact slice5
  · exact slice6
  · exact slice7
  · exact slice8
  · exact slice9
  · exact slice10
  · exact slice11
  · exact slice12
  · exact slice13
  · exact slice14
  · exact slice15
  · exact slice16
  · exact slice17
  · exact slice18
  · exact slice19
  · exact slice20
  · exact slice21
  · exact slice22
  · exact slice23
  · exact slice24
  · exact slice25
  · exact slice26
  · exact slice27
  · exact slice28
  · exact slice29
  · exact slice30
  · exact slice31
  · exact slice32
  · exact slice33
  · exact slice34
  · exact slice35
  · exact slice36
  · exact slice37
  · exact slice38
  · exact slice39
  · exact slice40
  · exact slice41
  · exact slice42
  · exact slice43
  · exact slice44
  · exact slice45
  · exact slice46
  · exact slice47
  · exact slice48
  · exact slice49
  · exact slice50
  · exact slice51
  · exact slice52
  · exact slice53
  · exact slice54
  · exact slice55
  · exact slice56
  · exact slice57
  · exact slice58
  · exact slice59
  · exact slice60
  · exact slice61
  · exact slice62
  · exact slice63
  · exact slice64
  · exact slice65
  · exact slice66
  · exact slice67
  · exact slice68
  · exact slice69
  · exact slice70
  · exact slice71
  · exact slice72
  · exact slice73
  · exact slice74
  · exact slice75
  · exact slice76
  · exact slice77
  · exact slice78
  · exact slice79
  · exact slice80
  · exact slice81
  · exact slice82
  · exact slice83
  · exact slice84
  · exact slice85
  · exact slice86
  · exact slice87
  · exact slice88
  · exact slice89
  · exact slice90
  · exact slice91
  · exact slice92
  · exact slice93
  · exact slice94
  · exact slice95
  · exact slice96
  · exact slice97
  · exact slice98
  · exact slice99
  · exact slice100
  · exact slice101
  · exact slice102
  · exact slice103
  · exact slice104
  · exact slice105
  · exact slice106
  · exact slice107
  · exact slice108
  · exact slice109
  · exact slice110
  · exact slice111
  · exact slice112
  · exact slice113
  · exact slice114
  · exact slice115
  · exact slice116
  · exact slice117
  · exact slice118
  · exact slice119
  · exact slice120
  · exact slice121
  · exact slice122
  · exact slice123
  · exact slice124
  · exact slice125
  · exact slice126
  · exact slice127
  · exact slice128
  · exact slice129
  · exact slice130
  · exact slice131
  · exact slice132
  · exact slice133
  · exact slice134
  · exact slice135
  · exact slice136
  · exact slice137
  · exact slice138
  · exact slice139
  · exact slice140
  · exact slice141
  · exact slice142
  · exact slice143
  · exact slice144
  · exact slice145
  · exact slice146
  · exact slice147
  · exact slice148
  · exact slice149
  · exact slice150
  · exact slice151
  · exact slice152
  · exact slice153
  · exact slice154
  · exact slice155
  · exact slice156
  · exact slice157
  · exact slice158
  · exact slice159
  · exact slice160
  · exact slice161
  · exact slice162
  · exact slice163
  · exact slice164
  · exact slice165
  · exact slice166
  · exact slice167
  · exact slice168
  · exact slice169
  · exact slice170
  · exact slice171
  · exact slice172
  · exact slice173
  · exact slice174
  · exact slice175
  · exact slice176
  · exact slice177
  · exact slice178
  · exact slice179
  · exact slice180
  · exact slice181
  · exact slice182
  · exact slice183
  · exact slice184
  · exact slice185
  · exact slice186
  · exact slice187
  · exact slice188
  · exact slice189
  · exact slice190
  · exact slice191
  · exact slice192
  · exact slice193
  · exact slice194
  · exact slice195
  · exact slice196
  · exact slice197
  · exact slice198
  · exact slice199
  · exact slice200
  · exact slice201
  · exact slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense2.Row65
