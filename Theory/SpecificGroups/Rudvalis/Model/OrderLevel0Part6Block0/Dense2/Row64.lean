module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps
import Mathlib.Tactic.FinCases

/-!
# Rudvalis dense transition 64

Certify row 64 of `FactorWords.row` on all 4060 points using 203 slices
of twenty points and the certified factor cache. The representative words
come from `OrderLevel0Data`, as decoded in the saved Batch13.lean witness
`point13_0_17`; their decoding is checked below in the kernel.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense2.Row64
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000

private theorem repWord : L0RepWord (FactorWords.row 64).2 = [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] := by
  decide +kernel

private theorem targetWord :
    L0RepWord (L0Act ((FactorWords.row 64).1.castLE (by decide))
      (FactorWords.row 64).2) = [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] := by
  decide +kernel

private theorem slice0 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 0 = true := by
  decide +kernel

private theorem slice1 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 1 = true := by
  decide +kernel

private theorem slice2 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 2 = true := by
  decide +kernel

private theorem slice3 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 3 = true := by
  decide +kernel

private theorem slice4 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 4 = true := by
  decide +kernel

private theorem slice5 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 5 = true := by
  decide +kernel

private theorem slice6 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 6 = true := by
  decide +kernel

private theorem slice7 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 7 = true := by
  decide +kernel

private theorem slice8 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 8 = true := by
  decide +kernel

private theorem slice9 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 9 = true := by
  decide +kernel

private theorem slice10 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 10 = true := by
  decide +kernel

private theorem slice11 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 11 = true := by
  decide +kernel

private theorem slice12 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 12 = true := by
  decide +kernel

private theorem slice13 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 13 = true := by
  decide +kernel

private theorem slice14 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 14 = true := by
  decide +kernel

private theorem slice15 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 15 = true := by
  decide +kernel

private theorem slice16 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 16 = true := by
  decide +kernel

private theorem slice17 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 17 = true := by
  decide +kernel

private theorem slice18 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 18 = true := by
  decide +kernel

private theorem slice19 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 19 = true := by
  decide +kernel

private theorem slice20 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 20 = true := by
  decide +kernel

private theorem slice21 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 21 = true := by
  decide +kernel

private theorem slice22 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 22 = true := by
  decide +kernel

private theorem slice23 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 23 = true := by
  decide +kernel

private theorem slice24 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 24 = true := by
  decide +kernel

private theorem slice25 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 25 = true := by
  decide +kernel

private theorem slice26 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 26 = true := by
  decide +kernel

private theorem slice27 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 27 = true := by
  decide +kernel

private theorem slice28 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 28 = true := by
  decide +kernel

private theorem slice29 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 29 = true := by
  decide +kernel

private theorem slice30 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 30 = true := by
  decide +kernel

private theorem slice31 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 31 = true := by
  decide +kernel

private theorem slice32 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 32 = true := by
  decide +kernel

private theorem slice33 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 33 = true := by
  decide +kernel

private theorem slice34 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 34 = true := by
  decide +kernel

private theorem slice35 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 35 = true := by
  decide +kernel

private theorem slice36 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 36 = true := by
  decide +kernel

private theorem slice37 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 37 = true := by
  decide +kernel

private theorem slice38 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 38 = true := by
  decide +kernel

private theorem slice39 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 39 = true := by
  decide +kernel

private theorem slice40 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 40 = true := by
  decide +kernel

private theorem slice41 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 41 = true := by
  decide +kernel

private theorem slice42 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 42 = true := by
  decide +kernel

private theorem slice43 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 43 = true := by
  decide +kernel

private theorem slice44 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 44 = true := by
  decide +kernel

private theorem slice45 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 45 = true := by
  decide +kernel

private theorem slice46 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 46 = true := by
  decide +kernel

private theorem slice47 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 47 = true := by
  decide +kernel

private theorem slice48 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 48 = true := by
  decide +kernel

private theorem slice49 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 49 = true := by
  decide +kernel

private theorem slice50 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 50 = true := by
  decide +kernel

private theorem slice51 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 51 = true := by
  decide +kernel

private theorem slice52 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 52 = true := by
  decide +kernel

private theorem slice53 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 53 = true := by
  decide +kernel

private theorem slice54 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 54 = true := by
  decide +kernel

private theorem slice55 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 55 = true := by
  decide +kernel

private theorem slice56 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 56 = true := by
  decide +kernel

private theorem slice57 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 57 = true := by
  decide +kernel

private theorem slice58 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 58 = true := by
  decide +kernel

private theorem slice59 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 59 = true := by
  decide +kernel

private theorem slice60 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 60 = true := by
  decide +kernel

private theorem slice61 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 61 = true := by
  decide +kernel

private theorem slice62 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 62 = true := by
  decide +kernel

private theorem slice63 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 63 = true := by
  decide +kernel

private theorem slice64 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 64 = true := by
  decide +kernel

private theorem slice65 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 65 = true := by
  decide +kernel

private theorem slice66 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 66 = true := by
  decide +kernel

private theorem slice67 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 67 = true := by
  decide +kernel

private theorem slice68 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 68 = true := by
  decide +kernel

private theorem slice69 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 69 = true := by
  decide +kernel

private theorem slice70 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 70 = true := by
  decide +kernel

private theorem slice71 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 71 = true := by
  decide +kernel

private theorem slice72 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 72 = true := by
  decide +kernel

private theorem slice73 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 73 = true := by
  decide +kernel

private theorem slice74 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 74 = true := by
  decide +kernel

private theorem slice75 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 75 = true := by
  decide +kernel

private theorem slice76 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 76 = true := by
  decide +kernel

private theorem slice77 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 77 = true := by
  decide +kernel

private theorem slice78 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 78 = true := by
  decide +kernel

private theorem slice79 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 79 = true := by
  decide +kernel

private theorem slice80 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 80 = true := by
  decide +kernel

private theorem slice81 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 81 = true := by
  decide +kernel

private theorem slice82 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 82 = true := by
  decide +kernel

private theorem slice83 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 83 = true := by
  decide +kernel

private theorem slice84 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 84 = true := by
  decide +kernel

private theorem slice85 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 85 = true := by
  decide +kernel

private theorem slice86 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 86 = true := by
  decide +kernel

private theorem slice87 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 87 = true := by
  decide +kernel

private theorem slice88 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 88 = true := by
  decide +kernel

private theorem slice89 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 89 = true := by
  decide +kernel

private theorem slice90 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 90 = true := by
  decide +kernel

private theorem slice91 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 91 = true := by
  decide +kernel

private theorem slice92 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 92 = true := by
  decide +kernel

private theorem slice93 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 93 = true := by
  decide +kernel

private theorem slice94 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 94 = true := by
  decide +kernel

private theorem slice95 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 95 = true := by
  decide +kernel

private theorem slice96 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 96 = true := by
  decide +kernel

private theorem slice97 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 97 = true := by
  decide +kernel

private theorem slice98 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 98 = true := by
  decide +kernel

private theorem slice99 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 99 = true := by
  decide +kernel

private theorem slice100 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 100 = true := by
  decide +kernel

private theorem slice101 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 101 = true := by
  decide +kernel

private theorem slice102 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 102 = true := by
  decide +kernel

private theorem slice103 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 103 = true := by
  decide +kernel

private theorem slice104 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 104 = true := by
  decide +kernel

private theorem slice105 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 105 = true := by
  decide +kernel

private theorem slice106 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 106 = true := by
  decide +kernel

private theorem slice107 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 107 = true := by
  decide +kernel

private theorem slice108 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 108 = true := by
  decide +kernel

private theorem slice109 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 109 = true := by
  decide +kernel

private theorem slice110 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 110 = true := by
  decide +kernel

private theorem slice111 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 111 = true := by
  decide +kernel

private theorem slice112 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 112 = true := by
  decide +kernel

private theorem slice113 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 113 = true := by
  decide +kernel

private theorem slice114 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 114 = true := by
  decide +kernel

private theorem slice115 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 115 = true := by
  decide +kernel

private theorem slice116 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 116 = true := by
  decide +kernel

private theorem slice117 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 117 = true := by
  decide +kernel

private theorem slice118 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 118 = true := by
  decide +kernel

private theorem slice119 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 119 = true := by
  decide +kernel

private theorem slice120 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 120 = true := by
  decide +kernel

private theorem slice121 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 121 = true := by
  decide +kernel

private theorem slice122 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 122 = true := by
  decide +kernel

private theorem slice123 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 123 = true := by
  decide +kernel

private theorem slice124 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 124 = true := by
  decide +kernel

private theorem slice125 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 125 = true := by
  decide +kernel

private theorem slice126 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 126 = true := by
  decide +kernel

private theorem slice127 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 127 = true := by
  decide +kernel

private theorem slice128 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 128 = true := by
  decide +kernel

private theorem slice129 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 129 = true := by
  decide +kernel

private theorem slice130 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 130 = true := by
  decide +kernel

private theorem slice131 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 131 = true := by
  decide +kernel

private theorem slice132 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 132 = true := by
  decide +kernel

private theorem slice133 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 133 = true := by
  decide +kernel

private theorem slice134 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 134 = true := by
  decide +kernel

private theorem slice135 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 135 = true := by
  decide +kernel

private theorem slice136 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 136 = true := by
  decide +kernel

private theorem slice137 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 137 = true := by
  decide +kernel

private theorem slice138 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 138 = true := by
  decide +kernel

private theorem slice139 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 139 = true := by
  decide +kernel

private theorem slice140 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 140 = true := by
  decide +kernel

private theorem slice141 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 141 = true := by
  decide +kernel

private theorem slice142 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 142 = true := by
  decide +kernel

private theorem slice143 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 143 = true := by
  decide +kernel

private theorem slice144 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 144 = true := by
  decide +kernel

private theorem slice145 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 145 = true := by
  decide +kernel

private theorem slice146 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 146 = true := by
  decide +kernel

private theorem slice147 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 147 = true := by
  decide +kernel

private theorem slice148 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 148 = true := by
  decide +kernel

private theorem slice149 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 149 = true := by
  decide +kernel

private theorem slice150 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 150 = true := by
  decide +kernel

private theorem slice151 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 151 = true := by
  decide +kernel

private theorem slice152 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 152 = true := by
  decide +kernel

private theorem slice153 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 153 = true := by
  decide +kernel

private theorem slice154 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 154 = true := by
  decide +kernel

private theorem slice155 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 155 = true := by
  decide +kernel

private theorem slice156 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 156 = true := by
  decide +kernel

private theorem slice157 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 157 = true := by
  decide +kernel

private theorem slice158 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 158 = true := by
  decide +kernel

private theorem slice159 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 159 = true := by
  decide +kernel

private theorem slice160 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 160 = true := by
  decide +kernel

private theorem slice161 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 161 = true := by
  decide +kernel

private theorem slice162 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 162 = true := by
  decide +kernel

private theorem slice163 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 163 = true := by
  decide +kernel

private theorem slice164 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 164 = true := by
  decide +kernel

private theorem slice165 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 165 = true := by
  decide +kernel

private theorem slice166 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 166 = true := by
  decide +kernel

private theorem slice167 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 167 = true := by
  decide +kernel

private theorem slice168 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 168 = true := by
  decide +kernel

private theorem slice169 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 169 = true := by
  decide +kernel

private theorem slice170 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 170 = true := by
  decide +kernel

private theorem slice171 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 171 = true := by
  decide +kernel

private theorem slice172 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 172 = true := by
  decide +kernel

private theorem slice173 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 173 = true := by
  decide +kernel

private theorem slice174 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 174 = true := by
  decide +kernel

private theorem slice175 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 175 = true := by
  decide +kernel

private theorem slice176 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 176 = true := by
  decide +kernel

private theorem slice177 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 177 = true := by
  decide +kernel

private theorem slice178 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 178 = true := by
  decide +kernel

private theorem slice179 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 179 = true := by
  decide +kernel

private theorem slice180 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 180 = true := by
  decide +kernel

private theorem slice181 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 181 = true := by
  decide +kernel

private theorem slice182 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 182 = true := by
  decide +kernel

private theorem slice183 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 183 = true := by
  decide +kernel

private theorem slice184 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 184 = true := by
  decide +kernel

private theorem slice185 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 185 = true := by
  decide +kernel

private theorem slice186 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 186 = true := by
  decide +kernel

private theorem slice187 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 187 = true := by
  decide +kernel

private theorem slice188 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 188 = true := by
  decide +kernel

private theorem slice189 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 189 = true := by
  decide +kernel

private theorem slice190 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 190 = true := by
  decide +kernel

private theorem slice191 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 191 = true := by
  decide +kernel

private theorem slice192 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 192 = true := by
  decide +kernel

private theorem slice193 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 193 = true := by
  decide +kernel

private theorem slice194 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 194 = true := by
  decide +kernel

private theorem slice195 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 195 = true := by
  decide +kernel

private theorem slice196 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 196 = true := by
  decide +kernel

private theorem slice197 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 197 = true := by
  decide +kernel

private theorem slice198 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 198 = true := by
  decide +kernel

private theorem slice199 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 199 = true := by
  decide +kernel

private theorem slice200 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 200 = true := by
  decide +kernel

private theorem slice201 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 201 = true := by
  decide +kernel

private theorem slice202 : FactorMaps.slice 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] 202 = true := by
  decide +kernel

/-- The cached checks certify the original transition on the whole domain. -/
public theorem checked : stepCheck (FactorWords.row 64).1 (FactorWords.row 64).2 := by
  apply FactorMaps.ofSlices 64 [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1] [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1] repWord targetWord
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

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense2.Row64
