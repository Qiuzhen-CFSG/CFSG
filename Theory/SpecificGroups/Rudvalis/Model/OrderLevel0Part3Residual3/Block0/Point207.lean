module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 207

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point207slice0 : Part6Nat.slice 1 3560 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice1 : Part6Nat.slice 1 3560 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice2 : Part6Nat.slice 1 3560 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice3 : Part6Nat.slice 1 3560 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice4 : Part6Nat.slice 1 3560 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice5 : Part6Nat.slice 1 3560 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice6 : Part6Nat.slice 1 3560 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice7 : Part6Nat.slice 1 3560 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice8 : Part6Nat.slice 1 3560 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice9 : Part6Nat.slice 1 3560 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice10 : Part6Nat.slice 1 3560 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice11 : Part6Nat.slice 1 3560 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice12 : Part6Nat.slice 1 3560 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice13 : Part6Nat.slice 1 3560 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice14 : Part6Nat.slice 1 3560 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice15 : Part6Nat.slice 1 3560 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice16 : Part6Nat.slice 1 3560 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice17 : Part6Nat.slice 1 3560 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice18 : Part6Nat.slice 1 3560 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice19 : Part6Nat.slice 1 3560 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice20 : Part6Nat.slice 1 3560 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice21 : Part6Nat.slice 1 3560 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice22 : Part6Nat.slice 1 3560 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice23 : Part6Nat.slice 1 3560 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice24 : Part6Nat.slice 1 3560 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice25 : Part6Nat.slice 1 3560 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice26 : Part6Nat.slice 1 3560 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice27 : Part6Nat.slice 1 3560 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice28 : Part6Nat.slice 1 3560 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice29 : Part6Nat.slice 1 3560 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice30 : Part6Nat.slice 1 3560 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice31 : Part6Nat.slice 1 3560 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice32 : Part6Nat.slice 1 3560 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice33 : Part6Nat.slice 1 3560 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice34 : Part6Nat.slice 1 3560 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice35 : Part6Nat.slice 1 3560 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice36 : Part6Nat.slice 1 3560 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice37 : Part6Nat.slice 1 3560 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice38 : Part6Nat.slice 1 3560 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice39 : Part6Nat.slice 1 3560 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice40 : Part6Nat.slice 1 3560 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice41 : Part6Nat.slice 1 3560 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice42 : Part6Nat.slice 1 3560 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice43 : Part6Nat.slice 1 3560 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice44 : Part6Nat.slice 1 3560 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice45 : Part6Nat.slice 1 3560 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice46 : Part6Nat.slice 1 3560 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice47 : Part6Nat.slice 1 3560 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice48 : Part6Nat.slice 1 3560 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice49 : Part6Nat.slice 1 3560 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice50 : Part6Nat.slice 1 3560 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice51 : Part6Nat.slice 1 3560 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice52 : Part6Nat.slice 1 3560 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice53 : Part6Nat.slice 1 3560 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice54 : Part6Nat.slice 1 3560 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice55 : Part6Nat.slice 1 3560 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice56 : Part6Nat.slice 1 3560 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice57 : Part6Nat.slice 1 3560 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice58 : Part6Nat.slice 1 3560 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice59 : Part6Nat.slice 1 3560 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice60 : Part6Nat.slice 1 3560 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice61 : Part6Nat.slice 1 3560 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice62 : Part6Nat.slice 1 3560 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice63 : Part6Nat.slice 1 3560 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice64 : Part6Nat.slice 1 3560 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice65 : Part6Nat.slice 1 3560 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice66 : Part6Nat.slice 1 3560 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice67 : Part6Nat.slice 1 3560 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice68 : Part6Nat.slice 1 3560 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice69 : Part6Nat.slice 1 3560 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice70 : Part6Nat.slice 1 3560 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice71 : Part6Nat.slice 1 3560 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice72 : Part6Nat.slice 1 3560 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice73 : Part6Nat.slice 1 3560 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice74 : Part6Nat.slice 1 3560 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice75 : Part6Nat.slice 1 3560 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice76 : Part6Nat.slice 1 3560 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice77 : Part6Nat.slice 1 3560 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice78 : Part6Nat.slice 1 3560 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice79 : Part6Nat.slice 1 3560 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice80 : Part6Nat.slice 1 3560 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice81 : Part6Nat.slice 1 3560 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice82 : Part6Nat.slice 1 3560 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice83 : Part6Nat.slice 1 3560 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice84 : Part6Nat.slice 1 3560 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice85 : Part6Nat.slice 1 3560 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice86 : Part6Nat.slice 1 3560 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice87 : Part6Nat.slice 1 3560 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice88 : Part6Nat.slice 1 3560 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice89 : Part6Nat.slice 1 3560 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice90 : Part6Nat.slice 1 3560 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice91 : Part6Nat.slice 1 3560 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice92 : Part6Nat.slice 1 3560 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice93 : Part6Nat.slice 1 3560 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice94 : Part6Nat.slice 1 3560 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice95 : Part6Nat.slice 1 3560 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice96 : Part6Nat.slice 1 3560 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice97 : Part6Nat.slice 1 3560 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice98 : Part6Nat.slice 1 3560 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice99 : Part6Nat.slice 1 3560 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice100 : Part6Nat.slice 1 3560 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice101 : Part6Nat.slice 1 3560 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice102 : Part6Nat.slice 1 3560 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice103 : Part6Nat.slice 1 3560 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice104 : Part6Nat.slice 1 3560 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice105 : Part6Nat.slice 1 3560 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice106 : Part6Nat.slice 1 3560 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice107 : Part6Nat.slice 1 3560 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice108 : Part6Nat.slice 1 3560 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice109 : Part6Nat.slice 1 3560 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice110 : Part6Nat.slice 1 3560 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice111 : Part6Nat.slice 1 3560 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice112 : Part6Nat.slice 1 3560 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice113 : Part6Nat.slice 1 3560 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice114 : Part6Nat.slice 1 3560 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice115 : Part6Nat.slice 1 3560 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice116 : Part6Nat.slice 1 3560 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice117 : Part6Nat.slice 1 3560 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice118 : Part6Nat.slice 1 3560 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice119 : Part6Nat.slice 1 3560 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice120 : Part6Nat.slice 1 3560 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice121 : Part6Nat.slice 1 3560 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice122 : Part6Nat.slice 1 3560 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice123 : Part6Nat.slice 1 3560 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice124 : Part6Nat.slice 1 3560 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice125 : Part6Nat.slice 1 3560 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice126 : Part6Nat.slice 1 3560 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice127 : Part6Nat.slice 1 3560 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice128 : Part6Nat.slice 1 3560 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice129 : Part6Nat.slice 1 3560 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice130 : Part6Nat.slice 1 3560 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice131 : Part6Nat.slice 1 3560 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice132 : Part6Nat.slice 1 3560 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice133 : Part6Nat.slice 1 3560 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice134 : Part6Nat.slice 1 3560 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice135 : Part6Nat.slice 1 3560 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice136 : Part6Nat.slice 1 3560 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice137 : Part6Nat.slice 1 3560 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice138 : Part6Nat.slice 1 3560 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice139 : Part6Nat.slice 1 3560 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice140 : Part6Nat.slice 1 3560 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice141 : Part6Nat.slice 1 3560 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice142 : Part6Nat.slice 1 3560 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice143 : Part6Nat.slice 1 3560 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice144 : Part6Nat.slice 1 3560 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice145 : Part6Nat.slice 1 3560 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice146 : Part6Nat.slice 1 3560 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice147 : Part6Nat.slice 1 3560 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice148 : Part6Nat.slice 1 3560 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice149 : Part6Nat.slice 1 3560 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice150 : Part6Nat.slice 1 3560 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice151 : Part6Nat.slice 1 3560 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice152 : Part6Nat.slice 1 3560 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice153 : Part6Nat.slice 1 3560 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice154 : Part6Nat.slice 1 3560 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice155 : Part6Nat.slice 1 3560 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice156 : Part6Nat.slice 1 3560 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice157 : Part6Nat.slice 1 3560 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice158 : Part6Nat.slice 1 3560 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice159 : Part6Nat.slice 1 3560 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice160 : Part6Nat.slice 1 3560 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice161 : Part6Nat.slice 1 3560 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice162 : Part6Nat.slice 1 3560 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice163 : Part6Nat.slice 1 3560 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice164 : Part6Nat.slice 1 3560 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice165 : Part6Nat.slice 1 3560 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice166 : Part6Nat.slice 1 3560 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice167 : Part6Nat.slice 1 3560 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice168 : Part6Nat.slice 1 3560 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice169 : Part6Nat.slice 1 3560 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice170 : Part6Nat.slice 1 3560 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice171 : Part6Nat.slice 1 3560 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice172 : Part6Nat.slice 1 3560 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice173 : Part6Nat.slice 1 3560 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice174 : Part6Nat.slice 1 3560 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice175 : Part6Nat.slice 1 3560 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice176 : Part6Nat.slice 1 3560 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice177 : Part6Nat.slice 1 3560 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice178 : Part6Nat.slice 1 3560 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice179 : Part6Nat.slice 1 3560 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice180 : Part6Nat.slice 1 3560 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice181 : Part6Nat.slice 1 3560 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice182 : Part6Nat.slice 1 3560 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice183 : Part6Nat.slice 1 3560 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice184 : Part6Nat.slice 1 3560 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice185 : Part6Nat.slice 1 3560 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice186 : Part6Nat.slice 1 3560 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice187 : Part6Nat.slice 1 3560 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice188 : Part6Nat.slice 1 3560 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice189 : Part6Nat.slice 1 3560 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice190 : Part6Nat.slice 1 3560 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice191 : Part6Nat.slice 1 3560 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice192 : Part6Nat.slice 1 3560 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice193 : Part6Nat.slice 1 3560 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice194 : Part6Nat.slice 1 3560 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice195 : Part6Nat.slice 1 3560 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice196 : Part6Nat.slice 1 3560 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice197 : Part6Nat.slice 1 3560 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice198 : Part6Nat.slice 1 3560 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice199 : Part6Nat.slice 1 3560 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice200 : Part6Nat.slice 1 3560 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice201 : Part6Nat.slice 1 3560 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point207slice202 : Part6Nat.slice 1 3560 202 = true := by
  decide +kernel

public theorem point207 : stepCheck 1 3560 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point207slice0
  · exact point207slice1
  · exact point207slice2
  · exact point207slice3
  · exact point207slice4
  · exact point207slice5
  · exact point207slice6
  · exact point207slice7
  · exact point207slice8
  · exact point207slice9
  · exact point207slice10
  · exact point207slice11
  · exact point207slice12
  · exact point207slice13
  · exact point207slice14
  · exact point207slice15
  · exact point207slice16
  · exact point207slice17
  · exact point207slice18
  · exact point207slice19
  · exact point207slice20
  · exact point207slice21
  · exact point207slice22
  · exact point207slice23
  · exact point207slice24
  · exact point207slice25
  · exact point207slice26
  · exact point207slice27
  · exact point207slice28
  · exact point207slice29
  · exact point207slice30
  · exact point207slice31
  · exact point207slice32
  · exact point207slice33
  · exact point207slice34
  · exact point207slice35
  · exact point207slice36
  · exact point207slice37
  · exact point207slice38
  · exact point207slice39
  · exact point207slice40
  · exact point207slice41
  · exact point207slice42
  · exact point207slice43
  · exact point207slice44
  · exact point207slice45
  · exact point207slice46
  · exact point207slice47
  · exact point207slice48
  · exact point207slice49
  · exact point207slice50
  · exact point207slice51
  · exact point207slice52
  · exact point207slice53
  · exact point207slice54
  · exact point207slice55
  · exact point207slice56
  · exact point207slice57
  · exact point207slice58
  · exact point207slice59
  · exact point207slice60
  · exact point207slice61
  · exact point207slice62
  · exact point207slice63
  · exact point207slice64
  · exact point207slice65
  · exact point207slice66
  · exact point207slice67
  · exact point207slice68
  · exact point207slice69
  · exact point207slice70
  · exact point207slice71
  · exact point207slice72
  · exact point207slice73
  · exact point207slice74
  · exact point207slice75
  · exact point207slice76
  · exact point207slice77
  · exact point207slice78
  · exact point207slice79
  · exact point207slice80
  · exact point207slice81
  · exact point207slice82
  · exact point207slice83
  · exact point207slice84
  · exact point207slice85
  · exact point207slice86
  · exact point207slice87
  · exact point207slice88
  · exact point207slice89
  · exact point207slice90
  · exact point207slice91
  · exact point207slice92
  · exact point207slice93
  · exact point207slice94
  · exact point207slice95
  · exact point207slice96
  · exact point207slice97
  · exact point207slice98
  · exact point207slice99
  · exact point207slice100
  · exact point207slice101
  · exact point207slice102
  · exact point207slice103
  · exact point207slice104
  · exact point207slice105
  · exact point207slice106
  · exact point207slice107
  · exact point207slice108
  · exact point207slice109
  · exact point207slice110
  · exact point207slice111
  · exact point207slice112
  · exact point207slice113
  · exact point207slice114
  · exact point207slice115
  · exact point207slice116
  · exact point207slice117
  · exact point207slice118
  · exact point207slice119
  · exact point207slice120
  · exact point207slice121
  · exact point207slice122
  · exact point207slice123
  · exact point207slice124
  · exact point207slice125
  · exact point207slice126
  · exact point207slice127
  · exact point207slice128
  · exact point207slice129
  · exact point207slice130
  · exact point207slice131
  · exact point207slice132
  · exact point207slice133
  · exact point207slice134
  · exact point207slice135
  · exact point207slice136
  · exact point207slice137
  · exact point207slice138
  · exact point207slice139
  · exact point207slice140
  · exact point207slice141
  · exact point207slice142
  · exact point207slice143
  · exact point207slice144
  · exact point207slice145
  · exact point207slice146
  · exact point207slice147
  · exact point207slice148
  · exact point207slice149
  · exact point207slice150
  · exact point207slice151
  · exact point207slice152
  · exact point207slice153
  · exact point207slice154
  · exact point207slice155
  · exact point207slice156
  · exact point207slice157
  · exact point207slice158
  · exact point207slice159
  · exact point207slice160
  · exact point207slice161
  · exact point207slice162
  · exact point207slice163
  · exact point207slice164
  · exact point207slice165
  · exact point207slice166
  · exact point207slice167
  · exact point207slice168
  · exact point207slice169
  · exact point207slice170
  · exact point207slice171
  · exact point207slice172
  · exact point207slice173
  · exact point207slice174
  · exact point207slice175
  · exact point207slice176
  · exact point207slice177
  · exact point207slice178
  · exact point207slice179
  · exact point207slice180
  · exact point207slice181
  · exact point207slice182
  · exact point207slice183
  · exact point207slice184
  · exact point207slice185
  · exact point207slice186
  · exact point207slice187
  · exact point207slice188
  · exact point207slice189
  · exact point207slice190
  · exact point207slice191
  · exact point207slice192
  · exact point207slice193
  · exact point207slice194
  · exact point207slice195
  · exact point207slice196
  · exact point207slice197
  · exact point207slice198
  · exact point207slice199
  · exact point207slice200
  · exact point207slice201
  · exact point207slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
