module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 256

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point256slice0 : Part6Nat.slice 0 3995 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice1 : Part6Nat.slice 0 3995 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice2 : Part6Nat.slice 0 3995 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice3 : Part6Nat.slice 0 3995 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice4 : Part6Nat.slice 0 3995 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice5 : Part6Nat.slice 0 3995 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice6 : Part6Nat.slice 0 3995 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice7 : Part6Nat.slice 0 3995 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice8 : Part6Nat.slice 0 3995 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice9 : Part6Nat.slice 0 3995 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice10 : Part6Nat.slice 0 3995 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice11 : Part6Nat.slice 0 3995 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice12 : Part6Nat.slice 0 3995 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice13 : Part6Nat.slice 0 3995 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice14 : Part6Nat.slice 0 3995 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice15 : Part6Nat.slice 0 3995 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice16 : Part6Nat.slice 0 3995 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice17 : Part6Nat.slice 0 3995 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice18 : Part6Nat.slice 0 3995 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice19 : Part6Nat.slice 0 3995 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice20 : Part6Nat.slice 0 3995 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice21 : Part6Nat.slice 0 3995 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice22 : Part6Nat.slice 0 3995 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice23 : Part6Nat.slice 0 3995 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice24 : Part6Nat.slice 0 3995 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice25 : Part6Nat.slice 0 3995 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice26 : Part6Nat.slice 0 3995 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice27 : Part6Nat.slice 0 3995 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice28 : Part6Nat.slice 0 3995 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice29 : Part6Nat.slice 0 3995 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice30 : Part6Nat.slice 0 3995 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice31 : Part6Nat.slice 0 3995 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice32 : Part6Nat.slice 0 3995 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice33 : Part6Nat.slice 0 3995 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice34 : Part6Nat.slice 0 3995 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice35 : Part6Nat.slice 0 3995 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice36 : Part6Nat.slice 0 3995 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice37 : Part6Nat.slice 0 3995 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice38 : Part6Nat.slice 0 3995 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice39 : Part6Nat.slice 0 3995 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice40 : Part6Nat.slice 0 3995 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice41 : Part6Nat.slice 0 3995 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice42 : Part6Nat.slice 0 3995 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice43 : Part6Nat.slice 0 3995 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice44 : Part6Nat.slice 0 3995 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice45 : Part6Nat.slice 0 3995 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice46 : Part6Nat.slice 0 3995 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice47 : Part6Nat.slice 0 3995 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice48 : Part6Nat.slice 0 3995 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice49 : Part6Nat.slice 0 3995 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice50 : Part6Nat.slice 0 3995 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice51 : Part6Nat.slice 0 3995 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice52 : Part6Nat.slice 0 3995 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice53 : Part6Nat.slice 0 3995 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice54 : Part6Nat.slice 0 3995 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice55 : Part6Nat.slice 0 3995 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice56 : Part6Nat.slice 0 3995 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice57 : Part6Nat.slice 0 3995 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice58 : Part6Nat.slice 0 3995 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice59 : Part6Nat.slice 0 3995 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice60 : Part6Nat.slice 0 3995 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice61 : Part6Nat.slice 0 3995 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice62 : Part6Nat.slice 0 3995 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice63 : Part6Nat.slice 0 3995 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice64 : Part6Nat.slice 0 3995 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice65 : Part6Nat.slice 0 3995 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice66 : Part6Nat.slice 0 3995 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice67 : Part6Nat.slice 0 3995 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice68 : Part6Nat.slice 0 3995 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice69 : Part6Nat.slice 0 3995 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice70 : Part6Nat.slice 0 3995 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice71 : Part6Nat.slice 0 3995 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice72 : Part6Nat.slice 0 3995 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice73 : Part6Nat.slice 0 3995 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice74 : Part6Nat.slice 0 3995 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice75 : Part6Nat.slice 0 3995 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice76 : Part6Nat.slice 0 3995 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice77 : Part6Nat.slice 0 3995 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice78 : Part6Nat.slice 0 3995 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice79 : Part6Nat.slice 0 3995 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice80 : Part6Nat.slice 0 3995 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice81 : Part6Nat.slice 0 3995 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice82 : Part6Nat.slice 0 3995 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice83 : Part6Nat.slice 0 3995 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice84 : Part6Nat.slice 0 3995 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice85 : Part6Nat.slice 0 3995 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice86 : Part6Nat.slice 0 3995 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice87 : Part6Nat.slice 0 3995 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice88 : Part6Nat.slice 0 3995 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice89 : Part6Nat.slice 0 3995 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice90 : Part6Nat.slice 0 3995 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice91 : Part6Nat.slice 0 3995 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice92 : Part6Nat.slice 0 3995 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice93 : Part6Nat.slice 0 3995 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice94 : Part6Nat.slice 0 3995 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice95 : Part6Nat.slice 0 3995 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice96 : Part6Nat.slice 0 3995 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice97 : Part6Nat.slice 0 3995 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice98 : Part6Nat.slice 0 3995 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice99 : Part6Nat.slice 0 3995 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice100 : Part6Nat.slice 0 3995 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice101 : Part6Nat.slice 0 3995 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice102 : Part6Nat.slice 0 3995 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice103 : Part6Nat.slice 0 3995 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice104 : Part6Nat.slice 0 3995 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice105 : Part6Nat.slice 0 3995 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice106 : Part6Nat.slice 0 3995 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice107 : Part6Nat.slice 0 3995 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice108 : Part6Nat.slice 0 3995 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice109 : Part6Nat.slice 0 3995 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice110 : Part6Nat.slice 0 3995 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice111 : Part6Nat.slice 0 3995 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice112 : Part6Nat.slice 0 3995 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice113 : Part6Nat.slice 0 3995 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice114 : Part6Nat.slice 0 3995 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice115 : Part6Nat.slice 0 3995 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice116 : Part6Nat.slice 0 3995 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice117 : Part6Nat.slice 0 3995 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice118 : Part6Nat.slice 0 3995 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice119 : Part6Nat.slice 0 3995 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice120 : Part6Nat.slice 0 3995 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice121 : Part6Nat.slice 0 3995 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice122 : Part6Nat.slice 0 3995 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice123 : Part6Nat.slice 0 3995 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice124 : Part6Nat.slice 0 3995 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice125 : Part6Nat.slice 0 3995 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice126 : Part6Nat.slice 0 3995 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice127 : Part6Nat.slice 0 3995 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice128 : Part6Nat.slice 0 3995 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice129 : Part6Nat.slice 0 3995 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice130 : Part6Nat.slice 0 3995 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice131 : Part6Nat.slice 0 3995 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice132 : Part6Nat.slice 0 3995 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice133 : Part6Nat.slice 0 3995 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice134 : Part6Nat.slice 0 3995 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice135 : Part6Nat.slice 0 3995 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice136 : Part6Nat.slice 0 3995 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice137 : Part6Nat.slice 0 3995 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice138 : Part6Nat.slice 0 3995 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice139 : Part6Nat.slice 0 3995 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice140 : Part6Nat.slice 0 3995 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice141 : Part6Nat.slice 0 3995 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice142 : Part6Nat.slice 0 3995 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice143 : Part6Nat.slice 0 3995 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice144 : Part6Nat.slice 0 3995 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice145 : Part6Nat.slice 0 3995 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice146 : Part6Nat.slice 0 3995 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice147 : Part6Nat.slice 0 3995 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice148 : Part6Nat.slice 0 3995 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice149 : Part6Nat.slice 0 3995 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice150 : Part6Nat.slice 0 3995 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice151 : Part6Nat.slice 0 3995 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice152 : Part6Nat.slice 0 3995 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice153 : Part6Nat.slice 0 3995 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice154 : Part6Nat.slice 0 3995 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice155 : Part6Nat.slice 0 3995 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice156 : Part6Nat.slice 0 3995 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice157 : Part6Nat.slice 0 3995 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice158 : Part6Nat.slice 0 3995 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice159 : Part6Nat.slice 0 3995 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice160 : Part6Nat.slice 0 3995 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice161 : Part6Nat.slice 0 3995 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice162 : Part6Nat.slice 0 3995 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice163 : Part6Nat.slice 0 3995 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice164 : Part6Nat.slice 0 3995 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice165 : Part6Nat.slice 0 3995 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice166 : Part6Nat.slice 0 3995 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice167 : Part6Nat.slice 0 3995 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice168 : Part6Nat.slice 0 3995 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice169 : Part6Nat.slice 0 3995 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice170 : Part6Nat.slice 0 3995 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice171 : Part6Nat.slice 0 3995 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice172 : Part6Nat.slice 0 3995 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice173 : Part6Nat.slice 0 3995 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice174 : Part6Nat.slice 0 3995 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice175 : Part6Nat.slice 0 3995 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice176 : Part6Nat.slice 0 3995 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice177 : Part6Nat.slice 0 3995 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice178 : Part6Nat.slice 0 3995 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice179 : Part6Nat.slice 0 3995 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice180 : Part6Nat.slice 0 3995 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice181 : Part6Nat.slice 0 3995 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice182 : Part6Nat.slice 0 3995 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice183 : Part6Nat.slice 0 3995 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice184 : Part6Nat.slice 0 3995 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice185 : Part6Nat.slice 0 3995 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice186 : Part6Nat.slice 0 3995 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice187 : Part6Nat.slice 0 3995 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice188 : Part6Nat.slice 0 3995 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice189 : Part6Nat.slice 0 3995 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice190 : Part6Nat.slice 0 3995 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice191 : Part6Nat.slice 0 3995 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice192 : Part6Nat.slice 0 3995 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice193 : Part6Nat.slice 0 3995 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice194 : Part6Nat.slice 0 3995 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice195 : Part6Nat.slice 0 3995 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice196 : Part6Nat.slice 0 3995 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice197 : Part6Nat.slice 0 3995 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice198 : Part6Nat.slice 0 3995 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice199 : Part6Nat.slice 0 3995 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice200 : Part6Nat.slice 0 3995 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice201 : Part6Nat.slice 0 3995 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point256slice202 : Part6Nat.slice 0 3995 202 = true := by
  decide +kernel

public theorem point256 : stepCheck 0 3995 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point256slice0
  · exact point256slice1
  · exact point256slice2
  · exact point256slice3
  · exact point256slice4
  · exact point256slice5
  · exact point256slice6
  · exact point256slice7
  · exact point256slice8
  · exact point256slice9
  · exact point256slice10
  · exact point256slice11
  · exact point256slice12
  · exact point256slice13
  · exact point256slice14
  · exact point256slice15
  · exact point256slice16
  · exact point256slice17
  · exact point256slice18
  · exact point256slice19
  · exact point256slice20
  · exact point256slice21
  · exact point256slice22
  · exact point256slice23
  · exact point256slice24
  · exact point256slice25
  · exact point256slice26
  · exact point256slice27
  · exact point256slice28
  · exact point256slice29
  · exact point256slice30
  · exact point256slice31
  · exact point256slice32
  · exact point256slice33
  · exact point256slice34
  · exact point256slice35
  · exact point256slice36
  · exact point256slice37
  · exact point256slice38
  · exact point256slice39
  · exact point256slice40
  · exact point256slice41
  · exact point256slice42
  · exact point256slice43
  · exact point256slice44
  · exact point256slice45
  · exact point256slice46
  · exact point256slice47
  · exact point256slice48
  · exact point256slice49
  · exact point256slice50
  · exact point256slice51
  · exact point256slice52
  · exact point256slice53
  · exact point256slice54
  · exact point256slice55
  · exact point256slice56
  · exact point256slice57
  · exact point256slice58
  · exact point256slice59
  · exact point256slice60
  · exact point256slice61
  · exact point256slice62
  · exact point256slice63
  · exact point256slice64
  · exact point256slice65
  · exact point256slice66
  · exact point256slice67
  · exact point256slice68
  · exact point256slice69
  · exact point256slice70
  · exact point256slice71
  · exact point256slice72
  · exact point256slice73
  · exact point256slice74
  · exact point256slice75
  · exact point256slice76
  · exact point256slice77
  · exact point256slice78
  · exact point256slice79
  · exact point256slice80
  · exact point256slice81
  · exact point256slice82
  · exact point256slice83
  · exact point256slice84
  · exact point256slice85
  · exact point256slice86
  · exact point256slice87
  · exact point256slice88
  · exact point256slice89
  · exact point256slice90
  · exact point256slice91
  · exact point256slice92
  · exact point256slice93
  · exact point256slice94
  · exact point256slice95
  · exact point256slice96
  · exact point256slice97
  · exact point256slice98
  · exact point256slice99
  · exact point256slice100
  · exact point256slice101
  · exact point256slice102
  · exact point256slice103
  · exact point256slice104
  · exact point256slice105
  · exact point256slice106
  · exact point256slice107
  · exact point256slice108
  · exact point256slice109
  · exact point256slice110
  · exact point256slice111
  · exact point256slice112
  · exact point256slice113
  · exact point256slice114
  · exact point256slice115
  · exact point256slice116
  · exact point256slice117
  · exact point256slice118
  · exact point256slice119
  · exact point256slice120
  · exact point256slice121
  · exact point256slice122
  · exact point256slice123
  · exact point256slice124
  · exact point256slice125
  · exact point256slice126
  · exact point256slice127
  · exact point256slice128
  · exact point256slice129
  · exact point256slice130
  · exact point256slice131
  · exact point256slice132
  · exact point256slice133
  · exact point256slice134
  · exact point256slice135
  · exact point256slice136
  · exact point256slice137
  · exact point256slice138
  · exact point256slice139
  · exact point256slice140
  · exact point256slice141
  · exact point256slice142
  · exact point256slice143
  · exact point256slice144
  · exact point256slice145
  · exact point256slice146
  · exact point256slice147
  · exact point256slice148
  · exact point256slice149
  · exact point256slice150
  · exact point256slice151
  · exact point256slice152
  · exact point256slice153
  · exact point256slice154
  · exact point256slice155
  · exact point256slice156
  · exact point256slice157
  · exact point256slice158
  · exact point256slice159
  · exact point256slice160
  · exact point256slice161
  · exact point256slice162
  · exact point256slice163
  · exact point256slice164
  · exact point256slice165
  · exact point256slice166
  · exact point256slice167
  · exact point256slice168
  · exact point256slice169
  · exact point256slice170
  · exact point256slice171
  · exact point256slice172
  · exact point256slice173
  · exact point256slice174
  · exact point256slice175
  · exact point256slice176
  · exact point256slice177
  · exact point256slice178
  · exact point256slice179
  · exact point256slice180
  · exact point256slice181
  · exact point256slice182
  · exact point256slice183
  · exact point256slice184
  · exact point256slice185
  · exact point256slice186
  · exact point256slice187
  · exact point256slice188
  · exact point256slice189
  · exact point256slice190
  · exact point256slice191
  · exact point256slice192
  · exact point256slice193
  · exact point256slice194
  · exact point256slice195
  · exact point256slice196
  · exact point256slice197
  · exact point256slice198
  · exact point256slice199
  · exact point256slice200
  · exact point256slice201
  · exact point256slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
