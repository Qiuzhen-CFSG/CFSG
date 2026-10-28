module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 245

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point245slice0 : Part6Nat.slice 0 3983 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice1 : Part6Nat.slice 0 3983 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice2 : Part6Nat.slice 0 3983 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice3 : Part6Nat.slice 0 3983 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice4 : Part6Nat.slice 0 3983 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice5 : Part6Nat.slice 0 3983 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice6 : Part6Nat.slice 0 3983 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice7 : Part6Nat.slice 0 3983 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice8 : Part6Nat.slice 0 3983 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice9 : Part6Nat.slice 0 3983 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice10 : Part6Nat.slice 0 3983 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice11 : Part6Nat.slice 0 3983 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice12 : Part6Nat.slice 0 3983 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice13 : Part6Nat.slice 0 3983 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice14 : Part6Nat.slice 0 3983 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice15 : Part6Nat.slice 0 3983 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice16 : Part6Nat.slice 0 3983 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice17 : Part6Nat.slice 0 3983 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice18 : Part6Nat.slice 0 3983 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice19 : Part6Nat.slice 0 3983 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice20 : Part6Nat.slice 0 3983 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice21 : Part6Nat.slice 0 3983 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice22 : Part6Nat.slice 0 3983 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice23 : Part6Nat.slice 0 3983 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice24 : Part6Nat.slice 0 3983 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice25 : Part6Nat.slice 0 3983 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice26 : Part6Nat.slice 0 3983 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice27 : Part6Nat.slice 0 3983 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice28 : Part6Nat.slice 0 3983 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice29 : Part6Nat.slice 0 3983 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice30 : Part6Nat.slice 0 3983 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice31 : Part6Nat.slice 0 3983 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice32 : Part6Nat.slice 0 3983 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice33 : Part6Nat.slice 0 3983 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice34 : Part6Nat.slice 0 3983 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice35 : Part6Nat.slice 0 3983 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice36 : Part6Nat.slice 0 3983 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice37 : Part6Nat.slice 0 3983 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice38 : Part6Nat.slice 0 3983 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice39 : Part6Nat.slice 0 3983 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice40 : Part6Nat.slice 0 3983 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice41 : Part6Nat.slice 0 3983 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice42 : Part6Nat.slice 0 3983 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice43 : Part6Nat.slice 0 3983 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice44 : Part6Nat.slice 0 3983 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice45 : Part6Nat.slice 0 3983 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice46 : Part6Nat.slice 0 3983 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice47 : Part6Nat.slice 0 3983 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice48 : Part6Nat.slice 0 3983 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice49 : Part6Nat.slice 0 3983 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice50 : Part6Nat.slice 0 3983 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice51 : Part6Nat.slice 0 3983 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice52 : Part6Nat.slice 0 3983 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice53 : Part6Nat.slice 0 3983 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice54 : Part6Nat.slice 0 3983 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice55 : Part6Nat.slice 0 3983 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice56 : Part6Nat.slice 0 3983 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice57 : Part6Nat.slice 0 3983 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice58 : Part6Nat.slice 0 3983 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice59 : Part6Nat.slice 0 3983 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice60 : Part6Nat.slice 0 3983 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice61 : Part6Nat.slice 0 3983 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice62 : Part6Nat.slice 0 3983 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice63 : Part6Nat.slice 0 3983 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice64 : Part6Nat.slice 0 3983 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice65 : Part6Nat.slice 0 3983 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice66 : Part6Nat.slice 0 3983 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice67 : Part6Nat.slice 0 3983 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice68 : Part6Nat.slice 0 3983 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice69 : Part6Nat.slice 0 3983 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice70 : Part6Nat.slice 0 3983 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice71 : Part6Nat.slice 0 3983 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice72 : Part6Nat.slice 0 3983 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice73 : Part6Nat.slice 0 3983 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice74 : Part6Nat.slice 0 3983 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice75 : Part6Nat.slice 0 3983 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice76 : Part6Nat.slice 0 3983 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice77 : Part6Nat.slice 0 3983 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice78 : Part6Nat.slice 0 3983 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice79 : Part6Nat.slice 0 3983 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice80 : Part6Nat.slice 0 3983 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice81 : Part6Nat.slice 0 3983 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice82 : Part6Nat.slice 0 3983 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice83 : Part6Nat.slice 0 3983 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice84 : Part6Nat.slice 0 3983 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice85 : Part6Nat.slice 0 3983 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice86 : Part6Nat.slice 0 3983 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice87 : Part6Nat.slice 0 3983 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice88 : Part6Nat.slice 0 3983 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice89 : Part6Nat.slice 0 3983 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice90 : Part6Nat.slice 0 3983 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice91 : Part6Nat.slice 0 3983 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice92 : Part6Nat.slice 0 3983 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice93 : Part6Nat.slice 0 3983 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice94 : Part6Nat.slice 0 3983 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice95 : Part6Nat.slice 0 3983 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice96 : Part6Nat.slice 0 3983 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice97 : Part6Nat.slice 0 3983 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice98 : Part6Nat.slice 0 3983 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice99 : Part6Nat.slice 0 3983 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice100 : Part6Nat.slice 0 3983 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice101 : Part6Nat.slice 0 3983 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice102 : Part6Nat.slice 0 3983 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice103 : Part6Nat.slice 0 3983 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice104 : Part6Nat.slice 0 3983 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice105 : Part6Nat.slice 0 3983 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice106 : Part6Nat.slice 0 3983 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice107 : Part6Nat.slice 0 3983 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice108 : Part6Nat.slice 0 3983 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice109 : Part6Nat.slice 0 3983 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice110 : Part6Nat.slice 0 3983 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice111 : Part6Nat.slice 0 3983 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice112 : Part6Nat.slice 0 3983 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice113 : Part6Nat.slice 0 3983 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice114 : Part6Nat.slice 0 3983 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice115 : Part6Nat.slice 0 3983 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice116 : Part6Nat.slice 0 3983 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice117 : Part6Nat.slice 0 3983 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice118 : Part6Nat.slice 0 3983 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice119 : Part6Nat.slice 0 3983 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice120 : Part6Nat.slice 0 3983 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice121 : Part6Nat.slice 0 3983 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice122 : Part6Nat.slice 0 3983 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice123 : Part6Nat.slice 0 3983 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice124 : Part6Nat.slice 0 3983 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice125 : Part6Nat.slice 0 3983 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice126 : Part6Nat.slice 0 3983 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice127 : Part6Nat.slice 0 3983 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice128 : Part6Nat.slice 0 3983 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice129 : Part6Nat.slice 0 3983 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice130 : Part6Nat.slice 0 3983 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice131 : Part6Nat.slice 0 3983 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice132 : Part6Nat.slice 0 3983 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice133 : Part6Nat.slice 0 3983 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice134 : Part6Nat.slice 0 3983 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice135 : Part6Nat.slice 0 3983 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice136 : Part6Nat.slice 0 3983 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice137 : Part6Nat.slice 0 3983 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice138 : Part6Nat.slice 0 3983 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice139 : Part6Nat.slice 0 3983 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice140 : Part6Nat.slice 0 3983 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice141 : Part6Nat.slice 0 3983 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice142 : Part6Nat.slice 0 3983 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice143 : Part6Nat.slice 0 3983 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice144 : Part6Nat.slice 0 3983 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice145 : Part6Nat.slice 0 3983 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice146 : Part6Nat.slice 0 3983 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice147 : Part6Nat.slice 0 3983 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice148 : Part6Nat.slice 0 3983 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice149 : Part6Nat.slice 0 3983 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice150 : Part6Nat.slice 0 3983 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice151 : Part6Nat.slice 0 3983 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice152 : Part6Nat.slice 0 3983 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice153 : Part6Nat.slice 0 3983 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice154 : Part6Nat.slice 0 3983 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice155 : Part6Nat.slice 0 3983 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice156 : Part6Nat.slice 0 3983 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice157 : Part6Nat.slice 0 3983 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice158 : Part6Nat.slice 0 3983 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice159 : Part6Nat.slice 0 3983 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice160 : Part6Nat.slice 0 3983 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice161 : Part6Nat.slice 0 3983 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice162 : Part6Nat.slice 0 3983 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice163 : Part6Nat.slice 0 3983 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice164 : Part6Nat.slice 0 3983 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice165 : Part6Nat.slice 0 3983 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice166 : Part6Nat.slice 0 3983 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice167 : Part6Nat.slice 0 3983 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice168 : Part6Nat.slice 0 3983 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice169 : Part6Nat.slice 0 3983 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice170 : Part6Nat.slice 0 3983 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice171 : Part6Nat.slice 0 3983 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice172 : Part6Nat.slice 0 3983 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice173 : Part6Nat.slice 0 3983 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice174 : Part6Nat.slice 0 3983 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice175 : Part6Nat.slice 0 3983 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice176 : Part6Nat.slice 0 3983 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice177 : Part6Nat.slice 0 3983 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice178 : Part6Nat.slice 0 3983 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice179 : Part6Nat.slice 0 3983 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice180 : Part6Nat.slice 0 3983 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice181 : Part6Nat.slice 0 3983 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice182 : Part6Nat.slice 0 3983 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice183 : Part6Nat.slice 0 3983 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice184 : Part6Nat.slice 0 3983 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice185 : Part6Nat.slice 0 3983 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice186 : Part6Nat.slice 0 3983 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice187 : Part6Nat.slice 0 3983 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice188 : Part6Nat.slice 0 3983 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice189 : Part6Nat.slice 0 3983 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice190 : Part6Nat.slice 0 3983 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice191 : Part6Nat.slice 0 3983 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice192 : Part6Nat.slice 0 3983 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice193 : Part6Nat.slice 0 3983 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice194 : Part6Nat.slice 0 3983 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice195 : Part6Nat.slice 0 3983 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice196 : Part6Nat.slice 0 3983 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice197 : Part6Nat.slice 0 3983 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice198 : Part6Nat.slice 0 3983 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice199 : Part6Nat.slice 0 3983 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice200 : Part6Nat.slice 0 3983 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice201 : Part6Nat.slice 0 3983 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point245slice202 : Part6Nat.slice 0 3983 202 = true := by
  decide +kernel

public theorem point245 : stepCheck 0 3983 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point245slice0
  · exact point245slice1
  · exact point245slice2
  · exact point245slice3
  · exact point245slice4
  · exact point245slice5
  · exact point245slice6
  · exact point245slice7
  · exact point245slice8
  · exact point245slice9
  · exact point245slice10
  · exact point245slice11
  · exact point245slice12
  · exact point245slice13
  · exact point245slice14
  · exact point245slice15
  · exact point245slice16
  · exact point245slice17
  · exact point245slice18
  · exact point245slice19
  · exact point245slice20
  · exact point245slice21
  · exact point245slice22
  · exact point245slice23
  · exact point245slice24
  · exact point245slice25
  · exact point245slice26
  · exact point245slice27
  · exact point245slice28
  · exact point245slice29
  · exact point245slice30
  · exact point245slice31
  · exact point245slice32
  · exact point245slice33
  · exact point245slice34
  · exact point245slice35
  · exact point245slice36
  · exact point245slice37
  · exact point245slice38
  · exact point245slice39
  · exact point245slice40
  · exact point245slice41
  · exact point245slice42
  · exact point245slice43
  · exact point245slice44
  · exact point245slice45
  · exact point245slice46
  · exact point245slice47
  · exact point245slice48
  · exact point245slice49
  · exact point245slice50
  · exact point245slice51
  · exact point245slice52
  · exact point245slice53
  · exact point245slice54
  · exact point245slice55
  · exact point245slice56
  · exact point245slice57
  · exact point245slice58
  · exact point245slice59
  · exact point245slice60
  · exact point245slice61
  · exact point245slice62
  · exact point245slice63
  · exact point245slice64
  · exact point245slice65
  · exact point245slice66
  · exact point245slice67
  · exact point245slice68
  · exact point245slice69
  · exact point245slice70
  · exact point245slice71
  · exact point245slice72
  · exact point245slice73
  · exact point245slice74
  · exact point245slice75
  · exact point245slice76
  · exact point245slice77
  · exact point245slice78
  · exact point245slice79
  · exact point245slice80
  · exact point245slice81
  · exact point245slice82
  · exact point245slice83
  · exact point245slice84
  · exact point245slice85
  · exact point245slice86
  · exact point245slice87
  · exact point245slice88
  · exact point245slice89
  · exact point245slice90
  · exact point245slice91
  · exact point245slice92
  · exact point245slice93
  · exact point245slice94
  · exact point245slice95
  · exact point245slice96
  · exact point245slice97
  · exact point245slice98
  · exact point245slice99
  · exact point245slice100
  · exact point245slice101
  · exact point245slice102
  · exact point245slice103
  · exact point245slice104
  · exact point245slice105
  · exact point245slice106
  · exact point245slice107
  · exact point245slice108
  · exact point245slice109
  · exact point245slice110
  · exact point245slice111
  · exact point245slice112
  · exact point245slice113
  · exact point245slice114
  · exact point245slice115
  · exact point245slice116
  · exact point245slice117
  · exact point245slice118
  · exact point245slice119
  · exact point245slice120
  · exact point245slice121
  · exact point245slice122
  · exact point245slice123
  · exact point245slice124
  · exact point245slice125
  · exact point245slice126
  · exact point245slice127
  · exact point245slice128
  · exact point245slice129
  · exact point245slice130
  · exact point245slice131
  · exact point245slice132
  · exact point245slice133
  · exact point245slice134
  · exact point245slice135
  · exact point245slice136
  · exact point245slice137
  · exact point245slice138
  · exact point245slice139
  · exact point245slice140
  · exact point245slice141
  · exact point245slice142
  · exact point245slice143
  · exact point245slice144
  · exact point245slice145
  · exact point245slice146
  · exact point245slice147
  · exact point245slice148
  · exact point245slice149
  · exact point245slice150
  · exact point245slice151
  · exact point245slice152
  · exact point245slice153
  · exact point245slice154
  · exact point245slice155
  · exact point245slice156
  · exact point245slice157
  · exact point245slice158
  · exact point245slice159
  · exact point245slice160
  · exact point245slice161
  · exact point245slice162
  · exact point245slice163
  · exact point245slice164
  · exact point245slice165
  · exact point245slice166
  · exact point245slice167
  · exact point245slice168
  · exact point245slice169
  · exact point245slice170
  · exact point245slice171
  · exact point245slice172
  · exact point245slice173
  · exact point245slice174
  · exact point245slice175
  · exact point245slice176
  · exact point245slice177
  · exact point245slice178
  · exact point245slice179
  · exact point245slice180
  · exact point245slice181
  · exact point245slice182
  · exact point245slice183
  · exact point245slice184
  · exact point245slice185
  · exact point245slice186
  · exact point245slice187
  · exact point245slice188
  · exact point245slice189
  · exact point245slice190
  · exact point245slice191
  · exact point245slice192
  · exact point245slice193
  · exact point245slice194
  · exact point245slice195
  · exact point245slice196
  · exact point245slice197
  · exact point245slice198
  · exact point245slice199
  · exact point245slice200
  · exact point245slice201
  · exact point245slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
