module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 260

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point260slice0 : Part6Nat.slice 0 3999 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice1 : Part6Nat.slice 0 3999 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice2 : Part6Nat.slice 0 3999 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice3 : Part6Nat.slice 0 3999 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice4 : Part6Nat.slice 0 3999 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice5 : Part6Nat.slice 0 3999 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice6 : Part6Nat.slice 0 3999 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice7 : Part6Nat.slice 0 3999 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice8 : Part6Nat.slice 0 3999 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice9 : Part6Nat.slice 0 3999 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice10 : Part6Nat.slice 0 3999 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice11 : Part6Nat.slice 0 3999 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice12 : Part6Nat.slice 0 3999 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice13 : Part6Nat.slice 0 3999 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice14 : Part6Nat.slice 0 3999 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice15 : Part6Nat.slice 0 3999 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice16 : Part6Nat.slice 0 3999 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice17 : Part6Nat.slice 0 3999 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice18 : Part6Nat.slice 0 3999 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice19 : Part6Nat.slice 0 3999 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice20 : Part6Nat.slice 0 3999 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice21 : Part6Nat.slice 0 3999 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice22 : Part6Nat.slice 0 3999 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice23 : Part6Nat.slice 0 3999 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice24 : Part6Nat.slice 0 3999 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice25 : Part6Nat.slice 0 3999 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice26 : Part6Nat.slice 0 3999 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice27 : Part6Nat.slice 0 3999 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice28 : Part6Nat.slice 0 3999 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice29 : Part6Nat.slice 0 3999 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice30 : Part6Nat.slice 0 3999 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice31 : Part6Nat.slice 0 3999 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice32 : Part6Nat.slice 0 3999 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice33 : Part6Nat.slice 0 3999 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice34 : Part6Nat.slice 0 3999 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice35 : Part6Nat.slice 0 3999 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice36 : Part6Nat.slice 0 3999 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice37 : Part6Nat.slice 0 3999 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice38 : Part6Nat.slice 0 3999 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice39 : Part6Nat.slice 0 3999 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice40 : Part6Nat.slice 0 3999 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice41 : Part6Nat.slice 0 3999 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice42 : Part6Nat.slice 0 3999 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice43 : Part6Nat.slice 0 3999 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice44 : Part6Nat.slice 0 3999 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice45 : Part6Nat.slice 0 3999 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice46 : Part6Nat.slice 0 3999 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice47 : Part6Nat.slice 0 3999 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice48 : Part6Nat.slice 0 3999 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice49 : Part6Nat.slice 0 3999 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice50 : Part6Nat.slice 0 3999 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice51 : Part6Nat.slice 0 3999 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice52 : Part6Nat.slice 0 3999 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice53 : Part6Nat.slice 0 3999 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice54 : Part6Nat.slice 0 3999 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice55 : Part6Nat.slice 0 3999 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice56 : Part6Nat.slice 0 3999 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice57 : Part6Nat.slice 0 3999 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice58 : Part6Nat.slice 0 3999 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice59 : Part6Nat.slice 0 3999 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice60 : Part6Nat.slice 0 3999 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice61 : Part6Nat.slice 0 3999 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice62 : Part6Nat.slice 0 3999 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice63 : Part6Nat.slice 0 3999 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice64 : Part6Nat.slice 0 3999 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice65 : Part6Nat.slice 0 3999 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice66 : Part6Nat.slice 0 3999 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice67 : Part6Nat.slice 0 3999 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice68 : Part6Nat.slice 0 3999 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice69 : Part6Nat.slice 0 3999 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice70 : Part6Nat.slice 0 3999 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice71 : Part6Nat.slice 0 3999 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice72 : Part6Nat.slice 0 3999 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice73 : Part6Nat.slice 0 3999 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice74 : Part6Nat.slice 0 3999 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice75 : Part6Nat.slice 0 3999 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice76 : Part6Nat.slice 0 3999 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice77 : Part6Nat.slice 0 3999 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice78 : Part6Nat.slice 0 3999 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice79 : Part6Nat.slice 0 3999 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice80 : Part6Nat.slice 0 3999 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice81 : Part6Nat.slice 0 3999 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice82 : Part6Nat.slice 0 3999 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice83 : Part6Nat.slice 0 3999 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice84 : Part6Nat.slice 0 3999 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice85 : Part6Nat.slice 0 3999 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice86 : Part6Nat.slice 0 3999 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice87 : Part6Nat.slice 0 3999 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice88 : Part6Nat.slice 0 3999 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice89 : Part6Nat.slice 0 3999 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice90 : Part6Nat.slice 0 3999 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice91 : Part6Nat.slice 0 3999 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice92 : Part6Nat.slice 0 3999 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice93 : Part6Nat.slice 0 3999 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice94 : Part6Nat.slice 0 3999 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice95 : Part6Nat.slice 0 3999 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice96 : Part6Nat.slice 0 3999 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice97 : Part6Nat.slice 0 3999 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice98 : Part6Nat.slice 0 3999 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice99 : Part6Nat.slice 0 3999 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice100 : Part6Nat.slice 0 3999 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice101 : Part6Nat.slice 0 3999 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice102 : Part6Nat.slice 0 3999 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice103 : Part6Nat.slice 0 3999 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice104 : Part6Nat.slice 0 3999 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice105 : Part6Nat.slice 0 3999 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice106 : Part6Nat.slice 0 3999 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice107 : Part6Nat.slice 0 3999 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice108 : Part6Nat.slice 0 3999 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice109 : Part6Nat.slice 0 3999 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice110 : Part6Nat.slice 0 3999 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice111 : Part6Nat.slice 0 3999 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice112 : Part6Nat.slice 0 3999 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice113 : Part6Nat.slice 0 3999 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice114 : Part6Nat.slice 0 3999 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice115 : Part6Nat.slice 0 3999 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice116 : Part6Nat.slice 0 3999 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice117 : Part6Nat.slice 0 3999 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice118 : Part6Nat.slice 0 3999 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice119 : Part6Nat.slice 0 3999 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice120 : Part6Nat.slice 0 3999 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice121 : Part6Nat.slice 0 3999 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice122 : Part6Nat.slice 0 3999 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice123 : Part6Nat.slice 0 3999 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice124 : Part6Nat.slice 0 3999 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice125 : Part6Nat.slice 0 3999 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice126 : Part6Nat.slice 0 3999 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice127 : Part6Nat.slice 0 3999 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice128 : Part6Nat.slice 0 3999 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice129 : Part6Nat.slice 0 3999 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice130 : Part6Nat.slice 0 3999 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice131 : Part6Nat.slice 0 3999 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice132 : Part6Nat.slice 0 3999 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice133 : Part6Nat.slice 0 3999 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice134 : Part6Nat.slice 0 3999 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice135 : Part6Nat.slice 0 3999 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice136 : Part6Nat.slice 0 3999 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice137 : Part6Nat.slice 0 3999 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice138 : Part6Nat.slice 0 3999 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice139 : Part6Nat.slice 0 3999 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice140 : Part6Nat.slice 0 3999 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice141 : Part6Nat.slice 0 3999 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice142 : Part6Nat.slice 0 3999 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice143 : Part6Nat.slice 0 3999 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice144 : Part6Nat.slice 0 3999 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice145 : Part6Nat.slice 0 3999 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice146 : Part6Nat.slice 0 3999 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice147 : Part6Nat.slice 0 3999 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice148 : Part6Nat.slice 0 3999 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice149 : Part6Nat.slice 0 3999 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice150 : Part6Nat.slice 0 3999 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice151 : Part6Nat.slice 0 3999 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice152 : Part6Nat.slice 0 3999 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice153 : Part6Nat.slice 0 3999 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice154 : Part6Nat.slice 0 3999 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice155 : Part6Nat.slice 0 3999 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice156 : Part6Nat.slice 0 3999 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice157 : Part6Nat.slice 0 3999 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice158 : Part6Nat.slice 0 3999 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice159 : Part6Nat.slice 0 3999 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice160 : Part6Nat.slice 0 3999 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice161 : Part6Nat.slice 0 3999 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice162 : Part6Nat.slice 0 3999 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice163 : Part6Nat.slice 0 3999 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice164 : Part6Nat.slice 0 3999 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice165 : Part6Nat.slice 0 3999 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice166 : Part6Nat.slice 0 3999 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice167 : Part6Nat.slice 0 3999 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice168 : Part6Nat.slice 0 3999 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice169 : Part6Nat.slice 0 3999 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice170 : Part6Nat.slice 0 3999 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice171 : Part6Nat.slice 0 3999 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice172 : Part6Nat.slice 0 3999 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice173 : Part6Nat.slice 0 3999 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice174 : Part6Nat.slice 0 3999 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice175 : Part6Nat.slice 0 3999 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice176 : Part6Nat.slice 0 3999 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice177 : Part6Nat.slice 0 3999 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice178 : Part6Nat.slice 0 3999 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice179 : Part6Nat.slice 0 3999 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice180 : Part6Nat.slice 0 3999 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice181 : Part6Nat.slice 0 3999 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice182 : Part6Nat.slice 0 3999 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice183 : Part6Nat.slice 0 3999 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice184 : Part6Nat.slice 0 3999 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice185 : Part6Nat.slice 0 3999 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice186 : Part6Nat.slice 0 3999 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice187 : Part6Nat.slice 0 3999 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice188 : Part6Nat.slice 0 3999 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice189 : Part6Nat.slice 0 3999 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice190 : Part6Nat.slice 0 3999 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice191 : Part6Nat.slice 0 3999 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice192 : Part6Nat.slice 0 3999 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice193 : Part6Nat.slice 0 3999 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice194 : Part6Nat.slice 0 3999 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice195 : Part6Nat.slice 0 3999 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice196 : Part6Nat.slice 0 3999 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice197 : Part6Nat.slice 0 3999 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice198 : Part6Nat.slice 0 3999 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice199 : Part6Nat.slice 0 3999 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice200 : Part6Nat.slice 0 3999 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice201 : Part6Nat.slice 0 3999 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point260slice202 : Part6Nat.slice 0 3999 202 = true := by
  decide +kernel

public theorem point260 : stepCheck 0 3999 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point260slice0
  · exact point260slice1
  · exact point260slice2
  · exact point260slice3
  · exact point260slice4
  · exact point260slice5
  · exact point260slice6
  · exact point260slice7
  · exact point260slice8
  · exact point260slice9
  · exact point260slice10
  · exact point260slice11
  · exact point260slice12
  · exact point260slice13
  · exact point260slice14
  · exact point260slice15
  · exact point260slice16
  · exact point260slice17
  · exact point260slice18
  · exact point260slice19
  · exact point260slice20
  · exact point260slice21
  · exact point260slice22
  · exact point260slice23
  · exact point260slice24
  · exact point260slice25
  · exact point260slice26
  · exact point260slice27
  · exact point260slice28
  · exact point260slice29
  · exact point260slice30
  · exact point260slice31
  · exact point260slice32
  · exact point260slice33
  · exact point260slice34
  · exact point260slice35
  · exact point260slice36
  · exact point260slice37
  · exact point260slice38
  · exact point260slice39
  · exact point260slice40
  · exact point260slice41
  · exact point260slice42
  · exact point260slice43
  · exact point260slice44
  · exact point260slice45
  · exact point260slice46
  · exact point260slice47
  · exact point260slice48
  · exact point260slice49
  · exact point260slice50
  · exact point260slice51
  · exact point260slice52
  · exact point260slice53
  · exact point260slice54
  · exact point260slice55
  · exact point260slice56
  · exact point260slice57
  · exact point260slice58
  · exact point260slice59
  · exact point260slice60
  · exact point260slice61
  · exact point260slice62
  · exact point260slice63
  · exact point260slice64
  · exact point260slice65
  · exact point260slice66
  · exact point260slice67
  · exact point260slice68
  · exact point260slice69
  · exact point260slice70
  · exact point260slice71
  · exact point260slice72
  · exact point260slice73
  · exact point260slice74
  · exact point260slice75
  · exact point260slice76
  · exact point260slice77
  · exact point260slice78
  · exact point260slice79
  · exact point260slice80
  · exact point260slice81
  · exact point260slice82
  · exact point260slice83
  · exact point260slice84
  · exact point260slice85
  · exact point260slice86
  · exact point260slice87
  · exact point260slice88
  · exact point260slice89
  · exact point260slice90
  · exact point260slice91
  · exact point260slice92
  · exact point260slice93
  · exact point260slice94
  · exact point260slice95
  · exact point260slice96
  · exact point260slice97
  · exact point260slice98
  · exact point260slice99
  · exact point260slice100
  · exact point260slice101
  · exact point260slice102
  · exact point260slice103
  · exact point260slice104
  · exact point260slice105
  · exact point260slice106
  · exact point260slice107
  · exact point260slice108
  · exact point260slice109
  · exact point260slice110
  · exact point260slice111
  · exact point260slice112
  · exact point260slice113
  · exact point260slice114
  · exact point260slice115
  · exact point260slice116
  · exact point260slice117
  · exact point260slice118
  · exact point260slice119
  · exact point260slice120
  · exact point260slice121
  · exact point260slice122
  · exact point260slice123
  · exact point260slice124
  · exact point260slice125
  · exact point260slice126
  · exact point260slice127
  · exact point260slice128
  · exact point260slice129
  · exact point260slice130
  · exact point260slice131
  · exact point260slice132
  · exact point260slice133
  · exact point260slice134
  · exact point260slice135
  · exact point260slice136
  · exact point260slice137
  · exact point260slice138
  · exact point260slice139
  · exact point260slice140
  · exact point260slice141
  · exact point260slice142
  · exact point260slice143
  · exact point260slice144
  · exact point260slice145
  · exact point260slice146
  · exact point260slice147
  · exact point260slice148
  · exact point260slice149
  · exact point260slice150
  · exact point260slice151
  · exact point260slice152
  · exact point260slice153
  · exact point260slice154
  · exact point260slice155
  · exact point260slice156
  · exact point260slice157
  · exact point260slice158
  · exact point260slice159
  · exact point260slice160
  · exact point260slice161
  · exact point260slice162
  · exact point260slice163
  · exact point260slice164
  · exact point260slice165
  · exact point260slice166
  · exact point260slice167
  · exact point260slice168
  · exact point260slice169
  · exact point260slice170
  · exact point260slice171
  · exact point260slice172
  · exact point260slice173
  · exact point260slice174
  · exact point260slice175
  · exact point260slice176
  · exact point260slice177
  · exact point260slice178
  · exact point260slice179
  · exact point260slice180
  · exact point260slice181
  · exact point260slice182
  · exact point260slice183
  · exact point260slice184
  · exact point260slice185
  · exact point260slice186
  · exact point260slice187
  · exact point260slice188
  · exact point260slice189
  · exact point260slice190
  · exact point260slice191
  · exact point260slice192
  · exact point260slice193
  · exact point260slice194
  · exact point260slice195
  · exact point260slice196
  · exact point260slice197
  · exact point260slice198
  · exact point260slice199
  · exact point260slice200
  · exact point260slice201
  · exact point260slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
