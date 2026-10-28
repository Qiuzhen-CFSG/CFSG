module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 270

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point270slice0 : Part6Nat.slice 1 3999 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice1 : Part6Nat.slice 1 3999 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice2 : Part6Nat.slice 1 3999 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice3 : Part6Nat.slice 1 3999 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice4 : Part6Nat.slice 1 3999 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice5 : Part6Nat.slice 1 3999 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice6 : Part6Nat.slice 1 3999 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice7 : Part6Nat.slice 1 3999 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice8 : Part6Nat.slice 1 3999 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice9 : Part6Nat.slice 1 3999 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice10 : Part6Nat.slice 1 3999 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice11 : Part6Nat.slice 1 3999 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice12 : Part6Nat.slice 1 3999 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice13 : Part6Nat.slice 1 3999 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice14 : Part6Nat.slice 1 3999 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice15 : Part6Nat.slice 1 3999 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice16 : Part6Nat.slice 1 3999 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice17 : Part6Nat.slice 1 3999 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice18 : Part6Nat.slice 1 3999 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice19 : Part6Nat.slice 1 3999 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice20 : Part6Nat.slice 1 3999 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice21 : Part6Nat.slice 1 3999 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice22 : Part6Nat.slice 1 3999 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice23 : Part6Nat.slice 1 3999 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice24 : Part6Nat.slice 1 3999 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice25 : Part6Nat.slice 1 3999 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice26 : Part6Nat.slice 1 3999 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice27 : Part6Nat.slice 1 3999 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice28 : Part6Nat.slice 1 3999 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice29 : Part6Nat.slice 1 3999 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice30 : Part6Nat.slice 1 3999 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice31 : Part6Nat.slice 1 3999 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice32 : Part6Nat.slice 1 3999 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice33 : Part6Nat.slice 1 3999 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice34 : Part6Nat.slice 1 3999 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice35 : Part6Nat.slice 1 3999 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice36 : Part6Nat.slice 1 3999 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice37 : Part6Nat.slice 1 3999 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice38 : Part6Nat.slice 1 3999 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice39 : Part6Nat.slice 1 3999 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice40 : Part6Nat.slice 1 3999 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice41 : Part6Nat.slice 1 3999 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice42 : Part6Nat.slice 1 3999 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice43 : Part6Nat.slice 1 3999 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice44 : Part6Nat.slice 1 3999 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice45 : Part6Nat.slice 1 3999 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice46 : Part6Nat.slice 1 3999 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice47 : Part6Nat.slice 1 3999 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice48 : Part6Nat.slice 1 3999 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice49 : Part6Nat.slice 1 3999 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice50 : Part6Nat.slice 1 3999 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice51 : Part6Nat.slice 1 3999 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice52 : Part6Nat.slice 1 3999 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice53 : Part6Nat.slice 1 3999 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice54 : Part6Nat.slice 1 3999 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice55 : Part6Nat.slice 1 3999 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice56 : Part6Nat.slice 1 3999 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice57 : Part6Nat.slice 1 3999 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice58 : Part6Nat.slice 1 3999 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice59 : Part6Nat.slice 1 3999 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice60 : Part6Nat.slice 1 3999 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice61 : Part6Nat.slice 1 3999 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice62 : Part6Nat.slice 1 3999 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice63 : Part6Nat.slice 1 3999 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice64 : Part6Nat.slice 1 3999 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice65 : Part6Nat.slice 1 3999 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice66 : Part6Nat.slice 1 3999 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice67 : Part6Nat.slice 1 3999 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice68 : Part6Nat.slice 1 3999 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice69 : Part6Nat.slice 1 3999 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice70 : Part6Nat.slice 1 3999 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice71 : Part6Nat.slice 1 3999 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice72 : Part6Nat.slice 1 3999 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice73 : Part6Nat.slice 1 3999 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice74 : Part6Nat.slice 1 3999 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice75 : Part6Nat.slice 1 3999 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice76 : Part6Nat.slice 1 3999 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice77 : Part6Nat.slice 1 3999 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice78 : Part6Nat.slice 1 3999 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice79 : Part6Nat.slice 1 3999 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice80 : Part6Nat.slice 1 3999 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice81 : Part6Nat.slice 1 3999 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice82 : Part6Nat.slice 1 3999 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice83 : Part6Nat.slice 1 3999 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice84 : Part6Nat.slice 1 3999 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice85 : Part6Nat.slice 1 3999 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice86 : Part6Nat.slice 1 3999 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice87 : Part6Nat.slice 1 3999 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice88 : Part6Nat.slice 1 3999 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice89 : Part6Nat.slice 1 3999 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice90 : Part6Nat.slice 1 3999 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice91 : Part6Nat.slice 1 3999 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice92 : Part6Nat.slice 1 3999 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice93 : Part6Nat.slice 1 3999 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice94 : Part6Nat.slice 1 3999 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice95 : Part6Nat.slice 1 3999 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice96 : Part6Nat.slice 1 3999 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice97 : Part6Nat.slice 1 3999 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice98 : Part6Nat.slice 1 3999 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice99 : Part6Nat.slice 1 3999 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice100 : Part6Nat.slice 1 3999 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice101 : Part6Nat.slice 1 3999 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice102 : Part6Nat.slice 1 3999 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice103 : Part6Nat.slice 1 3999 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice104 : Part6Nat.slice 1 3999 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice105 : Part6Nat.slice 1 3999 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice106 : Part6Nat.slice 1 3999 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice107 : Part6Nat.slice 1 3999 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice108 : Part6Nat.slice 1 3999 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice109 : Part6Nat.slice 1 3999 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice110 : Part6Nat.slice 1 3999 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice111 : Part6Nat.slice 1 3999 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice112 : Part6Nat.slice 1 3999 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice113 : Part6Nat.slice 1 3999 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice114 : Part6Nat.slice 1 3999 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice115 : Part6Nat.slice 1 3999 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice116 : Part6Nat.slice 1 3999 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice117 : Part6Nat.slice 1 3999 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice118 : Part6Nat.slice 1 3999 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice119 : Part6Nat.slice 1 3999 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice120 : Part6Nat.slice 1 3999 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice121 : Part6Nat.slice 1 3999 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice122 : Part6Nat.slice 1 3999 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice123 : Part6Nat.slice 1 3999 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice124 : Part6Nat.slice 1 3999 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice125 : Part6Nat.slice 1 3999 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice126 : Part6Nat.slice 1 3999 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice127 : Part6Nat.slice 1 3999 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice128 : Part6Nat.slice 1 3999 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice129 : Part6Nat.slice 1 3999 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice130 : Part6Nat.slice 1 3999 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice131 : Part6Nat.slice 1 3999 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice132 : Part6Nat.slice 1 3999 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice133 : Part6Nat.slice 1 3999 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice134 : Part6Nat.slice 1 3999 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice135 : Part6Nat.slice 1 3999 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice136 : Part6Nat.slice 1 3999 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice137 : Part6Nat.slice 1 3999 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice138 : Part6Nat.slice 1 3999 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice139 : Part6Nat.slice 1 3999 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice140 : Part6Nat.slice 1 3999 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice141 : Part6Nat.slice 1 3999 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice142 : Part6Nat.slice 1 3999 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice143 : Part6Nat.slice 1 3999 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice144 : Part6Nat.slice 1 3999 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice145 : Part6Nat.slice 1 3999 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice146 : Part6Nat.slice 1 3999 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice147 : Part6Nat.slice 1 3999 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice148 : Part6Nat.slice 1 3999 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice149 : Part6Nat.slice 1 3999 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice150 : Part6Nat.slice 1 3999 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice151 : Part6Nat.slice 1 3999 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice152 : Part6Nat.slice 1 3999 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice153 : Part6Nat.slice 1 3999 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice154 : Part6Nat.slice 1 3999 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice155 : Part6Nat.slice 1 3999 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice156 : Part6Nat.slice 1 3999 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice157 : Part6Nat.slice 1 3999 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice158 : Part6Nat.slice 1 3999 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice159 : Part6Nat.slice 1 3999 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice160 : Part6Nat.slice 1 3999 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice161 : Part6Nat.slice 1 3999 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice162 : Part6Nat.slice 1 3999 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice163 : Part6Nat.slice 1 3999 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice164 : Part6Nat.slice 1 3999 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice165 : Part6Nat.slice 1 3999 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice166 : Part6Nat.slice 1 3999 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice167 : Part6Nat.slice 1 3999 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice168 : Part6Nat.slice 1 3999 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice169 : Part6Nat.slice 1 3999 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice170 : Part6Nat.slice 1 3999 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice171 : Part6Nat.slice 1 3999 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice172 : Part6Nat.slice 1 3999 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice173 : Part6Nat.slice 1 3999 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice174 : Part6Nat.slice 1 3999 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice175 : Part6Nat.slice 1 3999 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice176 : Part6Nat.slice 1 3999 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice177 : Part6Nat.slice 1 3999 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice178 : Part6Nat.slice 1 3999 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice179 : Part6Nat.slice 1 3999 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice180 : Part6Nat.slice 1 3999 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice181 : Part6Nat.slice 1 3999 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice182 : Part6Nat.slice 1 3999 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice183 : Part6Nat.slice 1 3999 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice184 : Part6Nat.slice 1 3999 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice185 : Part6Nat.slice 1 3999 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice186 : Part6Nat.slice 1 3999 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice187 : Part6Nat.slice 1 3999 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice188 : Part6Nat.slice 1 3999 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice189 : Part6Nat.slice 1 3999 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice190 : Part6Nat.slice 1 3999 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice191 : Part6Nat.slice 1 3999 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice192 : Part6Nat.slice 1 3999 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice193 : Part6Nat.slice 1 3999 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice194 : Part6Nat.slice 1 3999 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice195 : Part6Nat.slice 1 3999 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice196 : Part6Nat.slice 1 3999 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice197 : Part6Nat.slice 1 3999 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice198 : Part6Nat.slice 1 3999 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice199 : Part6Nat.slice 1 3999 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice200 : Part6Nat.slice 1 3999 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice201 : Part6Nat.slice 1 3999 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point270slice202 : Part6Nat.slice 1 3999 202 = true := by
  decide +kernel

public theorem point270 : stepCheck 1 3999 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point270slice0
  · exact point270slice1
  · exact point270slice2
  · exact point270slice3
  · exact point270slice4
  · exact point270slice5
  · exact point270slice6
  · exact point270slice7
  · exact point270slice8
  · exact point270slice9
  · exact point270slice10
  · exact point270slice11
  · exact point270slice12
  · exact point270slice13
  · exact point270slice14
  · exact point270slice15
  · exact point270slice16
  · exact point270slice17
  · exact point270slice18
  · exact point270slice19
  · exact point270slice20
  · exact point270slice21
  · exact point270slice22
  · exact point270slice23
  · exact point270slice24
  · exact point270slice25
  · exact point270slice26
  · exact point270slice27
  · exact point270slice28
  · exact point270slice29
  · exact point270slice30
  · exact point270slice31
  · exact point270slice32
  · exact point270slice33
  · exact point270slice34
  · exact point270slice35
  · exact point270slice36
  · exact point270slice37
  · exact point270slice38
  · exact point270slice39
  · exact point270slice40
  · exact point270slice41
  · exact point270slice42
  · exact point270slice43
  · exact point270slice44
  · exact point270slice45
  · exact point270slice46
  · exact point270slice47
  · exact point270slice48
  · exact point270slice49
  · exact point270slice50
  · exact point270slice51
  · exact point270slice52
  · exact point270slice53
  · exact point270slice54
  · exact point270slice55
  · exact point270slice56
  · exact point270slice57
  · exact point270slice58
  · exact point270slice59
  · exact point270slice60
  · exact point270slice61
  · exact point270slice62
  · exact point270slice63
  · exact point270slice64
  · exact point270slice65
  · exact point270slice66
  · exact point270slice67
  · exact point270slice68
  · exact point270slice69
  · exact point270slice70
  · exact point270slice71
  · exact point270slice72
  · exact point270slice73
  · exact point270slice74
  · exact point270slice75
  · exact point270slice76
  · exact point270slice77
  · exact point270slice78
  · exact point270slice79
  · exact point270slice80
  · exact point270slice81
  · exact point270slice82
  · exact point270slice83
  · exact point270slice84
  · exact point270slice85
  · exact point270slice86
  · exact point270slice87
  · exact point270slice88
  · exact point270slice89
  · exact point270slice90
  · exact point270slice91
  · exact point270slice92
  · exact point270slice93
  · exact point270slice94
  · exact point270slice95
  · exact point270slice96
  · exact point270slice97
  · exact point270slice98
  · exact point270slice99
  · exact point270slice100
  · exact point270slice101
  · exact point270slice102
  · exact point270slice103
  · exact point270slice104
  · exact point270slice105
  · exact point270slice106
  · exact point270slice107
  · exact point270slice108
  · exact point270slice109
  · exact point270slice110
  · exact point270slice111
  · exact point270slice112
  · exact point270slice113
  · exact point270slice114
  · exact point270slice115
  · exact point270slice116
  · exact point270slice117
  · exact point270slice118
  · exact point270slice119
  · exact point270slice120
  · exact point270slice121
  · exact point270slice122
  · exact point270slice123
  · exact point270slice124
  · exact point270slice125
  · exact point270slice126
  · exact point270slice127
  · exact point270slice128
  · exact point270slice129
  · exact point270slice130
  · exact point270slice131
  · exact point270slice132
  · exact point270slice133
  · exact point270slice134
  · exact point270slice135
  · exact point270slice136
  · exact point270slice137
  · exact point270slice138
  · exact point270slice139
  · exact point270slice140
  · exact point270slice141
  · exact point270slice142
  · exact point270slice143
  · exact point270slice144
  · exact point270slice145
  · exact point270slice146
  · exact point270slice147
  · exact point270slice148
  · exact point270slice149
  · exact point270slice150
  · exact point270slice151
  · exact point270slice152
  · exact point270slice153
  · exact point270slice154
  · exact point270slice155
  · exact point270slice156
  · exact point270slice157
  · exact point270slice158
  · exact point270slice159
  · exact point270slice160
  · exact point270slice161
  · exact point270slice162
  · exact point270slice163
  · exact point270slice164
  · exact point270slice165
  · exact point270slice166
  · exact point270slice167
  · exact point270slice168
  · exact point270slice169
  · exact point270slice170
  · exact point270slice171
  · exact point270slice172
  · exact point270slice173
  · exact point270slice174
  · exact point270slice175
  · exact point270slice176
  · exact point270slice177
  · exact point270slice178
  · exact point270slice179
  · exact point270slice180
  · exact point270slice181
  · exact point270slice182
  · exact point270slice183
  · exact point270slice184
  · exact point270slice185
  · exact point270slice186
  · exact point270slice187
  · exact point270slice188
  · exact point270slice189
  · exact point270slice190
  · exact point270slice191
  · exact point270slice192
  · exact point270slice193
  · exact point270slice194
  · exact point270slice195
  · exact point270slice196
  · exact point270slice197
  · exact point270slice198
  · exact point270slice199
  · exact point270slice200
  · exact point270slice201
  · exact point270slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
