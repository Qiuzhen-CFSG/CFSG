module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 240

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point240slice0 : Part6Nat.slice 1 3853 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice1 : Part6Nat.slice 1 3853 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice2 : Part6Nat.slice 1 3853 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice3 : Part6Nat.slice 1 3853 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice4 : Part6Nat.slice 1 3853 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice5 : Part6Nat.slice 1 3853 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice6 : Part6Nat.slice 1 3853 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice7 : Part6Nat.slice 1 3853 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice8 : Part6Nat.slice 1 3853 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice9 : Part6Nat.slice 1 3853 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice10 : Part6Nat.slice 1 3853 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice11 : Part6Nat.slice 1 3853 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice12 : Part6Nat.slice 1 3853 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice13 : Part6Nat.slice 1 3853 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice14 : Part6Nat.slice 1 3853 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice15 : Part6Nat.slice 1 3853 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice16 : Part6Nat.slice 1 3853 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice17 : Part6Nat.slice 1 3853 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice18 : Part6Nat.slice 1 3853 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice19 : Part6Nat.slice 1 3853 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice20 : Part6Nat.slice 1 3853 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice21 : Part6Nat.slice 1 3853 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice22 : Part6Nat.slice 1 3853 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice23 : Part6Nat.slice 1 3853 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice24 : Part6Nat.slice 1 3853 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice25 : Part6Nat.slice 1 3853 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice26 : Part6Nat.slice 1 3853 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice27 : Part6Nat.slice 1 3853 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice28 : Part6Nat.slice 1 3853 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice29 : Part6Nat.slice 1 3853 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice30 : Part6Nat.slice 1 3853 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice31 : Part6Nat.slice 1 3853 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice32 : Part6Nat.slice 1 3853 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice33 : Part6Nat.slice 1 3853 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice34 : Part6Nat.slice 1 3853 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice35 : Part6Nat.slice 1 3853 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice36 : Part6Nat.slice 1 3853 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice37 : Part6Nat.slice 1 3853 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice38 : Part6Nat.slice 1 3853 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice39 : Part6Nat.slice 1 3853 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice40 : Part6Nat.slice 1 3853 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice41 : Part6Nat.slice 1 3853 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice42 : Part6Nat.slice 1 3853 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice43 : Part6Nat.slice 1 3853 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice44 : Part6Nat.slice 1 3853 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice45 : Part6Nat.slice 1 3853 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice46 : Part6Nat.slice 1 3853 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice47 : Part6Nat.slice 1 3853 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice48 : Part6Nat.slice 1 3853 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice49 : Part6Nat.slice 1 3853 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice50 : Part6Nat.slice 1 3853 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice51 : Part6Nat.slice 1 3853 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice52 : Part6Nat.slice 1 3853 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice53 : Part6Nat.slice 1 3853 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice54 : Part6Nat.slice 1 3853 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice55 : Part6Nat.slice 1 3853 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice56 : Part6Nat.slice 1 3853 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice57 : Part6Nat.slice 1 3853 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice58 : Part6Nat.slice 1 3853 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice59 : Part6Nat.slice 1 3853 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice60 : Part6Nat.slice 1 3853 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice61 : Part6Nat.slice 1 3853 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice62 : Part6Nat.slice 1 3853 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice63 : Part6Nat.slice 1 3853 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice64 : Part6Nat.slice 1 3853 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice65 : Part6Nat.slice 1 3853 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice66 : Part6Nat.slice 1 3853 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice67 : Part6Nat.slice 1 3853 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice68 : Part6Nat.slice 1 3853 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice69 : Part6Nat.slice 1 3853 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice70 : Part6Nat.slice 1 3853 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice71 : Part6Nat.slice 1 3853 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice72 : Part6Nat.slice 1 3853 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice73 : Part6Nat.slice 1 3853 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice74 : Part6Nat.slice 1 3853 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice75 : Part6Nat.slice 1 3853 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice76 : Part6Nat.slice 1 3853 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice77 : Part6Nat.slice 1 3853 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice78 : Part6Nat.slice 1 3853 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice79 : Part6Nat.slice 1 3853 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice80 : Part6Nat.slice 1 3853 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice81 : Part6Nat.slice 1 3853 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice82 : Part6Nat.slice 1 3853 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice83 : Part6Nat.slice 1 3853 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice84 : Part6Nat.slice 1 3853 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice85 : Part6Nat.slice 1 3853 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice86 : Part6Nat.slice 1 3853 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice87 : Part6Nat.slice 1 3853 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice88 : Part6Nat.slice 1 3853 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice89 : Part6Nat.slice 1 3853 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice90 : Part6Nat.slice 1 3853 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice91 : Part6Nat.slice 1 3853 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice92 : Part6Nat.slice 1 3853 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice93 : Part6Nat.slice 1 3853 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice94 : Part6Nat.slice 1 3853 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice95 : Part6Nat.slice 1 3853 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice96 : Part6Nat.slice 1 3853 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice97 : Part6Nat.slice 1 3853 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice98 : Part6Nat.slice 1 3853 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice99 : Part6Nat.slice 1 3853 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice100 : Part6Nat.slice 1 3853 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice101 : Part6Nat.slice 1 3853 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice102 : Part6Nat.slice 1 3853 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice103 : Part6Nat.slice 1 3853 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice104 : Part6Nat.slice 1 3853 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice105 : Part6Nat.slice 1 3853 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice106 : Part6Nat.slice 1 3853 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice107 : Part6Nat.slice 1 3853 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice108 : Part6Nat.slice 1 3853 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice109 : Part6Nat.slice 1 3853 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice110 : Part6Nat.slice 1 3853 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice111 : Part6Nat.slice 1 3853 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice112 : Part6Nat.slice 1 3853 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice113 : Part6Nat.slice 1 3853 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice114 : Part6Nat.slice 1 3853 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice115 : Part6Nat.slice 1 3853 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice116 : Part6Nat.slice 1 3853 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice117 : Part6Nat.slice 1 3853 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice118 : Part6Nat.slice 1 3853 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice119 : Part6Nat.slice 1 3853 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice120 : Part6Nat.slice 1 3853 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice121 : Part6Nat.slice 1 3853 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice122 : Part6Nat.slice 1 3853 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice123 : Part6Nat.slice 1 3853 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice124 : Part6Nat.slice 1 3853 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice125 : Part6Nat.slice 1 3853 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice126 : Part6Nat.slice 1 3853 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice127 : Part6Nat.slice 1 3853 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice128 : Part6Nat.slice 1 3853 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice129 : Part6Nat.slice 1 3853 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice130 : Part6Nat.slice 1 3853 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice131 : Part6Nat.slice 1 3853 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice132 : Part6Nat.slice 1 3853 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice133 : Part6Nat.slice 1 3853 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice134 : Part6Nat.slice 1 3853 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice135 : Part6Nat.slice 1 3853 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice136 : Part6Nat.slice 1 3853 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice137 : Part6Nat.slice 1 3853 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice138 : Part6Nat.slice 1 3853 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice139 : Part6Nat.slice 1 3853 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice140 : Part6Nat.slice 1 3853 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice141 : Part6Nat.slice 1 3853 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice142 : Part6Nat.slice 1 3853 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice143 : Part6Nat.slice 1 3853 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice144 : Part6Nat.slice 1 3853 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice145 : Part6Nat.slice 1 3853 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice146 : Part6Nat.slice 1 3853 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice147 : Part6Nat.slice 1 3853 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice148 : Part6Nat.slice 1 3853 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice149 : Part6Nat.slice 1 3853 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice150 : Part6Nat.slice 1 3853 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice151 : Part6Nat.slice 1 3853 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice152 : Part6Nat.slice 1 3853 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice153 : Part6Nat.slice 1 3853 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice154 : Part6Nat.slice 1 3853 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice155 : Part6Nat.slice 1 3853 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice156 : Part6Nat.slice 1 3853 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice157 : Part6Nat.slice 1 3853 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice158 : Part6Nat.slice 1 3853 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice159 : Part6Nat.slice 1 3853 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice160 : Part6Nat.slice 1 3853 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice161 : Part6Nat.slice 1 3853 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice162 : Part6Nat.slice 1 3853 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice163 : Part6Nat.slice 1 3853 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice164 : Part6Nat.slice 1 3853 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice165 : Part6Nat.slice 1 3853 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice166 : Part6Nat.slice 1 3853 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice167 : Part6Nat.slice 1 3853 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice168 : Part6Nat.slice 1 3853 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice169 : Part6Nat.slice 1 3853 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice170 : Part6Nat.slice 1 3853 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice171 : Part6Nat.slice 1 3853 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice172 : Part6Nat.slice 1 3853 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice173 : Part6Nat.slice 1 3853 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice174 : Part6Nat.slice 1 3853 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice175 : Part6Nat.slice 1 3853 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice176 : Part6Nat.slice 1 3853 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice177 : Part6Nat.slice 1 3853 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice178 : Part6Nat.slice 1 3853 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice179 : Part6Nat.slice 1 3853 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice180 : Part6Nat.slice 1 3853 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice181 : Part6Nat.slice 1 3853 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice182 : Part6Nat.slice 1 3853 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice183 : Part6Nat.slice 1 3853 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice184 : Part6Nat.slice 1 3853 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice185 : Part6Nat.slice 1 3853 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice186 : Part6Nat.slice 1 3853 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice187 : Part6Nat.slice 1 3853 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice188 : Part6Nat.slice 1 3853 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice189 : Part6Nat.slice 1 3853 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice190 : Part6Nat.slice 1 3853 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice191 : Part6Nat.slice 1 3853 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice192 : Part6Nat.slice 1 3853 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice193 : Part6Nat.slice 1 3853 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice194 : Part6Nat.slice 1 3853 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice195 : Part6Nat.slice 1 3853 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice196 : Part6Nat.slice 1 3853 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice197 : Part6Nat.slice 1 3853 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice198 : Part6Nat.slice 1 3853 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice199 : Part6Nat.slice 1 3853 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice200 : Part6Nat.slice 1 3853 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice201 : Part6Nat.slice 1 3853 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point240slice202 : Part6Nat.slice 1 3853 202 = true := by
  decide +kernel

public theorem point240 : stepCheck 1 3853 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point240slice0
  · exact point240slice1
  · exact point240slice2
  · exact point240slice3
  · exact point240slice4
  · exact point240slice5
  · exact point240slice6
  · exact point240slice7
  · exact point240slice8
  · exact point240slice9
  · exact point240slice10
  · exact point240slice11
  · exact point240slice12
  · exact point240slice13
  · exact point240slice14
  · exact point240slice15
  · exact point240slice16
  · exact point240slice17
  · exact point240slice18
  · exact point240slice19
  · exact point240slice20
  · exact point240slice21
  · exact point240slice22
  · exact point240slice23
  · exact point240slice24
  · exact point240slice25
  · exact point240slice26
  · exact point240slice27
  · exact point240slice28
  · exact point240slice29
  · exact point240slice30
  · exact point240slice31
  · exact point240slice32
  · exact point240slice33
  · exact point240slice34
  · exact point240slice35
  · exact point240slice36
  · exact point240slice37
  · exact point240slice38
  · exact point240slice39
  · exact point240slice40
  · exact point240slice41
  · exact point240slice42
  · exact point240slice43
  · exact point240slice44
  · exact point240slice45
  · exact point240slice46
  · exact point240slice47
  · exact point240slice48
  · exact point240slice49
  · exact point240slice50
  · exact point240slice51
  · exact point240slice52
  · exact point240slice53
  · exact point240slice54
  · exact point240slice55
  · exact point240slice56
  · exact point240slice57
  · exact point240slice58
  · exact point240slice59
  · exact point240slice60
  · exact point240slice61
  · exact point240slice62
  · exact point240slice63
  · exact point240slice64
  · exact point240slice65
  · exact point240slice66
  · exact point240slice67
  · exact point240slice68
  · exact point240slice69
  · exact point240slice70
  · exact point240slice71
  · exact point240slice72
  · exact point240slice73
  · exact point240slice74
  · exact point240slice75
  · exact point240slice76
  · exact point240slice77
  · exact point240slice78
  · exact point240slice79
  · exact point240slice80
  · exact point240slice81
  · exact point240slice82
  · exact point240slice83
  · exact point240slice84
  · exact point240slice85
  · exact point240slice86
  · exact point240slice87
  · exact point240slice88
  · exact point240slice89
  · exact point240slice90
  · exact point240slice91
  · exact point240slice92
  · exact point240slice93
  · exact point240slice94
  · exact point240slice95
  · exact point240slice96
  · exact point240slice97
  · exact point240slice98
  · exact point240slice99
  · exact point240slice100
  · exact point240slice101
  · exact point240slice102
  · exact point240slice103
  · exact point240slice104
  · exact point240slice105
  · exact point240slice106
  · exact point240slice107
  · exact point240slice108
  · exact point240slice109
  · exact point240slice110
  · exact point240slice111
  · exact point240slice112
  · exact point240slice113
  · exact point240slice114
  · exact point240slice115
  · exact point240slice116
  · exact point240slice117
  · exact point240slice118
  · exact point240slice119
  · exact point240slice120
  · exact point240slice121
  · exact point240slice122
  · exact point240slice123
  · exact point240slice124
  · exact point240slice125
  · exact point240slice126
  · exact point240slice127
  · exact point240slice128
  · exact point240slice129
  · exact point240slice130
  · exact point240slice131
  · exact point240slice132
  · exact point240slice133
  · exact point240slice134
  · exact point240slice135
  · exact point240slice136
  · exact point240slice137
  · exact point240slice138
  · exact point240slice139
  · exact point240slice140
  · exact point240slice141
  · exact point240slice142
  · exact point240slice143
  · exact point240slice144
  · exact point240slice145
  · exact point240slice146
  · exact point240slice147
  · exact point240slice148
  · exact point240slice149
  · exact point240slice150
  · exact point240slice151
  · exact point240slice152
  · exact point240slice153
  · exact point240slice154
  · exact point240slice155
  · exact point240slice156
  · exact point240slice157
  · exact point240slice158
  · exact point240slice159
  · exact point240slice160
  · exact point240slice161
  · exact point240slice162
  · exact point240slice163
  · exact point240slice164
  · exact point240slice165
  · exact point240slice166
  · exact point240slice167
  · exact point240slice168
  · exact point240slice169
  · exact point240slice170
  · exact point240slice171
  · exact point240slice172
  · exact point240slice173
  · exact point240slice174
  · exact point240slice175
  · exact point240slice176
  · exact point240slice177
  · exact point240slice178
  · exact point240slice179
  · exact point240slice180
  · exact point240slice181
  · exact point240slice182
  · exact point240slice183
  · exact point240slice184
  · exact point240slice185
  · exact point240slice186
  · exact point240slice187
  · exact point240slice188
  · exact point240slice189
  · exact point240slice190
  · exact point240slice191
  · exact point240slice192
  · exact point240slice193
  · exact point240slice194
  · exact point240slice195
  · exact point240slice196
  · exact point240slice197
  · exact point240slice198
  · exact point240slice199
  · exact point240slice200
  · exact point240slice201
  · exact point240slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
