module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 220

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point220slice0 : Part6Nat.slice 1 3705 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice1 : Part6Nat.slice 1 3705 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice2 : Part6Nat.slice 1 3705 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice3 : Part6Nat.slice 1 3705 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice4 : Part6Nat.slice 1 3705 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice5 : Part6Nat.slice 1 3705 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice6 : Part6Nat.slice 1 3705 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice7 : Part6Nat.slice 1 3705 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice8 : Part6Nat.slice 1 3705 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice9 : Part6Nat.slice 1 3705 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice10 : Part6Nat.slice 1 3705 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice11 : Part6Nat.slice 1 3705 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice12 : Part6Nat.slice 1 3705 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice13 : Part6Nat.slice 1 3705 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice14 : Part6Nat.slice 1 3705 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice15 : Part6Nat.slice 1 3705 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice16 : Part6Nat.slice 1 3705 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice17 : Part6Nat.slice 1 3705 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice18 : Part6Nat.slice 1 3705 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice19 : Part6Nat.slice 1 3705 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice20 : Part6Nat.slice 1 3705 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice21 : Part6Nat.slice 1 3705 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice22 : Part6Nat.slice 1 3705 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice23 : Part6Nat.slice 1 3705 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice24 : Part6Nat.slice 1 3705 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice25 : Part6Nat.slice 1 3705 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice26 : Part6Nat.slice 1 3705 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice27 : Part6Nat.slice 1 3705 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice28 : Part6Nat.slice 1 3705 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice29 : Part6Nat.slice 1 3705 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice30 : Part6Nat.slice 1 3705 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice31 : Part6Nat.slice 1 3705 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice32 : Part6Nat.slice 1 3705 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice33 : Part6Nat.slice 1 3705 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice34 : Part6Nat.slice 1 3705 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice35 : Part6Nat.slice 1 3705 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice36 : Part6Nat.slice 1 3705 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice37 : Part6Nat.slice 1 3705 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice38 : Part6Nat.slice 1 3705 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice39 : Part6Nat.slice 1 3705 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice40 : Part6Nat.slice 1 3705 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice41 : Part6Nat.slice 1 3705 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice42 : Part6Nat.slice 1 3705 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice43 : Part6Nat.slice 1 3705 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice44 : Part6Nat.slice 1 3705 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice45 : Part6Nat.slice 1 3705 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice46 : Part6Nat.slice 1 3705 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice47 : Part6Nat.slice 1 3705 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice48 : Part6Nat.slice 1 3705 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice49 : Part6Nat.slice 1 3705 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice50 : Part6Nat.slice 1 3705 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice51 : Part6Nat.slice 1 3705 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice52 : Part6Nat.slice 1 3705 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice53 : Part6Nat.slice 1 3705 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice54 : Part6Nat.slice 1 3705 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice55 : Part6Nat.slice 1 3705 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice56 : Part6Nat.slice 1 3705 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice57 : Part6Nat.slice 1 3705 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice58 : Part6Nat.slice 1 3705 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice59 : Part6Nat.slice 1 3705 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice60 : Part6Nat.slice 1 3705 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice61 : Part6Nat.slice 1 3705 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice62 : Part6Nat.slice 1 3705 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice63 : Part6Nat.slice 1 3705 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice64 : Part6Nat.slice 1 3705 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice65 : Part6Nat.slice 1 3705 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice66 : Part6Nat.slice 1 3705 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice67 : Part6Nat.slice 1 3705 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice68 : Part6Nat.slice 1 3705 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice69 : Part6Nat.slice 1 3705 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice70 : Part6Nat.slice 1 3705 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice71 : Part6Nat.slice 1 3705 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice72 : Part6Nat.slice 1 3705 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice73 : Part6Nat.slice 1 3705 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice74 : Part6Nat.slice 1 3705 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice75 : Part6Nat.slice 1 3705 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice76 : Part6Nat.slice 1 3705 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice77 : Part6Nat.slice 1 3705 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice78 : Part6Nat.slice 1 3705 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice79 : Part6Nat.slice 1 3705 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice80 : Part6Nat.slice 1 3705 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice81 : Part6Nat.slice 1 3705 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice82 : Part6Nat.slice 1 3705 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice83 : Part6Nat.slice 1 3705 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice84 : Part6Nat.slice 1 3705 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice85 : Part6Nat.slice 1 3705 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice86 : Part6Nat.slice 1 3705 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice87 : Part6Nat.slice 1 3705 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice88 : Part6Nat.slice 1 3705 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice89 : Part6Nat.slice 1 3705 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice90 : Part6Nat.slice 1 3705 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice91 : Part6Nat.slice 1 3705 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice92 : Part6Nat.slice 1 3705 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice93 : Part6Nat.slice 1 3705 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice94 : Part6Nat.slice 1 3705 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice95 : Part6Nat.slice 1 3705 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice96 : Part6Nat.slice 1 3705 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice97 : Part6Nat.slice 1 3705 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice98 : Part6Nat.slice 1 3705 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice99 : Part6Nat.slice 1 3705 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice100 : Part6Nat.slice 1 3705 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice101 : Part6Nat.slice 1 3705 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice102 : Part6Nat.slice 1 3705 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice103 : Part6Nat.slice 1 3705 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice104 : Part6Nat.slice 1 3705 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice105 : Part6Nat.slice 1 3705 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice106 : Part6Nat.slice 1 3705 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice107 : Part6Nat.slice 1 3705 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice108 : Part6Nat.slice 1 3705 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice109 : Part6Nat.slice 1 3705 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice110 : Part6Nat.slice 1 3705 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice111 : Part6Nat.slice 1 3705 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice112 : Part6Nat.slice 1 3705 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice113 : Part6Nat.slice 1 3705 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice114 : Part6Nat.slice 1 3705 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice115 : Part6Nat.slice 1 3705 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice116 : Part6Nat.slice 1 3705 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice117 : Part6Nat.slice 1 3705 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice118 : Part6Nat.slice 1 3705 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice119 : Part6Nat.slice 1 3705 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice120 : Part6Nat.slice 1 3705 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice121 : Part6Nat.slice 1 3705 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice122 : Part6Nat.slice 1 3705 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice123 : Part6Nat.slice 1 3705 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice124 : Part6Nat.slice 1 3705 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice125 : Part6Nat.slice 1 3705 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice126 : Part6Nat.slice 1 3705 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice127 : Part6Nat.slice 1 3705 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice128 : Part6Nat.slice 1 3705 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice129 : Part6Nat.slice 1 3705 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice130 : Part6Nat.slice 1 3705 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice131 : Part6Nat.slice 1 3705 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice132 : Part6Nat.slice 1 3705 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice133 : Part6Nat.slice 1 3705 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice134 : Part6Nat.slice 1 3705 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice135 : Part6Nat.slice 1 3705 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice136 : Part6Nat.slice 1 3705 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice137 : Part6Nat.slice 1 3705 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice138 : Part6Nat.slice 1 3705 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice139 : Part6Nat.slice 1 3705 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice140 : Part6Nat.slice 1 3705 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice141 : Part6Nat.slice 1 3705 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice142 : Part6Nat.slice 1 3705 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice143 : Part6Nat.slice 1 3705 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice144 : Part6Nat.slice 1 3705 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice145 : Part6Nat.slice 1 3705 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice146 : Part6Nat.slice 1 3705 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice147 : Part6Nat.slice 1 3705 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice148 : Part6Nat.slice 1 3705 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice149 : Part6Nat.slice 1 3705 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice150 : Part6Nat.slice 1 3705 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice151 : Part6Nat.slice 1 3705 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice152 : Part6Nat.slice 1 3705 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice153 : Part6Nat.slice 1 3705 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice154 : Part6Nat.slice 1 3705 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice155 : Part6Nat.slice 1 3705 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice156 : Part6Nat.slice 1 3705 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice157 : Part6Nat.slice 1 3705 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice158 : Part6Nat.slice 1 3705 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice159 : Part6Nat.slice 1 3705 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice160 : Part6Nat.slice 1 3705 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice161 : Part6Nat.slice 1 3705 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice162 : Part6Nat.slice 1 3705 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice163 : Part6Nat.slice 1 3705 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice164 : Part6Nat.slice 1 3705 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice165 : Part6Nat.slice 1 3705 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice166 : Part6Nat.slice 1 3705 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice167 : Part6Nat.slice 1 3705 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice168 : Part6Nat.slice 1 3705 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice169 : Part6Nat.slice 1 3705 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice170 : Part6Nat.slice 1 3705 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice171 : Part6Nat.slice 1 3705 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice172 : Part6Nat.slice 1 3705 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice173 : Part6Nat.slice 1 3705 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice174 : Part6Nat.slice 1 3705 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice175 : Part6Nat.slice 1 3705 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice176 : Part6Nat.slice 1 3705 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice177 : Part6Nat.slice 1 3705 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice178 : Part6Nat.slice 1 3705 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice179 : Part6Nat.slice 1 3705 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice180 : Part6Nat.slice 1 3705 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice181 : Part6Nat.slice 1 3705 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice182 : Part6Nat.slice 1 3705 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice183 : Part6Nat.slice 1 3705 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice184 : Part6Nat.slice 1 3705 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice185 : Part6Nat.slice 1 3705 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice186 : Part6Nat.slice 1 3705 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice187 : Part6Nat.slice 1 3705 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice188 : Part6Nat.slice 1 3705 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice189 : Part6Nat.slice 1 3705 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice190 : Part6Nat.slice 1 3705 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice191 : Part6Nat.slice 1 3705 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice192 : Part6Nat.slice 1 3705 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice193 : Part6Nat.slice 1 3705 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice194 : Part6Nat.slice 1 3705 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice195 : Part6Nat.slice 1 3705 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice196 : Part6Nat.slice 1 3705 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice197 : Part6Nat.slice 1 3705 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice198 : Part6Nat.slice 1 3705 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice199 : Part6Nat.slice 1 3705 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice200 : Part6Nat.slice 1 3705 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice201 : Part6Nat.slice 1 3705 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point220slice202 : Part6Nat.slice 1 3705 202 = true := by
  decide +kernel

public theorem point220 : stepCheck 1 3705 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point220slice0
  · exact point220slice1
  · exact point220slice2
  · exact point220slice3
  · exact point220slice4
  · exact point220slice5
  · exact point220slice6
  · exact point220slice7
  · exact point220slice8
  · exact point220slice9
  · exact point220slice10
  · exact point220slice11
  · exact point220slice12
  · exact point220slice13
  · exact point220slice14
  · exact point220slice15
  · exact point220slice16
  · exact point220slice17
  · exact point220slice18
  · exact point220slice19
  · exact point220slice20
  · exact point220slice21
  · exact point220slice22
  · exact point220slice23
  · exact point220slice24
  · exact point220slice25
  · exact point220slice26
  · exact point220slice27
  · exact point220slice28
  · exact point220slice29
  · exact point220slice30
  · exact point220slice31
  · exact point220slice32
  · exact point220slice33
  · exact point220slice34
  · exact point220slice35
  · exact point220slice36
  · exact point220slice37
  · exact point220slice38
  · exact point220slice39
  · exact point220slice40
  · exact point220slice41
  · exact point220slice42
  · exact point220slice43
  · exact point220slice44
  · exact point220slice45
  · exact point220slice46
  · exact point220slice47
  · exact point220slice48
  · exact point220slice49
  · exact point220slice50
  · exact point220slice51
  · exact point220slice52
  · exact point220slice53
  · exact point220slice54
  · exact point220slice55
  · exact point220slice56
  · exact point220slice57
  · exact point220slice58
  · exact point220slice59
  · exact point220slice60
  · exact point220slice61
  · exact point220slice62
  · exact point220slice63
  · exact point220slice64
  · exact point220slice65
  · exact point220slice66
  · exact point220slice67
  · exact point220slice68
  · exact point220slice69
  · exact point220slice70
  · exact point220slice71
  · exact point220slice72
  · exact point220slice73
  · exact point220slice74
  · exact point220slice75
  · exact point220slice76
  · exact point220slice77
  · exact point220slice78
  · exact point220slice79
  · exact point220slice80
  · exact point220slice81
  · exact point220slice82
  · exact point220slice83
  · exact point220slice84
  · exact point220slice85
  · exact point220slice86
  · exact point220slice87
  · exact point220slice88
  · exact point220slice89
  · exact point220slice90
  · exact point220slice91
  · exact point220slice92
  · exact point220slice93
  · exact point220slice94
  · exact point220slice95
  · exact point220slice96
  · exact point220slice97
  · exact point220slice98
  · exact point220slice99
  · exact point220slice100
  · exact point220slice101
  · exact point220slice102
  · exact point220slice103
  · exact point220slice104
  · exact point220slice105
  · exact point220slice106
  · exact point220slice107
  · exact point220slice108
  · exact point220slice109
  · exact point220slice110
  · exact point220slice111
  · exact point220slice112
  · exact point220slice113
  · exact point220slice114
  · exact point220slice115
  · exact point220slice116
  · exact point220slice117
  · exact point220slice118
  · exact point220slice119
  · exact point220slice120
  · exact point220slice121
  · exact point220slice122
  · exact point220slice123
  · exact point220slice124
  · exact point220slice125
  · exact point220slice126
  · exact point220slice127
  · exact point220slice128
  · exact point220slice129
  · exact point220slice130
  · exact point220slice131
  · exact point220slice132
  · exact point220slice133
  · exact point220slice134
  · exact point220slice135
  · exact point220slice136
  · exact point220slice137
  · exact point220slice138
  · exact point220slice139
  · exact point220slice140
  · exact point220slice141
  · exact point220slice142
  · exact point220slice143
  · exact point220slice144
  · exact point220slice145
  · exact point220slice146
  · exact point220slice147
  · exact point220slice148
  · exact point220slice149
  · exact point220slice150
  · exact point220slice151
  · exact point220slice152
  · exact point220slice153
  · exact point220slice154
  · exact point220slice155
  · exact point220slice156
  · exact point220slice157
  · exact point220slice158
  · exact point220slice159
  · exact point220slice160
  · exact point220slice161
  · exact point220slice162
  · exact point220slice163
  · exact point220slice164
  · exact point220slice165
  · exact point220slice166
  · exact point220slice167
  · exact point220slice168
  · exact point220slice169
  · exact point220slice170
  · exact point220slice171
  · exact point220slice172
  · exact point220slice173
  · exact point220slice174
  · exact point220slice175
  · exact point220slice176
  · exact point220slice177
  · exact point220slice178
  · exact point220slice179
  · exact point220slice180
  · exact point220slice181
  · exact point220slice182
  · exact point220slice183
  · exact point220slice184
  · exact point220slice185
  · exact point220slice186
  · exact point220slice187
  · exact point220slice188
  · exact point220slice189
  · exact point220slice190
  · exact point220slice191
  · exact point220slice192
  · exact point220slice193
  · exact point220slice194
  · exact point220slice195
  · exact point220slice196
  · exact point220slice197
  · exact point220slice198
  · exact point220slice199
  · exact point220slice200
  · exact point220slice201
  · exact point220slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
