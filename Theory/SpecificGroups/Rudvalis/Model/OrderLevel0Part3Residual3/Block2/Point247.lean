module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 247

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point247slice0 : Part6Nat.slice 0 3985 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice1 : Part6Nat.slice 0 3985 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice2 : Part6Nat.slice 0 3985 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice3 : Part6Nat.slice 0 3985 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice4 : Part6Nat.slice 0 3985 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice5 : Part6Nat.slice 0 3985 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice6 : Part6Nat.slice 0 3985 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice7 : Part6Nat.slice 0 3985 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice8 : Part6Nat.slice 0 3985 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice9 : Part6Nat.slice 0 3985 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice10 : Part6Nat.slice 0 3985 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice11 : Part6Nat.slice 0 3985 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice12 : Part6Nat.slice 0 3985 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice13 : Part6Nat.slice 0 3985 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice14 : Part6Nat.slice 0 3985 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice15 : Part6Nat.slice 0 3985 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice16 : Part6Nat.slice 0 3985 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice17 : Part6Nat.slice 0 3985 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice18 : Part6Nat.slice 0 3985 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice19 : Part6Nat.slice 0 3985 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice20 : Part6Nat.slice 0 3985 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice21 : Part6Nat.slice 0 3985 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice22 : Part6Nat.slice 0 3985 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice23 : Part6Nat.slice 0 3985 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice24 : Part6Nat.slice 0 3985 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice25 : Part6Nat.slice 0 3985 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice26 : Part6Nat.slice 0 3985 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice27 : Part6Nat.slice 0 3985 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice28 : Part6Nat.slice 0 3985 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice29 : Part6Nat.slice 0 3985 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice30 : Part6Nat.slice 0 3985 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice31 : Part6Nat.slice 0 3985 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice32 : Part6Nat.slice 0 3985 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice33 : Part6Nat.slice 0 3985 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice34 : Part6Nat.slice 0 3985 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice35 : Part6Nat.slice 0 3985 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice36 : Part6Nat.slice 0 3985 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice37 : Part6Nat.slice 0 3985 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice38 : Part6Nat.slice 0 3985 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice39 : Part6Nat.slice 0 3985 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice40 : Part6Nat.slice 0 3985 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice41 : Part6Nat.slice 0 3985 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice42 : Part6Nat.slice 0 3985 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice43 : Part6Nat.slice 0 3985 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice44 : Part6Nat.slice 0 3985 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice45 : Part6Nat.slice 0 3985 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice46 : Part6Nat.slice 0 3985 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice47 : Part6Nat.slice 0 3985 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice48 : Part6Nat.slice 0 3985 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice49 : Part6Nat.slice 0 3985 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice50 : Part6Nat.slice 0 3985 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice51 : Part6Nat.slice 0 3985 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice52 : Part6Nat.slice 0 3985 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice53 : Part6Nat.slice 0 3985 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice54 : Part6Nat.slice 0 3985 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice55 : Part6Nat.slice 0 3985 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice56 : Part6Nat.slice 0 3985 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice57 : Part6Nat.slice 0 3985 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice58 : Part6Nat.slice 0 3985 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice59 : Part6Nat.slice 0 3985 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice60 : Part6Nat.slice 0 3985 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice61 : Part6Nat.slice 0 3985 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice62 : Part6Nat.slice 0 3985 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice63 : Part6Nat.slice 0 3985 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice64 : Part6Nat.slice 0 3985 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice65 : Part6Nat.slice 0 3985 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice66 : Part6Nat.slice 0 3985 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice67 : Part6Nat.slice 0 3985 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice68 : Part6Nat.slice 0 3985 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice69 : Part6Nat.slice 0 3985 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice70 : Part6Nat.slice 0 3985 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice71 : Part6Nat.slice 0 3985 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice72 : Part6Nat.slice 0 3985 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice73 : Part6Nat.slice 0 3985 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice74 : Part6Nat.slice 0 3985 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice75 : Part6Nat.slice 0 3985 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice76 : Part6Nat.slice 0 3985 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice77 : Part6Nat.slice 0 3985 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice78 : Part6Nat.slice 0 3985 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice79 : Part6Nat.slice 0 3985 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice80 : Part6Nat.slice 0 3985 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice81 : Part6Nat.slice 0 3985 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice82 : Part6Nat.slice 0 3985 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice83 : Part6Nat.slice 0 3985 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice84 : Part6Nat.slice 0 3985 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice85 : Part6Nat.slice 0 3985 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice86 : Part6Nat.slice 0 3985 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice87 : Part6Nat.slice 0 3985 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice88 : Part6Nat.slice 0 3985 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice89 : Part6Nat.slice 0 3985 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice90 : Part6Nat.slice 0 3985 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice91 : Part6Nat.slice 0 3985 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice92 : Part6Nat.slice 0 3985 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice93 : Part6Nat.slice 0 3985 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice94 : Part6Nat.slice 0 3985 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice95 : Part6Nat.slice 0 3985 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice96 : Part6Nat.slice 0 3985 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice97 : Part6Nat.slice 0 3985 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice98 : Part6Nat.slice 0 3985 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice99 : Part6Nat.slice 0 3985 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice100 : Part6Nat.slice 0 3985 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice101 : Part6Nat.slice 0 3985 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice102 : Part6Nat.slice 0 3985 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice103 : Part6Nat.slice 0 3985 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice104 : Part6Nat.slice 0 3985 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice105 : Part6Nat.slice 0 3985 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice106 : Part6Nat.slice 0 3985 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice107 : Part6Nat.slice 0 3985 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice108 : Part6Nat.slice 0 3985 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice109 : Part6Nat.slice 0 3985 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice110 : Part6Nat.slice 0 3985 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice111 : Part6Nat.slice 0 3985 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice112 : Part6Nat.slice 0 3985 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice113 : Part6Nat.slice 0 3985 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice114 : Part6Nat.slice 0 3985 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice115 : Part6Nat.slice 0 3985 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice116 : Part6Nat.slice 0 3985 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice117 : Part6Nat.slice 0 3985 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice118 : Part6Nat.slice 0 3985 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice119 : Part6Nat.slice 0 3985 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice120 : Part6Nat.slice 0 3985 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice121 : Part6Nat.slice 0 3985 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice122 : Part6Nat.slice 0 3985 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice123 : Part6Nat.slice 0 3985 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice124 : Part6Nat.slice 0 3985 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice125 : Part6Nat.slice 0 3985 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice126 : Part6Nat.slice 0 3985 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice127 : Part6Nat.slice 0 3985 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice128 : Part6Nat.slice 0 3985 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice129 : Part6Nat.slice 0 3985 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice130 : Part6Nat.slice 0 3985 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice131 : Part6Nat.slice 0 3985 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice132 : Part6Nat.slice 0 3985 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice133 : Part6Nat.slice 0 3985 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice134 : Part6Nat.slice 0 3985 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice135 : Part6Nat.slice 0 3985 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice136 : Part6Nat.slice 0 3985 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice137 : Part6Nat.slice 0 3985 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice138 : Part6Nat.slice 0 3985 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice139 : Part6Nat.slice 0 3985 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice140 : Part6Nat.slice 0 3985 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice141 : Part6Nat.slice 0 3985 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice142 : Part6Nat.slice 0 3985 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice143 : Part6Nat.slice 0 3985 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice144 : Part6Nat.slice 0 3985 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice145 : Part6Nat.slice 0 3985 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice146 : Part6Nat.slice 0 3985 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice147 : Part6Nat.slice 0 3985 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice148 : Part6Nat.slice 0 3985 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice149 : Part6Nat.slice 0 3985 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice150 : Part6Nat.slice 0 3985 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice151 : Part6Nat.slice 0 3985 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice152 : Part6Nat.slice 0 3985 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice153 : Part6Nat.slice 0 3985 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice154 : Part6Nat.slice 0 3985 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice155 : Part6Nat.slice 0 3985 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice156 : Part6Nat.slice 0 3985 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice157 : Part6Nat.slice 0 3985 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice158 : Part6Nat.slice 0 3985 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice159 : Part6Nat.slice 0 3985 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice160 : Part6Nat.slice 0 3985 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice161 : Part6Nat.slice 0 3985 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice162 : Part6Nat.slice 0 3985 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice163 : Part6Nat.slice 0 3985 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice164 : Part6Nat.slice 0 3985 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice165 : Part6Nat.slice 0 3985 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice166 : Part6Nat.slice 0 3985 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice167 : Part6Nat.slice 0 3985 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice168 : Part6Nat.slice 0 3985 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice169 : Part6Nat.slice 0 3985 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice170 : Part6Nat.slice 0 3985 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice171 : Part6Nat.slice 0 3985 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice172 : Part6Nat.slice 0 3985 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice173 : Part6Nat.slice 0 3985 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice174 : Part6Nat.slice 0 3985 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice175 : Part6Nat.slice 0 3985 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice176 : Part6Nat.slice 0 3985 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice177 : Part6Nat.slice 0 3985 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice178 : Part6Nat.slice 0 3985 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice179 : Part6Nat.slice 0 3985 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice180 : Part6Nat.slice 0 3985 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice181 : Part6Nat.slice 0 3985 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice182 : Part6Nat.slice 0 3985 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice183 : Part6Nat.slice 0 3985 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice184 : Part6Nat.slice 0 3985 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice185 : Part6Nat.slice 0 3985 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice186 : Part6Nat.slice 0 3985 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice187 : Part6Nat.slice 0 3985 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice188 : Part6Nat.slice 0 3985 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice189 : Part6Nat.slice 0 3985 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice190 : Part6Nat.slice 0 3985 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice191 : Part6Nat.slice 0 3985 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice192 : Part6Nat.slice 0 3985 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice193 : Part6Nat.slice 0 3985 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice194 : Part6Nat.slice 0 3985 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice195 : Part6Nat.slice 0 3985 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice196 : Part6Nat.slice 0 3985 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice197 : Part6Nat.slice 0 3985 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice198 : Part6Nat.slice 0 3985 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice199 : Part6Nat.slice 0 3985 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice200 : Part6Nat.slice 0 3985 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice201 : Part6Nat.slice 0 3985 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point247slice202 : Part6Nat.slice 0 3985 202 = true := by
  decide +kernel

public theorem point247 : stepCheck 0 3985 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point247slice0
  · exact point247slice1
  · exact point247slice2
  · exact point247slice3
  · exact point247slice4
  · exact point247slice5
  · exact point247slice6
  · exact point247slice7
  · exact point247slice8
  · exact point247slice9
  · exact point247slice10
  · exact point247slice11
  · exact point247slice12
  · exact point247slice13
  · exact point247slice14
  · exact point247slice15
  · exact point247slice16
  · exact point247slice17
  · exact point247slice18
  · exact point247slice19
  · exact point247slice20
  · exact point247slice21
  · exact point247slice22
  · exact point247slice23
  · exact point247slice24
  · exact point247slice25
  · exact point247slice26
  · exact point247slice27
  · exact point247slice28
  · exact point247slice29
  · exact point247slice30
  · exact point247slice31
  · exact point247slice32
  · exact point247slice33
  · exact point247slice34
  · exact point247slice35
  · exact point247slice36
  · exact point247slice37
  · exact point247slice38
  · exact point247slice39
  · exact point247slice40
  · exact point247slice41
  · exact point247slice42
  · exact point247slice43
  · exact point247slice44
  · exact point247slice45
  · exact point247slice46
  · exact point247slice47
  · exact point247slice48
  · exact point247slice49
  · exact point247slice50
  · exact point247slice51
  · exact point247slice52
  · exact point247slice53
  · exact point247slice54
  · exact point247slice55
  · exact point247slice56
  · exact point247slice57
  · exact point247slice58
  · exact point247slice59
  · exact point247slice60
  · exact point247slice61
  · exact point247slice62
  · exact point247slice63
  · exact point247slice64
  · exact point247slice65
  · exact point247slice66
  · exact point247slice67
  · exact point247slice68
  · exact point247slice69
  · exact point247slice70
  · exact point247slice71
  · exact point247slice72
  · exact point247slice73
  · exact point247slice74
  · exact point247slice75
  · exact point247slice76
  · exact point247slice77
  · exact point247slice78
  · exact point247slice79
  · exact point247slice80
  · exact point247slice81
  · exact point247slice82
  · exact point247slice83
  · exact point247slice84
  · exact point247slice85
  · exact point247slice86
  · exact point247slice87
  · exact point247slice88
  · exact point247slice89
  · exact point247slice90
  · exact point247slice91
  · exact point247slice92
  · exact point247slice93
  · exact point247slice94
  · exact point247slice95
  · exact point247slice96
  · exact point247slice97
  · exact point247slice98
  · exact point247slice99
  · exact point247slice100
  · exact point247slice101
  · exact point247slice102
  · exact point247slice103
  · exact point247slice104
  · exact point247slice105
  · exact point247slice106
  · exact point247slice107
  · exact point247slice108
  · exact point247slice109
  · exact point247slice110
  · exact point247slice111
  · exact point247slice112
  · exact point247slice113
  · exact point247slice114
  · exact point247slice115
  · exact point247slice116
  · exact point247slice117
  · exact point247slice118
  · exact point247slice119
  · exact point247slice120
  · exact point247slice121
  · exact point247slice122
  · exact point247slice123
  · exact point247slice124
  · exact point247slice125
  · exact point247slice126
  · exact point247slice127
  · exact point247slice128
  · exact point247slice129
  · exact point247slice130
  · exact point247slice131
  · exact point247slice132
  · exact point247slice133
  · exact point247slice134
  · exact point247slice135
  · exact point247slice136
  · exact point247slice137
  · exact point247slice138
  · exact point247slice139
  · exact point247slice140
  · exact point247slice141
  · exact point247slice142
  · exact point247slice143
  · exact point247slice144
  · exact point247slice145
  · exact point247slice146
  · exact point247slice147
  · exact point247slice148
  · exact point247slice149
  · exact point247slice150
  · exact point247slice151
  · exact point247slice152
  · exact point247slice153
  · exact point247slice154
  · exact point247slice155
  · exact point247slice156
  · exact point247slice157
  · exact point247slice158
  · exact point247slice159
  · exact point247slice160
  · exact point247slice161
  · exact point247slice162
  · exact point247slice163
  · exact point247slice164
  · exact point247slice165
  · exact point247slice166
  · exact point247slice167
  · exact point247slice168
  · exact point247slice169
  · exact point247slice170
  · exact point247slice171
  · exact point247slice172
  · exact point247slice173
  · exact point247slice174
  · exact point247slice175
  · exact point247slice176
  · exact point247slice177
  · exact point247slice178
  · exact point247slice179
  · exact point247slice180
  · exact point247slice181
  · exact point247slice182
  · exact point247slice183
  · exact point247slice184
  · exact point247slice185
  · exact point247slice186
  · exact point247slice187
  · exact point247slice188
  · exact point247slice189
  · exact point247slice190
  · exact point247slice191
  · exact point247slice192
  · exact point247slice193
  · exact point247slice194
  · exact point247slice195
  · exact point247slice196
  · exact point247slice197
  · exact point247slice198
  · exact point247slice199
  · exact point247slice200
  · exact point247slice201
  · exact point247slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
