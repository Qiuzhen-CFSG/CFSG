module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 213

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point213slice0 : Part6Nat.slice 0 3701 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice1 : Part6Nat.slice 0 3701 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice2 : Part6Nat.slice 0 3701 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice3 : Part6Nat.slice 0 3701 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice4 : Part6Nat.slice 0 3701 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice5 : Part6Nat.slice 0 3701 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice6 : Part6Nat.slice 0 3701 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice7 : Part6Nat.slice 0 3701 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice8 : Part6Nat.slice 0 3701 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice9 : Part6Nat.slice 0 3701 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice10 : Part6Nat.slice 0 3701 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice11 : Part6Nat.slice 0 3701 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice12 : Part6Nat.slice 0 3701 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice13 : Part6Nat.slice 0 3701 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice14 : Part6Nat.slice 0 3701 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice15 : Part6Nat.slice 0 3701 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice16 : Part6Nat.slice 0 3701 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice17 : Part6Nat.slice 0 3701 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice18 : Part6Nat.slice 0 3701 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice19 : Part6Nat.slice 0 3701 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice20 : Part6Nat.slice 0 3701 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice21 : Part6Nat.slice 0 3701 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice22 : Part6Nat.slice 0 3701 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice23 : Part6Nat.slice 0 3701 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice24 : Part6Nat.slice 0 3701 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice25 : Part6Nat.slice 0 3701 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice26 : Part6Nat.slice 0 3701 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice27 : Part6Nat.slice 0 3701 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice28 : Part6Nat.slice 0 3701 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice29 : Part6Nat.slice 0 3701 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice30 : Part6Nat.slice 0 3701 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice31 : Part6Nat.slice 0 3701 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice32 : Part6Nat.slice 0 3701 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice33 : Part6Nat.slice 0 3701 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice34 : Part6Nat.slice 0 3701 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice35 : Part6Nat.slice 0 3701 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice36 : Part6Nat.slice 0 3701 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice37 : Part6Nat.slice 0 3701 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice38 : Part6Nat.slice 0 3701 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice39 : Part6Nat.slice 0 3701 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice40 : Part6Nat.slice 0 3701 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice41 : Part6Nat.slice 0 3701 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice42 : Part6Nat.slice 0 3701 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice43 : Part6Nat.slice 0 3701 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice44 : Part6Nat.slice 0 3701 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice45 : Part6Nat.slice 0 3701 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice46 : Part6Nat.slice 0 3701 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice47 : Part6Nat.slice 0 3701 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice48 : Part6Nat.slice 0 3701 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice49 : Part6Nat.slice 0 3701 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice50 : Part6Nat.slice 0 3701 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice51 : Part6Nat.slice 0 3701 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice52 : Part6Nat.slice 0 3701 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice53 : Part6Nat.slice 0 3701 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice54 : Part6Nat.slice 0 3701 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice55 : Part6Nat.slice 0 3701 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice56 : Part6Nat.slice 0 3701 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice57 : Part6Nat.slice 0 3701 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice58 : Part6Nat.slice 0 3701 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice59 : Part6Nat.slice 0 3701 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice60 : Part6Nat.slice 0 3701 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice61 : Part6Nat.slice 0 3701 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice62 : Part6Nat.slice 0 3701 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice63 : Part6Nat.slice 0 3701 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice64 : Part6Nat.slice 0 3701 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice65 : Part6Nat.slice 0 3701 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice66 : Part6Nat.slice 0 3701 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice67 : Part6Nat.slice 0 3701 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice68 : Part6Nat.slice 0 3701 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice69 : Part6Nat.slice 0 3701 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice70 : Part6Nat.slice 0 3701 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice71 : Part6Nat.slice 0 3701 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice72 : Part6Nat.slice 0 3701 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice73 : Part6Nat.slice 0 3701 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice74 : Part6Nat.slice 0 3701 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice75 : Part6Nat.slice 0 3701 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice76 : Part6Nat.slice 0 3701 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice77 : Part6Nat.slice 0 3701 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice78 : Part6Nat.slice 0 3701 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice79 : Part6Nat.slice 0 3701 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice80 : Part6Nat.slice 0 3701 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice81 : Part6Nat.slice 0 3701 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice82 : Part6Nat.slice 0 3701 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice83 : Part6Nat.slice 0 3701 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice84 : Part6Nat.slice 0 3701 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice85 : Part6Nat.slice 0 3701 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice86 : Part6Nat.slice 0 3701 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice87 : Part6Nat.slice 0 3701 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice88 : Part6Nat.slice 0 3701 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice89 : Part6Nat.slice 0 3701 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice90 : Part6Nat.slice 0 3701 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice91 : Part6Nat.slice 0 3701 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice92 : Part6Nat.slice 0 3701 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice93 : Part6Nat.slice 0 3701 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice94 : Part6Nat.slice 0 3701 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice95 : Part6Nat.slice 0 3701 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice96 : Part6Nat.slice 0 3701 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice97 : Part6Nat.slice 0 3701 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice98 : Part6Nat.slice 0 3701 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice99 : Part6Nat.slice 0 3701 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice100 : Part6Nat.slice 0 3701 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice101 : Part6Nat.slice 0 3701 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice102 : Part6Nat.slice 0 3701 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice103 : Part6Nat.slice 0 3701 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice104 : Part6Nat.slice 0 3701 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice105 : Part6Nat.slice 0 3701 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice106 : Part6Nat.slice 0 3701 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice107 : Part6Nat.slice 0 3701 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice108 : Part6Nat.slice 0 3701 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice109 : Part6Nat.slice 0 3701 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice110 : Part6Nat.slice 0 3701 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice111 : Part6Nat.slice 0 3701 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice112 : Part6Nat.slice 0 3701 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice113 : Part6Nat.slice 0 3701 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice114 : Part6Nat.slice 0 3701 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice115 : Part6Nat.slice 0 3701 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice116 : Part6Nat.slice 0 3701 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice117 : Part6Nat.slice 0 3701 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice118 : Part6Nat.slice 0 3701 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice119 : Part6Nat.slice 0 3701 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice120 : Part6Nat.slice 0 3701 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice121 : Part6Nat.slice 0 3701 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice122 : Part6Nat.slice 0 3701 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice123 : Part6Nat.slice 0 3701 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice124 : Part6Nat.slice 0 3701 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice125 : Part6Nat.slice 0 3701 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice126 : Part6Nat.slice 0 3701 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice127 : Part6Nat.slice 0 3701 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice128 : Part6Nat.slice 0 3701 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice129 : Part6Nat.slice 0 3701 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice130 : Part6Nat.slice 0 3701 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice131 : Part6Nat.slice 0 3701 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice132 : Part6Nat.slice 0 3701 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice133 : Part6Nat.slice 0 3701 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice134 : Part6Nat.slice 0 3701 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice135 : Part6Nat.slice 0 3701 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice136 : Part6Nat.slice 0 3701 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice137 : Part6Nat.slice 0 3701 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice138 : Part6Nat.slice 0 3701 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice139 : Part6Nat.slice 0 3701 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice140 : Part6Nat.slice 0 3701 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice141 : Part6Nat.slice 0 3701 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice142 : Part6Nat.slice 0 3701 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice143 : Part6Nat.slice 0 3701 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice144 : Part6Nat.slice 0 3701 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice145 : Part6Nat.slice 0 3701 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice146 : Part6Nat.slice 0 3701 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice147 : Part6Nat.slice 0 3701 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice148 : Part6Nat.slice 0 3701 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice149 : Part6Nat.slice 0 3701 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice150 : Part6Nat.slice 0 3701 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice151 : Part6Nat.slice 0 3701 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice152 : Part6Nat.slice 0 3701 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice153 : Part6Nat.slice 0 3701 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice154 : Part6Nat.slice 0 3701 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice155 : Part6Nat.slice 0 3701 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice156 : Part6Nat.slice 0 3701 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice157 : Part6Nat.slice 0 3701 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice158 : Part6Nat.slice 0 3701 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice159 : Part6Nat.slice 0 3701 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice160 : Part6Nat.slice 0 3701 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice161 : Part6Nat.slice 0 3701 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice162 : Part6Nat.slice 0 3701 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice163 : Part6Nat.slice 0 3701 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice164 : Part6Nat.slice 0 3701 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice165 : Part6Nat.slice 0 3701 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice166 : Part6Nat.slice 0 3701 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice167 : Part6Nat.slice 0 3701 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice168 : Part6Nat.slice 0 3701 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice169 : Part6Nat.slice 0 3701 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice170 : Part6Nat.slice 0 3701 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice171 : Part6Nat.slice 0 3701 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice172 : Part6Nat.slice 0 3701 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice173 : Part6Nat.slice 0 3701 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice174 : Part6Nat.slice 0 3701 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice175 : Part6Nat.slice 0 3701 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice176 : Part6Nat.slice 0 3701 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice177 : Part6Nat.slice 0 3701 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice178 : Part6Nat.slice 0 3701 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice179 : Part6Nat.slice 0 3701 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice180 : Part6Nat.slice 0 3701 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice181 : Part6Nat.slice 0 3701 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice182 : Part6Nat.slice 0 3701 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice183 : Part6Nat.slice 0 3701 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice184 : Part6Nat.slice 0 3701 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice185 : Part6Nat.slice 0 3701 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice186 : Part6Nat.slice 0 3701 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice187 : Part6Nat.slice 0 3701 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice188 : Part6Nat.slice 0 3701 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice189 : Part6Nat.slice 0 3701 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice190 : Part6Nat.slice 0 3701 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice191 : Part6Nat.slice 0 3701 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice192 : Part6Nat.slice 0 3701 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice193 : Part6Nat.slice 0 3701 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice194 : Part6Nat.slice 0 3701 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice195 : Part6Nat.slice 0 3701 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice196 : Part6Nat.slice 0 3701 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice197 : Part6Nat.slice 0 3701 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice198 : Part6Nat.slice 0 3701 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice199 : Part6Nat.slice 0 3701 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice200 : Part6Nat.slice 0 3701 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice201 : Part6Nat.slice 0 3701 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point213slice202 : Part6Nat.slice 0 3701 202 = true := by
  decide +kernel

public theorem point213 : stepCheck 0 3701 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point213slice0
  · exact point213slice1
  · exact point213slice2
  · exact point213slice3
  · exact point213slice4
  · exact point213slice5
  · exact point213slice6
  · exact point213slice7
  · exact point213slice8
  · exact point213slice9
  · exact point213slice10
  · exact point213slice11
  · exact point213slice12
  · exact point213slice13
  · exact point213slice14
  · exact point213slice15
  · exact point213slice16
  · exact point213slice17
  · exact point213slice18
  · exact point213slice19
  · exact point213slice20
  · exact point213slice21
  · exact point213slice22
  · exact point213slice23
  · exact point213slice24
  · exact point213slice25
  · exact point213slice26
  · exact point213slice27
  · exact point213slice28
  · exact point213slice29
  · exact point213slice30
  · exact point213slice31
  · exact point213slice32
  · exact point213slice33
  · exact point213slice34
  · exact point213slice35
  · exact point213slice36
  · exact point213slice37
  · exact point213slice38
  · exact point213slice39
  · exact point213slice40
  · exact point213slice41
  · exact point213slice42
  · exact point213slice43
  · exact point213slice44
  · exact point213slice45
  · exact point213slice46
  · exact point213slice47
  · exact point213slice48
  · exact point213slice49
  · exact point213slice50
  · exact point213slice51
  · exact point213slice52
  · exact point213slice53
  · exact point213slice54
  · exact point213slice55
  · exact point213slice56
  · exact point213slice57
  · exact point213slice58
  · exact point213slice59
  · exact point213slice60
  · exact point213slice61
  · exact point213slice62
  · exact point213slice63
  · exact point213slice64
  · exact point213slice65
  · exact point213slice66
  · exact point213slice67
  · exact point213slice68
  · exact point213slice69
  · exact point213slice70
  · exact point213slice71
  · exact point213slice72
  · exact point213slice73
  · exact point213slice74
  · exact point213slice75
  · exact point213slice76
  · exact point213slice77
  · exact point213slice78
  · exact point213slice79
  · exact point213slice80
  · exact point213slice81
  · exact point213slice82
  · exact point213slice83
  · exact point213slice84
  · exact point213slice85
  · exact point213slice86
  · exact point213slice87
  · exact point213slice88
  · exact point213slice89
  · exact point213slice90
  · exact point213slice91
  · exact point213slice92
  · exact point213slice93
  · exact point213slice94
  · exact point213slice95
  · exact point213slice96
  · exact point213slice97
  · exact point213slice98
  · exact point213slice99
  · exact point213slice100
  · exact point213slice101
  · exact point213slice102
  · exact point213slice103
  · exact point213slice104
  · exact point213slice105
  · exact point213slice106
  · exact point213slice107
  · exact point213slice108
  · exact point213slice109
  · exact point213slice110
  · exact point213slice111
  · exact point213slice112
  · exact point213slice113
  · exact point213slice114
  · exact point213slice115
  · exact point213slice116
  · exact point213slice117
  · exact point213slice118
  · exact point213slice119
  · exact point213slice120
  · exact point213slice121
  · exact point213slice122
  · exact point213slice123
  · exact point213slice124
  · exact point213slice125
  · exact point213slice126
  · exact point213slice127
  · exact point213slice128
  · exact point213slice129
  · exact point213slice130
  · exact point213slice131
  · exact point213slice132
  · exact point213slice133
  · exact point213slice134
  · exact point213slice135
  · exact point213slice136
  · exact point213slice137
  · exact point213slice138
  · exact point213slice139
  · exact point213slice140
  · exact point213slice141
  · exact point213slice142
  · exact point213slice143
  · exact point213slice144
  · exact point213slice145
  · exact point213slice146
  · exact point213slice147
  · exact point213slice148
  · exact point213slice149
  · exact point213slice150
  · exact point213slice151
  · exact point213slice152
  · exact point213slice153
  · exact point213slice154
  · exact point213slice155
  · exact point213slice156
  · exact point213slice157
  · exact point213slice158
  · exact point213slice159
  · exact point213slice160
  · exact point213slice161
  · exact point213slice162
  · exact point213slice163
  · exact point213slice164
  · exact point213slice165
  · exact point213slice166
  · exact point213slice167
  · exact point213slice168
  · exact point213slice169
  · exact point213slice170
  · exact point213slice171
  · exact point213slice172
  · exact point213slice173
  · exact point213slice174
  · exact point213slice175
  · exact point213slice176
  · exact point213slice177
  · exact point213slice178
  · exact point213slice179
  · exact point213slice180
  · exact point213slice181
  · exact point213slice182
  · exact point213slice183
  · exact point213slice184
  · exact point213slice185
  · exact point213slice186
  · exact point213slice187
  · exact point213slice188
  · exact point213slice189
  · exact point213slice190
  · exact point213slice191
  · exact point213slice192
  · exact point213slice193
  · exact point213slice194
  · exact point213slice195
  · exact point213slice196
  · exact point213slice197
  · exact point213slice198
  · exact point213slice199
  · exact point213slice200
  · exact point213slice201
  · exact point213slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
