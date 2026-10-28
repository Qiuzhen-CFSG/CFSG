module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 246

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point246slice0 : Part6Nat.slice 0 3984 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice1 : Part6Nat.slice 0 3984 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice2 : Part6Nat.slice 0 3984 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice3 : Part6Nat.slice 0 3984 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice4 : Part6Nat.slice 0 3984 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice5 : Part6Nat.slice 0 3984 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice6 : Part6Nat.slice 0 3984 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice7 : Part6Nat.slice 0 3984 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice8 : Part6Nat.slice 0 3984 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice9 : Part6Nat.slice 0 3984 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice10 : Part6Nat.slice 0 3984 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice11 : Part6Nat.slice 0 3984 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice12 : Part6Nat.slice 0 3984 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice13 : Part6Nat.slice 0 3984 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice14 : Part6Nat.slice 0 3984 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice15 : Part6Nat.slice 0 3984 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice16 : Part6Nat.slice 0 3984 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice17 : Part6Nat.slice 0 3984 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice18 : Part6Nat.slice 0 3984 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice19 : Part6Nat.slice 0 3984 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice20 : Part6Nat.slice 0 3984 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice21 : Part6Nat.slice 0 3984 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice22 : Part6Nat.slice 0 3984 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice23 : Part6Nat.slice 0 3984 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice24 : Part6Nat.slice 0 3984 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice25 : Part6Nat.slice 0 3984 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice26 : Part6Nat.slice 0 3984 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice27 : Part6Nat.slice 0 3984 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice28 : Part6Nat.slice 0 3984 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice29 : Part6Nat.slice 0 3984 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice30 : Part6Nat.slice 0 3984 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice31 : Part6Nat.slice 0 3984 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice32 : Part6Nat.slice 0 3984 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice33 : Part6Nat.slice 0 3984 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice34 : Part6Nat.slice 0 3984 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice35 : Part6Nat.slice 0 3984 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice36 : Part6Nat.slice 0 3984 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice37 : Part6Nat.slice 0 3984 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice38 : Part6Nat.slice 0 3984 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice39 : Part6Nat.slice 0 3984 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice40 : Part6Nat.slice 0 3984 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice41 : Part6Nat.slice 0 3984 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice42 : Part6Nat.slice 0 3984 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice43 : Part6Nat.slice 0 3984 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice44 : Part6Nat.slice 0 3984 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice45 : Part6Nat.slice 0 3984 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice46 : Part6Nat.slice 0 3984 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice47 : Part6Nat.slice 0 3984 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice48 : Part6Nat.slice 0 3984 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice49 : Part6Nat.slice 0 3984 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice50 : Part6Nat.slice 0 3984 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice51 : Part6Nat.slice 0 3984 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice52 : Part6Nat.slice 0 3984 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice53 : Part6Nat.slice 0 3984 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice54 : Part6Nat.slice 0 3984 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice55 : Part6Nat.slice 0 3984 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice56 : Part6Nat.slice 0 3984 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice57 : Part6Nat.slice 0 3984 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice58 : Part6Nat.slice 0 3984 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice59 : Part6Nat.slice 0 3984 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice60 : Part6Nat.slice 0 3984 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice61 : Part6Nat.slice 0 3984 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice62 : Part6Nat.slice 0 3984 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice63 : Part6Nat.slice 0 3984 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice64 : Part6Nat.slice 0 3984 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice65 : Part6Nat.slice 0 3984 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice66 : Part6Nat.slice 0 3984 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice67 : Part6Nat.slice 0 3984 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice68 : Part6Nat.slice 0 3984 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice69 : Part6Nat.slice 0 3984 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice70 : Part6Nat.slice 0 3984 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice71 : Part6Nat.slice 0 3984 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice72 : Part6Nat.slice 0 3984 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice73 : Part6Nat.slice 0 3984 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice74 : Part6Nat.slice 0 3984 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice75 : Part6Nat.slice 0 3984 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice76 : Part6Nat.slice 0 3984 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice77 : Part6Nat.slice 0 3984 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice78 : Part6Nat.slice 0 3984 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice79 : Part6Nat.slice 0 3984 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice80 : Part6Nat.slice 0 3984 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice81 : Part6Nat.slice 0 3984 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice82 : Part6Nat.slice 0 3984 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice83 : Part6Nat.slice 0 3984 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice84 : Part6Nat.slice 0 3984 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice85 : Part6Nat.slice 0 3984 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice86 : Part6Nat.slice 0 3984 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice87 : Part6Nat.slice 0 3984 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice88 : Part6Nat.slice 0 3984 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice89 : Part6Nat.slice 0 3984 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice90 : Part6Nat.slice 0 3984 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice91 : Part6Nat.slice 0 3984 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice92 : Part6Nat.slice 0 3984 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice93 : Part6Nat.slice 0 3984 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice94 : Part6Nat.slice 0 3984 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice95 : Part6Nat.slice 0 3984 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice96 : Part6Nat.slice 0 3984 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice97 : Part6Nat.slice 0 3984 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice98 : Part6Nat.slice 0 3984 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice99 : Part6Nat.slice 0 3984 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice100 : Part6Nat.slice 0 3984 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice101 : Part6Nat.slice 0 3984 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice102 : Part6Nat.slice 0 3984 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice103 : Part6Nat.slice 0 3984 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice104 : Part6Nat.slice 0 3984 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice105 : Part6Nat.slice 0 3984 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice106 : Part6Nat.slice 0 3984 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice107 : Part6Nat.slice 0 3984 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice108 : Part6Nat.slice 0 3984 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice109 : Part6Nat.slice 0 3984 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice110 : Part6Nat.slice 0 3984 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice111 : Part6Nat.slice 0 3984 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice112 : Part6Nat.slice 0 3984 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice113 : Part6Nat.slice 0 3984 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice114 : Part6Nat.slice 0 3984 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice115 : Part6Nat.slice 0 3984 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice116 : Part6Nat.slice 0 3984 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice117 : Part6Nat.slice 0 3984 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice118 : Part6Nat.slice 0 3984 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice119 : Part6Nat.slice 0 3984 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice120 : Part6Nat.slice 0 3984 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice121 : Part6Nat.slice 0 3984 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice122 : Part6Nat.slice 0 3984 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice123 : Part6Nat.slice 0 3984 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice124 : Part6Nat.slice 0 3984 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice125 : Part6Nat.slice 0 3984 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice126 : Part6Nat.slice 0 3984 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice127 : Part6Nat.slice 0 3984 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice128 : Part6Nat.slice 0 3984 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice129 : Part6Nat.slice 0 3984 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice130 : Part6Nat.slice 0 3984 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice131 : Part6Nat.slice 0 3984 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice132 : Part6Nat.slice 0 3984 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice133 : Part6Nat.slice 0 3984 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice134 : Part6Nat.slice 0 3984 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice135 : Part6Nat.slice 0 3984 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice136 : Part6Nat.slice 0 3984 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice137 : Part6Nat.slice 0 3984 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice138 : Part6Nat.slice 0 3984 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice139 : Part6Nat.slice 0 3984 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice140 : Part6Nat.slice 0 3984 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice141 : Part6Nat.slice 0 3984 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice142 : Part6Nat.slice 0 3984 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice143 : Part6Nat.slice 0 3984 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice144 : Part6Nat.slice 0 3984 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice145 : Part6Nat.slice 0 3984 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice146 : Part6Nat.slice 0 3984 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice147 : Part6Nat.slice 0 3984 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice148 : Part6Nat.slice 0 3984 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice149 : Part6Nat.slice 0 3984 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice150 : Part6Nat.slice 0 3984 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice151 : Part6Nat.slice 0 3984 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice152 : Part6Nat.slice 0 3984 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice153 : Part6Nat.slice 0 3984 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice154 : Part6Nat.slice 0 3984 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice155 : Part6Nat.slice 0 3984 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice156 : Part6Nat.slice 0 3984 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice157 : Part6Nat.slice 0 3984 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice158 : Part6Nat.slice 0 3984 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice159 : Part6Nat.slice 0 3984 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice160 : Part6Nat.slice 0 3984 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice161 : Part6Nat.slice 0 3984 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice162 : Part6Nat.slice 0 3984 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice163 : Part6Nat.slice 0 3984 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice164 : Part6Nat.slice 0 3984 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice165 : Part6Nat.slice 0 3984 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice166 : Part6Nat.slice 0 3984 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice167 : Part6Nat.slice 0 3984 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice168 : Part6Nat.slice 0 3984 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice169 : Part6Nat.slice 0 3984 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice170 : Part6Nat.slice 0 3984 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice171 : Part6Nat.slice 0 3984 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice172 : Part6Nat.slice 0 3984 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice173 : Part6Nat.slice 0 3984 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice174 : Part6Nat.slice 0 3984 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice175 : Part6Nat.slice 0 3984 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice176 : Part6Nat.slice 0 3984 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice177 : Part6Nat.slice 0 3984 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice178 : Part6Nat.slice 0 3984 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice179 : Part6Nat.slice 0 3984 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice180 : Part6Nat.slice 0 3984 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice181 : Part6Nat.slice 0 3984 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice182 : Part6Nat.slice 0 3984 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice183 : Part6Nat.slice 0 3984 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice184 : Part6Nat.slice 0 3984 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice185 : Part6Nat.slice 0 3984 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice186 : Part6Nat.slice 0 3984 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice187 : Part6Nat.slice 0 3984 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice188 : Part6Nat.slice 0 3984 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice189 : Part6Nat.slice 0 3984 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice190 : Part6Nat.slice 0 3984 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice191 : Part6Nat.slice 0 3984 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice192 : Part6Nat.slice 0 3984 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice193 : Part6Nat.slice 0 3984 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice194 : Part6Nat.slice 0 3984 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice195 : Part6Nat.slice 0 3984 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice196 : Part6Nat.slice 0 3984 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice197 : Part6Nat.slice 0 3984 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice198 : Part6Nat.slice 0 3984 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice199 : Part6Nat.slice 0 3984 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice200 : Part6Nat.slice 0 3984 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice201 : Part6Nat.slice 0 3984 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point246slice202 : Part6Nat.slice 0 3984 202 = true := by
  decide +kernel

public theorem point246 : stepCheck 0 3984 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point246slice0
  · exact point246slice1
  · exact point246slice2
  · exact point246slice3
  · exact point246slice4
  · exact point246slice5
  · exact point246slice6
  · exact point246slice7
  · exact point246slice8
  · exact point246slice9
  · exact point246slice10
  · exact point246slice11
  · exact point246slice12
  · exact point246slice13
  · exact point246slice14
  · exact point246slice15
  · exact point246slice16
  · exact point246slice17
  · exact point246slice18
  · exact point246slice19
  · exact point246slice20
  · exact point246slice21
  · exact point246slice22
  · exact point246slice23
  · exact point246slice24
  · exact point246slice25
  · exact point246slice26
  · exact point246slice27
  · exact point246slice28
  · exact point246slice29
  · exact point246slice30
  · exact point246slice31
  · exact point246slice32
  · exact point246slice33
  · exact point246slice34
  · exact point246slice35
  · exact point246slice36
  · exact point246slice37
  · exact point246slice38
  · exact point246slice39
  · exact point246slice40
  · exact point246slice41
  · exact point246slice42
  · exact point246slice43
  · exact point246slice44
  · exact point246slice45
  · exact point246slice46
  · exact point246slice47
  · exact point246slice48
  · exact point246slice49
  · exact point246slice50
  · exact point246slice51
  · exact point246slice52
  · exact point246slice53
  · exact point246slice54
  · exact point246slice55
  · exact point246slice56
  · exact point246slice57
  · exact point246slice58
  · exact point246slice59
  · exact point246slice60
  · exact point246slice61
  · exact point246slice62
  · exact point246slice63
  · exact point246slice64
  · exact point246slice65
  · exact point246slice66
  · exact point246slice67
  · exact point246slice68
  · exact point246slice69
  · exact point246slice70
  · exact point246slice71
  · exact point246slice72
  · exact point246slice73
  · exact point246slice74
  · exact point246slice75
  · exact point246slice76
  · exact point246slice77
  · exact point246slice78
  · exact point246slice79
  · exact point246slice80
  · exact point246slice81
  · exact point246slice82
  · exact point246slice83
  · exact point246slice84
  · exact point246slice85
  · exact point246slice86
  · exact point246slice87
  · exact point246slice88
  · exact point246slice89
  · exact point246slice90
  · exact point246slice91
  · exact point246slice92
  · exact point246slice93
  · exact point246slice94
  · exact point246slice95
  · exact point246slice96
  · exact point246slice97
  · exact point246slice98
  · exact point246slice99
  · exact point246slice100
  · exact point246slice101
  · exact point246slice102
  · exact point246slice103
  · exact point246slice104
  · exact point246slice105
  · exact point246slice106
  · exact point246slice107
  · exact point246slice108
  · exact point246slice109
  · exact point246slice110
  · exact point246slice111
  · exact point246slice112
  · exact point246slice113
  · exact point246slice114
  · exact point246slice115
  · exact point246slice116
  · exact point246slice117
  · exact point246slice118
  · exact point246slice119
  · exact point246slice120
  · exact point246slice121
  · exact point246slice122
  · exact point246slice123
  · exact point246slice124
  · exact point246slice125
  · exact point246slice126
  · exact point246slice127
  · exact point246slice128
  · exact point246slice129
  · exact point246slice130
  · exact point246slice131
  · exact point246slice132
  · exact point246slice133
  · exact point246slice134
  · exact point246slice135
  · exact point246slice136
  · exact point246slice137
  · exact point246slice138
  · exact point246slice139
  · exact point246slice140
  · exact point246slice141
  · exact point246slice142
  · exact point246slice143
  · exact point246slice144
  · exact point246slice145
  · exact point246slice146
  · exact point246slice147
  · exact point246slice148
  · exact point246slice149
  · exact point246slice150
  · exact point246slice151
  · exact point246slice152
  · exact point246slice153
  · exact point246slice154
  · exact point246slice155
  · exact point246slice156
  · exact point246slice157
  · exact point246slice158
  · exact point246slice159
  · exact point246slice160
  · exact point246slice161
  · exact point246slice162
  · exact point246slice163
  · exact point246slice164
  · exact point246slice165
  · exact point246slice166
  · exact point246slice167
  · exact point246slice168
  · exact point246slice169
  · exact point246slice170
  · exact point246slice171
  · exact point246slice172
  · exact point246slice173
  · exact point246slice174
  · exact point246slice175
  · exact point246slice176
  · exact point246slice177
  · exact point246slice178
  · exact point246slice179
  · exact point246slice180
  · exact point246slice181
  · exact point246slice182
  · exact point246slice183
  · exact point246slice184
  · exact point246slice185
  · exact point246slice186
  · exact point246slice187
  · exact point246slice188
  · exact point246slice189
  · exact point246slice190
  · exact point246slice191
  · exact point246slice192
  · exact point246slice193
  · exact point246slice194
  · exact point246slice195
  · exact point246slice196
  · exact point246slice197
  · exact point246slice198
  · exact point246slice199
  · exact point246slice200
  · exact point246slice201
  · exact point246slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
