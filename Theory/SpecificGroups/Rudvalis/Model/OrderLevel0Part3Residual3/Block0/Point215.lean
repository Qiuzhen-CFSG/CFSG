module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 215

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point215slice0 : Part6Nat.slice 0 3710 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice1 : Part6Nat.slice 0 3710 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice2 : Part6Nat.slice 0 3710 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice3 : Part6Nat.slice 0 3710 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice4 : Part6Nat.slice 0 3710 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice5 : Part6Nat.slice 0 3710 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice6 : Part6Nat.slice 0 3710 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice7 : Part6Nat.slice 0 3710 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice8 : Part6Nat.slice 0 3710 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice9 : Part6Nat.slice 0 3710 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice10 : Part6Nat.slice 0 3710 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice11 : Part6Nat.slice 0 3710 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice12 : Part6Nat.slice 0 3710 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice13 : Part6Nat.slice 0 3710 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice14 : Part6Nat.slice 0 3710 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice15 : Part6Nat.slice 0 3710 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice16 : Part6Nat.slice 0 3710 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice17 : Part6Nat.slice 0 3710 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice18 : Part6Nat.slice 0 3710 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice19 : Part6Nat.slice 0 3710 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice20 : Part6Nat.slice 0 3710 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice21 : Part6Nat.slice 0 3710 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice22 : Part6Nat.slice 0 3710 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice23 : Part6Nat.slice 0 3710 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice24 : Part6Nat.slice 0 3710 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice25 : Part6Nat.slice 0 3710 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice26 : Part6Nat.slice 0 3710 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice27 : Part6Nat.slice 0 3710 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice28 : Part6Nat.slice 0 3710 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice29 : Part6Nat.slice 0 3710 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice30 : Part6Nat.slice 0 3710 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice31 : Part6Nat.slice 0 3710 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice32 : Part6Nat.slice 0 3710 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice33 : Part6Nat.slice 0 3710 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice34 : Part6Nat.slice 0 3710 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice35 : Part6Nat.slice 0 3710 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice36 : Part6Nat.slice 0 3710 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice37 : Part6Nat.slice 0 3710 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice38 : Part6Nat.slice 0 3710 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice39 : Part6Nat.slice 0 3710 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice40 : Part6Nat.slice 0 3710 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice41 : Part6Nat.slice 0 3710 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice42 : Part6Nat.slice 0 3710 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice43 : Part6Nat.slice 0 3710 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice44 : Part6Nat.slice 0 3710 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice45 : Part6Nat.slice 0 3710 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice46 : Part6Nat.slice 0 3710 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice47 : Part6Nat.slice 0 3710 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice48 : Part6Nat.slice 0 3710 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice49 : Part6Nat.slice 0 3710 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice50 : Part6Nat.slice 0 3710 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice51 : Part6Nat.slice 0 3710 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice52 : Part6Nat.slice 0 3710 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice53 : Part6Nat.slice 0 3710 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice54 : Part6Nat.slice 0 3710 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice55 : Part6Nat.slice 0 3710 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice56 : Part6Nat.slice 0 3710 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice57 : Part6Nat.slice 0 3710 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice58 : Part6Nat.slice 0 3710 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice59 : Part6Nat.slice 0 3710 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice60 : Part6Nat.slice 0 3710 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice61 : Part6Nat.slice 0 3710 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice62 : Part6Nat.slice 0 3710 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice63 : Part6Nat.slice 0 3710 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice64 : Part6Nat.slice 0 3710 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice65 : Part6Nat.slice 0 3710 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice66 : Part6Nat.slice 0 3710 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice67 : Part6Nat.slice 0 3710 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice68 : Part6Nat.slice 0 3710 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice69 : Part6Nat.slice 0 3710 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice70 : Part6Nat.slice 0 3710 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice71 : Part6Nat.slice 0 3710 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice72 : Part6Nat.slice 0 3710 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice73 : Part6Nat.slice 0 3710 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice74 : Part6Nat.slice 0 3710 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice75 : Part6Nat.slice 0 3710 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice76 : Part6Nat.slice 0 3710 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice77 : Part6Nat.slice 0 3710 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice78 : Part6Nat.slice 0 3710 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice79 : Part6Nat.slice 0 3710 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice80 : Part6Nat.slice 0 3710 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice81 : Part6Nat.slice 0 3710 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice82 : Part6Nat.slice 0 3710 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice83 : Part6Nat.slice 0 3710 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice84 : Part6Nat.slice 0 3710 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice85 : Part6Nat.slice 0 3710 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice86 : Part6Nat.slice 0 3710 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice87 : Part6Nat.slice 0 3710 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice88 : Part6Nat.slice 0 3710 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice89 : Part6Nat.slice 0 3710 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice90 : Part6Nat.slice 0 3710 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice91 : Part6Nat.slice 0 3710 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice92 : Part6Nat.slice 0 3710 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice93 : Part6Nat.slice 0 3710 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice94 : Part6Nat.slice 0 3710 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice95 : Part6Nat.slice 0 3710 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice96 : Part6Nat.slice 0 3710 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice97 : Part6Nat.slice 0 3710 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice98 : Part6Nat.slice 0 3710 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice99 : Part6Nat.slice 0 3710 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice100 : Part6Nat.slice 0 3710 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice101 : Part6Nat.slice 0 3710 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice102 : Part6Nat.slice 0 3710 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice103 : Part6Nat.slice 0 3710 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice104 : Part6Nat.slice 0 3710 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice105 : Part6Nat.slice 0 3710 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice106 : Part6Nat.slice 0 3710 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice107 : Part6Nat.slice 0 3710 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice108 : Part6Nat.slice 0 3710 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice109 : Part6Nat.slice 0 3710 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice110 : Part6Nat.slice 0 3710 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice111 : Part6Nat.slice 0 3710 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice112 : Part6Nat.slice 0 3710 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice113 : Part6Nat.slice 0 3710 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice114 : Part6Nat.slice 0 3710 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice115 : Part6Nat.slice 0 3710 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice116 : Part6Nat.slice 0 3710 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice117 : Part6Nat.slice 0 3710 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice118 : Part6Nat.slice 0 3710 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice119 : Part6Nat.slice 0 3710 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice120 : Part6Nat.slice 0 3710 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice121 : Part6Nat.slice 0 3710 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice122 : Part6Nat.slice 0 3710 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice123 : Part6Nat.slice 0 3710 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice124 : Part6Nat.slice 0 3710 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice125 : Part6Nat.slice 0 3710 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice126 : Part6Nat.slice 0 3710 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice127 : Part6Nat.slice 0 3710 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice128 : Part6Nat.slice 0 3710 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice129 : Part6Nat.slice 0 3710 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice130 : Part6Nat.slice 0 3710 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice131 : Part6Nat.slice 0 3710 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice132 : Part6Nat.slice 0 3710 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice133 : Part6Nat.slice 0 3710 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice134 : Part6Nat.slice 0 3710 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice135 : Part6Nat.slice 0 3710 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice136 : Part6Nat.slice 0 3710 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice137 : Part6Nat.slice 0 3710 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice138 : Part6Nat.slice 0 3710 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice139 : Part6Nat.slice 0 3710 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice140 : Part6Nat.slice 0 3710 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice141 : Part6Nat.slice 0 3710 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice142 : Part6Nat.slice 0 3710 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice143 : Part6Nat.slice 0 3710 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice144 : Part6Nat.slice 0 3710 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice145 : Part6Nat.slice 0 3710 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice146 : Part6Nat.slice 0 3710 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice147 : Part6Nat.slice 0 3710 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice148 : Part6Nat.slice 0 3710 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice149 : Part6Nat.slice 0 3710 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice150 : Part6Nat.slice 0 3710 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice151 : Part6Nat.slice 0 3710 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice152 : Part6Nat.slice 0 3710 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice153 : Part6Nat.slice 0 3710 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice154 : Part6Nat.slice 0 3710 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice155 : Part6Nat.slice 0 3710 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice156 : Part6Nat.slice 0 3710 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice157 : Part6Nat.slice 0 3710 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice158 : Part6Nat.slice 0 3710 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice159 : Part6Nat.slice 0 3710 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice160 : Part6Nat.slice 0 3710 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice161 : Part6Nat.slice 0 3710 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice162 : Part6Nat.slice 0 3710 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice163 : Part6Nat.slice 0 3710 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice164 : Part6Nat.slice 0 3710 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice165 : Part6Nat.slice 0 3710 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice166 : Part6Nat.slice 0 3710 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice167 : Part6Nat.slice 0 3710 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice168 : Part6Nat.slice 0 3710 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice169 : Part6Nat.slice 0 3710 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice170 : Part6Nat.slice 0 3710 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice171 : Part6Nat.slice 0 3710 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice172 : Part6Nat.slice 0 3710 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice173 : Part6Nat.slice 0 3710 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice174 : Part6Nat.slice 0 3710 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice175 : Part6Nat.slice 0 3710 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice176 : Part6Nat.slice 0 3710 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice177 : Part6Nat.slice 0 3710 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice178 : Part6Nat.slice 0 3710 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice179 : Part6Nat.slice 0 3710 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice180 : Part6Nat.slice 0 3710 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice181 : Part6Nat.slice 0 3710 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice182 : Part6Nat.slice 0 3710 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice183 : Part6Nat.slice 0 3710 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice184 : Part6Nat.slice 0 3710 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice185 : Part6Nat.slice 0 3710 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice186 : Part6Nat.slice 0 3710 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice187 : Part6Nat.slice 0 3710 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice188 : Part6Nat.slice 0 3710 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice189 : Part6Nat.slice 0 3710 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice190 : Part6Nat.slice 0 3710 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice191 : Part6Nat.slice 0 3710 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice192 : Part6Nat.slice 0 3710 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice193 : Part6Nat.slice 0 3710 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice194 : Part6Nat.slice 0 3710 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice195 : Part6Nat.slice 0 3710 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice196 : Part6Nat.slice 0 3710 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice197 : Part6Nat.slice 0 3710 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice198 : Part6Nat.slice 0 3710 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice199 : Part6Nat.slice 0 3710 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice200 : Part6Nat.slice 0 3710 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice201 : Part6Nat.slice 0 3710 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point215slice202 : Part6Nat.slice 0 3710 202 = true := by
  decide +kernel

public theorem point215 : stepCheck 0 3710 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point215slice0
  · exact point215slice1
  · exact point215slice2
  · exact point215slice3
  · exact point215slice4
  · exact point215slice5
  · exact point215slice6
  · exact point215slice7
  · exact point215slice8
  · exact point215slice9
  · exact point215slice10
  · exact point215slice11
  · exact point215slice12
  · exact point215slice13
  · exact point215slice14
  · exact point215slice15
  · exact point215slice16
  · exact point215slice17
  · exact point215slice18
  · exact point215slice19
  · exact point215slice20
  · exact point215slice21
  · exact point215slice22
  · exact point215slice23
  · exact point215slice24
  · exact point215slice25
  · exact point215slice26
  · exact point215slice27
  · exact point215slice28
  · exact point215slice29
  · exact point215slice30
  · exact point215slice31
  · exact point215slice32
  · exact point215slice33
  · exact point215slice34
  · exact point215slice35
  · exact point215slice36
  · exact point215slice37
  · exact point215slice38
  · exact point215slice39
  · exact point215slice40
  · exact point215slice41
  · exact point215slice42
  · exact point215slice43
  · exact point215slice44
  · exact point215slice45
  · exact point215slice46
  · exact point215slice47
  · exact point215slice48
  · exact point215slice49
  · exact point215slice50
  · exact point215slice51
  · exact point215slice52
  · exact point215slice53
  · exact point215slice54
  · exact point215slice55
  · exact point215slice56
  · exact point215slice57
  · exact point215slice58
  · exact point215slice59
  · exact point215slice60
  · exact point215slice61
  · exact point215slice62
  · exact point215slice63
  · exact point215slice64
  · exact point215slice65
  · exact point215slice66
  · exact point215slice67
  · exact point215slice68
  · exact point215slice69
  · exact point215slice70
  · exact point215slice71
  · exact point215slice72
  · exact point215slice73
  · exact point215slice74
  · exact point215slice75
  · exact point215slice76
  · exact point215slice77
  · exact point215slice78
  · exact point215slice79
  · exact point215slice80
  · exact point215slice81
  · exact point215slice82
  · exact point215slice83
  · exact point215slice84
  · exact point215slice85
  · exact point215slice86
  · exact point215slice87
  · exact point215slice88
  · exact point215slice89
  · exact point215slice90
  · exact point215slice91
  · exact point215slice92
  · exact point215slice93
  · exact point215slice94
  · exact point215slice95
  · exact point215slice96
  · exact point215slice97
  · exact point215slice98
  · exact point215slice99
  · exact point215slice100
  · exact point215slice101
  · exact point215slice102
  · exact point215slice103
  · exact point215slice104
  · exact point215slice105
  · exact point215slice106
  · exact point215slice107
  · exact point215slice108
  · exact point215slice109
  · exact point215slice110
  · exact point215slice111
  · exact point215slice112
  · exact point215slice113
  · exact point215slice114
  · exact point215slice115
  · exact point215slice116
  · exact point215slice117
  · exact point215slice118
  · exact point215slice119
  · exact point215slice120
  · exact point215slice121
  · exact point215slice122
  · exact point215slice123
  · exact point215slice124
  · exact point215slice125
  · exact point215slice126
  · exact point215slice127
  · exact point215slice128
  · exact point215slice129
  · exact point215slice130
  · exact point215slice131
  · exact point215slice132
  · exact point215slice133
  · exact point215slice134
  · exact point215slice135
  · exact point215slice136
  · exact point215slice137
  · exact point215slice138
  · exact point215slice139
  · exact point215slice140
  · exact point215slice141
  · exact point215slice142
  · exact point215slice143
  · exact point215slice144
  · exact point215slice145
  · exact point215slice146
  · exact point215slice147
  · exact point215slice148
  · exact point215slice149
  · exact point215slice150
  · exact point215slice151
  · exact point215slice152
  · exact point215slice153
  · exact point215slice154
  · exact point215slice155
  · exact point215slice156
  · exact point215slice157
  · exact point215slice158
  · exact point215slice159
  · exact point215slice160
  · exact point215slice161
  · exact point215slice162
  · exact point215slice163
  · exact point215slice164
  · exact point215slice165
  · exact point215slice166
  · exact point215slice167
  · exact point215slice168
  · exact point215slice169
  · exact point215slice170
  · exact point215slice171
  · exact point215slice172
  · exact point215slice173
  · exact point215slice174
  · exact point215slice175
  · exact point215slice176
  · exact point215slice177
  · exact point215slice178
  · exact point215slice179
  · exact point215slice180
  · exact point215slice181
  · exact point215slice182
  · exact point215slice183
  · exact point215slice184
  · exact point215slice185
  · exact point215slice186
  · exact point215slice187
  · exact point215slice188
  · exact point215slice189
  · exact point215slice190
  · exact point215slice191
  · exact point215slice192
  · exact point215slice193
  · exact point215slice194
  · exact point215slice195
  · exact point215slice196
  · exact point215slice197
  · exact point215slice198
  · exact point215slice199
  · exact point215slice200
  · exact point215slice201
  · exact point215slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
