module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 235

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point235slice0 : Part6Nat.slice 1 3846 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice1 : Part6Nat.slice 1 3846 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice2 : Part6Nat.slice 1 3846 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice3 : Part6Nat.slice 1 3846 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice4 : Part6Nat.slice 1 3846 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice5 : Part6Nat.slice 1 3846 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice6 : Part6Nat.slice 1 3846 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice7 : Part6Nat.slice 1 3846 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice8 : Part6Nat.slice 1 3846 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice9 : Part6Nat.slice 1 3846 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice10 : Part6Nat.slice 1 3846 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice11 : Part6Nat.slice 1 3846 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice12 : Part6Nat.slice 1 3846 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice13 : Part6Nat.slice 1 3846 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice14 : Part6Nat.slice 1 3846 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice15 : Part6Nat.slice 1 3846 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice16 : Part6Nat.slice 1 3846 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice17 : Part6Nat.slice 1 3846 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice18 : Part6Nat.slice 1 3846 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice19 : Part6Nat.slice 1 3846 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice20 : Part6Nat.slice 1 3846 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice21 : Part6Nat.slice 1 3846 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice22 : Part6Nat.slice 1 3846 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice23 : Part6Nat.slice 1 3846 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice24 : Part6Nat.slice 1 3846 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice25 : Part6Nat.slice 1 3846 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice26 : Part6Nat.slice 1 3846 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice27 : Part6Nat.slice 1 3846 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice28 : Part6Nat.slice 1 3846 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice29 : Part6Nat.slice 1 3846 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice30 : Part6Nat.slice 1 3846 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice31 : Part6Nat.slice 1 3846 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice32 : Part6Nat.slice 1 3846 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice33 : Part6Nat.slice 1 3846 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice34 : Part6Nat.slice 1 3846 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice35 : Part6Nat.slice 1 3846 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice36 : Part6Nat.slice 1 3846 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice37 : Part6Nat.slice 1 3846 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice38 : Part6Nat.slice 1 3846 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice39 : Part6Nat.slice 1 3846 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice40 : Part6Nat.slice 1 3846 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice41 : Part6Nat.slice 1 3846 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice42 : Part6Nat.slice 1 3846 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice43 : Part6Nat.slice 1 3846 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice44 : Part6Nat.slice 1 3846 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice45 : Part6Nat.slice 1 3846 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice46 : Part6Nat.slice 1 3846 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice47 : Part6Nat.slice 1 3846 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice48 : Part6Nat.slice 1 3846 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice49 : Part6Nat.slice 1 3846 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice50 : Part6Nat.slice 1 3846 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice51 : Part6Nat.slice 1 3846 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice52 : Part6Nat.slice 1 3846 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice53 : Part6Nat.slice 1 3846 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice54 : Part6Nat.slice 1 3846 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice55 : Part6Nat.slice 1 3846 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice56 : Part6Nat.slice 1 3846 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice57 : Part6Nat.slice 1 3846 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice58 : Part6Nat.slice 1 3846 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice59 : Part6Nat.slice 1 3846 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice60 : Part6Nat.slice 1 3846 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice61 : Part6Nat.slice 1 3846 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice62 : Part6Nat.slice 1 3846 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice63 : Part6Nat.slice 1 3846 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice64 : Part6Nat.slice 1 3846 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice65 : Part6Nat.slice 1 3846 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice66 : Part6Nat.slice 1 3846 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice67 : Part6Nat.slice 1 3846 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice68 : Part6Nat.slice 1 3846 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice69 : Part6Nat.slice 1 3846 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice70 : Part6Nat.slice 1 3846 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice71 : Part6Nat.slice 1 3846 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice72 : Part6Nat.slice 1 3846 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice73 : Part6Nat.slice 1 3846 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice74 : Part6Nat.slice 1 3846 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice75 : Part6Nat.slice 1 3846 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice76 : Part6Nat.slice 1 3846 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice77 : Part6Nat.slice 1 3846 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice78 : Part6Nat.slice 1 3846 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice79 : Part6Nat.slice 1 3846 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice80 : Part6Nat.slice 1 3846 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice81 : Part6Nat.slice 1 3846 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice82 : Part6Nat.slice 1 3846 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice83 : Part6Nat.slice 1 3846 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice84 : Part6Nat.slice 1 3846 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice85 : Part6Nat.slice 1 3846 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice86 : Part6Nat.slice 1 3846 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice87 : Part6Nat.slice 1 3846 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice88 : Part6Nat.slice 1 3846 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice89 : Part6Nat.slice 1 3846 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice90 : Part6Nat.slice 1 3846 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice91 : Part6Nat.slice 1 3846 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice92 : Part6Nat.slice 1 3846 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice93 : Part6Nat.slice 1 3846 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice94 : Part6Nat.slice 1 3846 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice95 : Part6Nat.slice 1 3846 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice96 : Part6Nat.slice 1 3846 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice97 : Part6Nat.slice 1 3846 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice98 : Part6Nat.slice 1 3846 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice99 : Part6Nat.slice 1 3846 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice100 : Part6Nat.slice 1 3846 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice101 : Part6Nat.slice 1 3846 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice102 : Part6Nat.slice 1 3846 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice103 : Part6Nat.slice 1 3846 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice104 : Part6Nat.slice 1 3846 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice105 : Part6Nat.slice 1 3846 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice106 : Part6Nat.slice 1 3846 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice107 : Part6Nat.slice 1 3846 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice108 : Part6Nat.slice 1 3846 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice109 : Part6Nat.slice 1 3846 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice110 : Part6Nat.slice 1 3846 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice111 : Part6Nat.slice 1 3846 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice112 : Part6Nat.slice 1 3846 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice113 : Part6Nat.slice 1 3846 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice114 : Part6Nat.slice 1 3846 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice115 : Part6Nat.slice 1 3846 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice116 : Part6Nat.slice 1 3846 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice117 : Part6Nat.slice 1 3846 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice118 : Part6Nat.slice 1 3846 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice119 : Part6Nat.slice 1 3846 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice120 : Part6Nat.slice 1 3846 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice121 : Part6Nat.slice 1 3846 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice122 : Part6Nat.slice 1 3846 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice123 : Part6Nat.slice 1 3846 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice124 : Part6Nat.slice 1 3846 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice125 : Part6Nat.slice 1 3846 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice126 : Part6Nat.slice 1 3846 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice127 : Part6Nat.slice 1 3846 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice128 : Part6Nat.slice 1 3846 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice129 : Part6Nat.slice 1 3846 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice130 : Part6Nat.slice 1 3846 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice131 : Part6Nat.slice 1 3846 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice132 : Part6Nat.slice 1 3846 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice133 : Part6Nat.slice 1 3846 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice134 : Part6Nat.slice 1 3846 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice135 : Part6Nat.slice 1 3846 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice136 : Part6Nat.slice 1 3846 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice137 : Part6Nat.slice 1 3846 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice138 : Part6Nat.slice 1 3846 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice139 : Part6Nat.slice 1 3846 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice140 : Part6Nat.slice 1 3846 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice141 : Part6Nat.slice 1 3846 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice142 : Part6Nat.slice 1 3846 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice143 : Part6Nat.slice 1 3846 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice144 : Part6Nat.slice 1 3846 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice145 : Part6Nat.slice 1 3846 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice146 : Part6Nat.slice 1 3846 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice147 : Part6Nat.slice 1 3846 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice148 : Part6Nat.slice 1 3846 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice149 : Part6Nat.slice 1 3846 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice150 : Part6Nat.slice 1 3846 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice151 : Part6Nat.slice 1 3846 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice152 : Part6Nat.slice 1 3846 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice153 : Part6Nat.slice 1 3846 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice154 : Part6Nat.slice 1 3846 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice155 : Part6Nat.slice 1 3846 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice156 : Part6Nat.slice 1 3846 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice157 : Part6Nat.slice 1 3846 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice158 : Part6Nat.slice 1 3846 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice159 : Part6Nat.slice 1 3846 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice160 : Part6Nat.slice 1 3846 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice161 : Part6Nat.slice 1 3846 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice162 : Part6Nat.slice 1 3846 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice163 : Part6Nat.slice 1 3846 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice164 : Part6Nat.slice 1 3846 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice165 : Part6Nat.slice 1 3846 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice166 : Part6Nat.slice 1 3846 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice167 : Part6Nat.slice 1 3846 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice168 : Part6Nat.slice 1 3846 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice169 : Part6Nat.slice 1 3846 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice170 : Part6Nat.slice 1 3846 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice171 : Part6Nat.slice 1 3846 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice172 : Part6Nat.slice 1 3846 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice173 : Part6Nat.slice 1 3846 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice174 : Part6Nat.slice 1 3846 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice175 : Part6Nat.slice 1 3846 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice176 : Part6Nat.slice 1 3846 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice177 : Part6Nat.slice 1 3846 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice178 : Part6Nat.slice 1 3846 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice179 : Part6Nat.slice 1 3846 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice180 : Part6Nat.slice 1 3846 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice181 : Part6Nat.slice 1 3846 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice182 : Part6Nat.slice 1 3846 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice183 : Part6Nat.slice 1 3846 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice184 : Part6Nat.slice 1 3846 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice185 : Part6Nat.slice 1 3846 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice186 : Part6Nat.slice 1 3846 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice187 : Part6Nat.slice 1 3846 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice188 : Part6Nat.slice 1 3846 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice189 : Part6Nat.slice 1 3846 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice190 : Part6Nat.slice 1 3846 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice191 : Part6Nat.slice 1 3846 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice192 : Part6Nat.slice 1 3846 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice193 : Part6Nat.slice 1 3846 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice194 : Part6Nat.slice 1 3846 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice195 : Part6Nat.slice 1 3846 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice196 : Part6Nat.slice 1 3846 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice197 : Part6Nat.slice 1 3846 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice198 : Part6Nat.slice 1 3846 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice199 : Part6Nat.slice 1 3846 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice200 : Part6Nat.slice 1 3846 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice201 : Part6Nat.slice 1 3846 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point235slice202 : Part6Nat.slice 1 3846 202 = true := by
  decide +kernel

public theorem point235 : stepCheck 1 3846 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point235slice0
  · exact point235slice1
  · exact point235slice2
  · exact point235slice3
  · exact point235slice4
  · exact point235slice5
  · exact point235slice6
  · exact point235slice7
  · exact point235slice8
  · exact point235slice9
  · exact point235slice10
  · exact point235slice11
  · exact point235slice12
  · exact point235slice13
  · exact point235slice14
  · exact point235slice15
  · exact point235slice16
  · exact point235slice17
  · exact point235slice18
  · exact point235slice19
  · exact point235slice20
  · exact point235slice21
  · exact point235slice22
  · exact point235slice23
  · exact point235slice24
  · exact point235slice25
  · exact point235slice26
  · exact point235slice27
  · exact point235slice28
  · exact point235slice29
  · exact point235slice30
  · exact point235slice31
  · exact point235slice32
  · exact point235slice33
  · exact point235slice34
  · exact point235slice35
  · exact point235slice36
  · exact point235slice37
  · exact point235slice38
  · exact point235slice39
  · exact point235slice40
  · exact point235slice41
  · exact point235slice42
  · exact point235slice43
  · exact point235slice44
  · exact point235slice45
  · exact point235slice46
  · exact point235slice47
  · exact point235slice48
  · exact point235slice49
  · exact point235slice50
  · exact point235slice51
  · exact point235slice52
  · exact point235slice53
  · exact point235slice54
  · exact point235slice55
  · exact point235slice56
  · exact point235slice57
  · exact point235slice58
  · exact point235slice59
  · exact point235slice60
  · exact point235slice61
  · exact point235slice62
  · exact point235slice63
  · exact point235slice64
  · exact point235slice65
  · exact point235slice66
  · exact point235slice67
  · exact point235slice68
  · exact point235slice69
  · exact point235slice70
  · exact point235slice71
  · exact point235slice72
  · exact point235slice73
  · exact point235slice74
  · exact point235slice75
  · exact point235slice76
  · exact point235slice77
  · exact point235slice78
  · exact point235slice79
  · exact point235slice80
  · exact point235slice81
  · exact point235slice82
  · exact point235slice83
  · exact point235slice84
  · exact point235slice85
  · exact point235slice86
  · exact point235slice87
  · exact point235slice88
  · exact point235slice89
  · exact point235slice90
  · exact point235slice91
  · exact point235slice92
  · exact point235slice93
  · exact point235slice94
  · exact point235slice95
  · exact point235slice96
  · exact point235slice97
  · exact point235slice98
  · exact point235slice99
  · exact point235slice100
  · exact point235slice101
  · exact point235slice102
  · exact point235slice103
  · exact point235slice104
  · exact point235slice105
  · exact point235slice106
  · exact point235slice107
  · exact point235slice108
  · exact point235slice109
  · exact point235slice110
  · exact point235slice111
  · exact point235slice112
  · exact point235slice113
  · exact point235slice114
  · exact point235slice115
  · exact point235slice116
  · exact point235slice117
  · exact point235slice118
  · exact point235slice119
  · exact point235slice120
  · exact point235slice121
  · exact point235slice122
  · exact point235slice123
  · exact point235slice124
  · exact point235slice125
  · exact point235slice126
  · exact point235slice127
  · exact point235slice128
  · exact point235slice129
  · exact point235slice130
  · exact point235slice131
  · exact point235slice132
  · exact point235slice133
  · exact point235slice134
  · exact point235slice135
  · exact point235slice136
  · exact point235slice137
  · exact point235slice138
  · exact point235slice139
  · exact point235slice140
  · exact point235slice141
  · exact point235slice142
  · exact point235slice143
  · exact point235slice144
  · exact point235slice145
  · exact point235slice146
  · exact point235slice147
  · exact point235slice148
  · exact point235slice149
  · exact point235slice150
  · exact point235slice151
  · exact point235slice152
  · exact point235slice153
  · exact point235slice154
  · exact point235slice155
  · exact point235slice156
  · exact point235slice157
  · exact point235slice158
  · exact point235slice159
  · exact point235slice160
  · exact point235slice161
  · exact point235slice162
  · exact point235slice163
  · exact point235slice164
  · exact point235slice165
  · exact point235slice166
  · exact point235slice167
  · exact point235slice168
  · exact point235slice169
  · exact point235slice170
  · exact point235slice171
  · exact point235slice172
  · exact point235slice173
  · exact point235slice174
  · exact point235slice175
  · exact point235slice176
  · exact point235slice177
  · exact point235slice178
  · exact point235slice179
  · exact point235slice180
  · exact point235slice181
  · exact point235slice182
  · exact point235slice183
  · exact point235slice184
  · exact point235slice185
  · exact point235slice186
  · exact point235slice187
  · exact point235slice188
  · exact point235slice189
  · exact point235slice190
  · exact point235slice191
  · exact point235slice192
  · exact point235slice193
  · exact point235slice194
  · exact point235slice195
  · exact point235slice196
  · exact point235slice197
  · exact point235slice198
  · exact point235slice199
  · exact point235slice200
  · exact point235slice201
  · exact point235slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
