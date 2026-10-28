module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 205

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point205slice0 : Part6Nat.slice 0 3575 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice1 : Part6Nat.slice 0 3575 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice2 : Part6Nat.slice 0 3575 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice3 : Part6Nat.slice 0 3575 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice4 : Part6Nat.slice 0 3575 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice5 : Part6Nat.slice 0 3575 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice6 : Part6Nat.slice 0 3575 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice7 : Part6Nat.slice 0 3575 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice8 : Part6Nat.slice 0 3575 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice9 : Part6Nat.slice 0 3575 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice10 : Part6Nat.slice 0 3575 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice11 : Part6Nat.slice 0 3575 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice12 : Part6Nat.slice 0 3575 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice13 : Part6Nat.slice 0 3575 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice14 : Part6Nat.slice 0 3575 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice15 : Part6Nat.slice 0 3575 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice16 : Part6Nat.slice 0 3575 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice17 : Part6Nat.slice 0 3575 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice18 : Part6Nat.slice 0 3575 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice19 : Part6Nat.slice 0 3575 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice20 : Part6Nat.slice 0 3575 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice21 : Part6Nat.slice 0 3575 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice22 : Part6Nat.slice 0 3575 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice23 : Part6Nat.slice 0 3575 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice24 : Part6Nat.slice 0 3575 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice25 : Part6Nat.slice 0 3575 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice26 : Part6Nat.slice 0 3575 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice27 : Part6Nat.slice 0 3575 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice28 : Part6Nat.slice 0 3575 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice29 : Part6Nat.slice 0 3575 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice30 : Part6Nat.slice 0 3575 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice31 : Part6Nat.slice 0 3575 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice32 : Part6Nat.slice 0 3575 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice33 : Part6Nat.slice 0 3575 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice34 : Part6Nat.slice 0 3575 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice35 : Part6Nat.slice 0 3575 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice36 : Part6Nat.slice 0 3575 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice37 : Part6Nat.slice 0 3575 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice38 : Part6Nat.slice 0 3575 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice39 : Part6Nat.slice 0 3575 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice40 : Part6Nat.slice 0 3575 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice41 : Part6Nat.slice 0 3575 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice42 : Part6Nat.slice 0 3575 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice43 : Part6Nat.slice 0 3575 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice44 : Part6Nat.slice 0 3575 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice45 : Part6Nat.slice 0 3575 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice46 : Part6Nat.slice 0 3575 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice47 : Part6Nat.slice 0 3575 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice48 : Part6Nat.slice 0 3575 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice49 : Part6Nat.slice 0 3575 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice50 : Part6Nat.slice 0 3575 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice51 : Part6Nat.slice 0 3575 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice52 : Part6Nat.slice 0 3575 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice53 : Part6Nat.slice 0 3575 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice54 : Part6Nat.slice 0 3575 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice55 : Part6Nat.slice 0 3575 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice56 : Part6Nat.slice 0 3575 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice57 : Part6Nat.slice 0 3575 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice58 : Part6Nat.slice 0 3575 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice59 : Part6Nat.slice 0 3575 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice60 : Part6Nat.slice 0 3575 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice61 : Part6Nat.slice 0 3575 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice62 : Part6Nat.slice 0 3575 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice63 : Part6Nat.slice 0 3575 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice64 : Part6Nat.slice 0 3575 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice65 : Part6Nat.slice 0 3575 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice66 : Part6Nat.slice 0 3575 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice67 : Part6Nat.slice 0 3575 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice68 : Part6Nat.slice 0 3575 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice69 : Part6Nat.slice 0 3575 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice70 : Part6Nat.slice 0 3575 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice71 : Part6Nat.slice 0 3575 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice72 : Part6Nat.slice 0 3575 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice73 : Part6Nat.slice 0 3575 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice74 : Part6Nat.slice 0 3575 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice75 : Part6Nat.slice 0 3575 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice76 : Part6Nat.slice 0 3575 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice77 : Part6Nat.slice 0 3575 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice78 : Part6Nat.slice 0 3575 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice79 : Part6Nat.slice 0 3575 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice80 : Part6Nat.slice 0 3575 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice81 : Part6Nat.slice 0 3575 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice82 : Part6Nat.slice 0 3575 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice83 : Part6Nat.slice 0 3575 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice84 : Part6Nat.slice 0 3575 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice85 : Part6Nat.slice 0 3575 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice86 : Part6Nat.slice 0 3575 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice87 : Part6Nat.slice 0 3575 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice88 : Part6Nat.slice 0 3575 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice89 : Part6Nat.slice 0 3575 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice90 : Part6Nat.slice 0 3575 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice91 : Part6Nat.slice 0 3575 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice92 : Part6Nat.slice 0 3575 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice93 : Part6Nat.slice 0 3575 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice94 : Part6Nat.slice 0 3575 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice95 : Part6Nat.slice 0 3575 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice96 : Part6Nat.slice 0 3575 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice97 : Part6Nat.slice 0 3575 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice98 : Part6Nat.slice 0 3575 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice99 : Part6Nat.slice 0 3575 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice100 : Part6Nat.slice 0 3575 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice101 : Part6Nat.slice 0 3575 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice102 : Part6Nat.slice 0 3575 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice103 : Part6Nat.slice 0 3575 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice104 : Part6Nat.slice 0 3575 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice105 : Part6Nat.slice 0 3575 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice106 : Part6Nat.slice 0 3575 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice107 : Part6Nat.slice 0 3575 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice108 : Part6Nat.slice 0 3575 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice109 : Part6Nat.slice 0 3575 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice110 : Part6Nat.slice 0 3575 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice111 : Part6Nat.slice 0 3575 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice112 : Part6Nat.slice 0 3575 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice113 : Part6Nat.slice 0 3575 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice114 : Part6Nat.slice 0 3575 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice115 : Part6Nat.slice 0 3575 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice116 : Part6Nat.slice 0 3575 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice117 : Part6Nat.slice 0 3575 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice118 : Part6Nat.slice 0 3575 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice119 : Part6Nat.slice 0 3575 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice120 : Part6Nat.slice 0 3575 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice121 : Part6Nat.slice 0 3575 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice122 : Part6Nat.slice 0 3575 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice123 : Part6Nat.slice 0 3575 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice124 : Part6Nat.slice 0 3575 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice125 : Part6Nat.slice 0 3575 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice126 : Part6Nat.slice 0 3575 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice127 : Part6Nat.slice 0 3575 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice128 : Part6Nat.slice 0 3575 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice129 : Part6Nat.slice 0 3575 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice130 : Part6Nat.slice 0 3575 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice131 : Part6Nat.slice 0 3575 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice132 : Part6Nat.slice 0 3575 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice133 : Part6Nat.slice 0 3575 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice134 : Part6Nat.slice 0 3575 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice135 : Part6Nat.slice 0 3575 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice136 : Part6Nat.slice 0 3575 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice137 : Part6Nat.slice 0 3575 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice138 : Part6Nat.slice 0 3575 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice139 : Part6Nat.slice 0 3575 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice140 : Part6Nat.slice 0 3575 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice141 : Part6Nat.slice 0 3575 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice142 : Part6Nat.slice 0 3575 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice143 : Part6Nat.slice 0 3575 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice144 : Part6Nat.slice 0 3575 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice145 : Part6Nat.slice 0 3575 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice146 : Part6Nat.slice 0 3575 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice147 : Part6Nat.slice 0 3575 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice148 : Part6Nat.slice 0 3575 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice149 : Part6Nat.slice 0 3575 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice150 : Part6Nat.slice 0 3575 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice151 : Part6Nat.slice 0 3575 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice152 : Part6Nat.slice 0 3575 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice153 : Part6Nat.slice 0 3575 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice154 : Part6Nat.slice 0 3575 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice155 : Part6Nat.slice 0 3575 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice156 : Part6Nat.slice 0 3575 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice157 : Part6Nat.slice 0 3575 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice158 : Part6Nat.slice 0 3575 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice159 : Part6Nat.slice 0 3575 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice160 : Part6Nat.slice 0 3575 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice161 : Part6Nat.slice 0 3575 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice162 : Part6Nat.slice 0 3575 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice163 : Part6Nat.slice 0 3575 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice164 : Part6Nat.slice 0 3575 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice165 : Part6Nat.slice 0 3575 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice166 : Part6Nat.slice 0 3575 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice167 : Part6Nat.slice 0 3575 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice168 : Part6Nat.slice 0 3575 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice169 : Part6Nat.slice 0 3575 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice170 : Part6Nat.slice 0 3575 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice171 : Part6Nat.slice 0 3575 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice172 : Part6Nat.slice 0 3575 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice173 : Part6Nat.slice 0 3575 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice174 : Part6Nat.slice 0 3575 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice175 : Part6Nat.slice 0 3575 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice176 : Part6Nat.slice 0 3575 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice177 : Part6Nat.slice 0 3575 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice178 : Part6Nat.slice 0 3575 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice179 : Part6Nat.slice 0 3575 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice180 : Part6Nat.slice 0 3575 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice181 : Part6Nat.slice 0 3575 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice182 : Part6Nat.slice 0 3575 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice183 : Part6Nat.slice 0 3575 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice184 : Part6Nat.slice 0 3575 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice185 : Part6Nat.slice 0 3575 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice186 : Part6Nat.slice 0 3575 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice187 : Part6Nat.slice 0 3575 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice188 : Part6Nat.slice 0 3575 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice189 : Part6Nat.slice 0 3575 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice190 : Part6Nat.slice 0 3575 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice191 : Part6Nat.slice 0 3575 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice192 : Part6Nat.slice 0 3575 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice193 : Part6Nat.slice 0 3575 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice194 : Part6Nat.slice 0 3575 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice195 : Part6Nat.slice 0 3575 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice196 : Part6Nat.slice 0 3575 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice197 : Part6Nat.slice 0 3575 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice198 : Part6Nat.slice 0 3575 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice199 : Part6Nat.slice 0 3575 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice200 : Part6Nat.slice 0 3575 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice201 : Part6Nat.slice 0 3575 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point205slice202 : Part6Nat.slice 0 3575 202 = true := by
  decide +kernel

public theorem point205 : stepCheck 0 3575 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point205slice0
  · exact point205slice1
  · exact point205slice2
  · exact point205slice3
  · exact point205slice4
  · exact point205slice5
  · exact point205slice6
  · exact point205slice7
  · exact point205slice8
  · exact point205slice9
  · exact point205slice10
  · exact point205slice11
  · exact point205slice12
  · exact point205slice13
  · exact point205slice14
  · exact point205slice15
  · exact point205slice16
  · exact point205slice17
  · exact point205slice18
  · exact point205slice19
  · exact point205slice20
  · exact point205slice21
  · exact point205slice22
  · exact point205slice23
  · exact point205slice24
  · exact point205slice25
  · exact point205slice26
  · exact point205slice27
  · exact point205slice28
  · exact point205slice29
  · exact point205slice30
  · exact point205slice31
  · exact point205slice32
  · exact point205slice33
  · exact point205slice34
  · exact point205slice35
  · exact point205slice36
  · exact point205slice37
  · exact point205slice38
  · exact point205slice39
  · exact point205slice40
  · exact point205slice41
  · exact point205slice42
  · exact point205slice43
  · exact point205slice44
  · exact point205slice45
  · exact point205slice46
  · exact point205slice47
  · exact point205slice48
  · exact point205slice49
  · exact point205slice50
  · exact point205slice51
  · exact point205slice52
  · exact point205slice53
  · exact point205slice54
  · exact point205slice55
  · exact point205slice56
  · exact point205slice57
  · exact point205slice58
  · exact point205slice59
  · exact point205slice60
  · exact point205slice61
  · exact point205slice62
  · exact point205slice63
  · exact point205slice64
  · exact point205slice65
  · exact point205slice66
  · exact point205slice67
  · exact point205slice68
  · exact point205slice69
  · exact point205slice70
  · exact point205slice71
  · exact point205slice72
  · exact point205slice73
  · exact point205slice74
  · exact point205slice75
  · exact point205slice76
  · exact point205slice77
  · exact point205slice78
  · exact point205slice79
  · exact point205slice80
  · exact point205slice81
  · exact point205slice82
  · exact point205slice83
  · exact point205slice84
  · exact point205slice85
  · exact point205slice86
  · exact point205slice87
  · exact point205slice88
  · exact point205slice89
  · exact point205slice90
  · exact point205slice91
  · exact point205slice92
  · exact point205slice93
  · exact point205slice94
  · exact point205slice95
  · exact point205slice96
  · exact point205slice97
  · exact point205slice98
  · exact point205slice99
  · exact point205slice100
  · exact point205slice101
  · exact point205slice102
  · exact point205slice103
  · exact point205slice104
  · exact point205slice105
  · exact point205slice106
  · exact point205slice107
  · exact point205slice108
  · exact point205slice109
  · exact point205slice110
  · exact point205slice111
  · exact point205slice112
  · exact point205slice113
  · exact point205slice114
  · exact point205slice115
  · exact point205slice116
  · exact point205slice117
  · exact point205slice118
  · exact point205slice119
  · exact point205slice120
  · exact point205slice121
  · exact point205slice122
  · exact point205slice123
  · exact point205slice124
  · exact point205slice125
  · exact point205slice126
  · exact point205slice127
  · exact point205slice128
  · exact point205slice129
  · exact point205slice130
  · exact point205slice131
  · exact point205slice132
  · exact point205slice133
  · exact point205slice134
  · exact point205slice135
  · exact point205slice136
  · exact point205slice137
  · exact point205slice138
  · exact point205slice139
  · exact point205slice140
  · exact point205slice141
  · exact point205slice142
  · exact point205slice143
  · exact point205slice144
  · exact point205slice145
  · exact point205slice146
  · exact point205slice147
  · exact point205slice148
  · exact point205slice149
  · exact point205slice150
  · exact point205slice151
  · exact point205slice152
  · exact point205slice153
  · exact point205slice154
  · exact point205slice155
  · exact point205slice156
  · exact point205slice157
  · exact point205slice158
  · exact point205slice159
  · exact point205slice160
  · exact point205slice161
  · exact point205slice162
  · exact point205slice163
  · exact point205slice164
  · exact point205slice165
  · exact point205slice166
  · exact point205slice167
  · exact point205slice168
  · exact point205slice169
  · exact point205slice170
  · exact point205slice171
  · exact point205slice172
  · exact point205slice173
  · exact point205slice174
  · exact point205slice175
  · exact point205slice176
  · exact point205slice177
  · exact point205slice178
  · exact point205slice179
  · exact point205slice180
  · exact point205slice181
  · exact point205slice182
  · exact point205slice183
  · exact point205slice184
  · exact point205slice185
  · exact point205slice186
  · exact point205slice187
  · exact point205slice188
  · exact point205slice189
  · exact point205slice190
  · exact point205slice191
  · exact point205slice192
  · exact point205slice193
  · exact point205slice194
  · exact point205slice195
  · exact point205slice196
  · exact point205slice197
  · exact point205slice198
  · exact point205slice199
  · exact point205slice200
  · exact point205slice201
  · exact point205slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
