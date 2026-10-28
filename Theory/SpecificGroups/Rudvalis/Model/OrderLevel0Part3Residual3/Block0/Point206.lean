module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 206

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point206slice0 : Part6Nat.slice 0 3577 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice1 : Part6Nat.slice 0 3577 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice2 : Part6Nat.slice 0 3577 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice3 : Part6Nat.slice 0 3577 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice4 : Part6Nat.slice 0 3577 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice5 : Part6Nat.slice 0 3577 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice6 : Part6Nat.slice 0 3577 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice7 : Part6Nat.slice 0 3577 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice8 : Part6Nat.slice 0 3577 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice9 : Part6Nat.slice 0 3577 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice10 : Part6Nat.slice 0 3577 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice11 : Part6Nat.slice 0 3577 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice12 : Part6Nat.slice 0 3577 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice13 : Part6Nat.slice 0 3577 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice14 : Part6Nat.slice 0 3577 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice15 : Part6Nat.slice 0 3577 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice16 : Part6Nat.slice 0 3577 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice17 : Part6Nat.slice 0 3577 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice18 : Part6Nat.slice 0 3577 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice19 : Part6Nat.slice 0 3577 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice20 : Part6Nat.slice 0 3577 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice21 : Part6Nat.slice 0 3577 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice22 : Part6Nat.slice 0 3577 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice23 : Part6Nat.slice 0 3577 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice24 : Part6Nat.slice 0 3577 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice25 : Part6Nat.slice 0 3577 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice26 : Part6Nat.slice 0 3577 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice27 : Part6Nat.slice 0 3577 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice28 : Part6Nat.slice 0 3577 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice29 : Part6Nat.slice 0 3577 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice30 : Part6Nat.slice 0 3577 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice31 : Part6Nat.slice 0 3577 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice32 : Part6Nat.slice 0 3577 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice33 : Part6Nat.slice 0 3577 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice34 : Part6Nat.slice 0 3577 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice35 : Part6Nat.slice 0 3577 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice36 : Part6Nat.slice 0 3577 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice37 : Part6Nat.slice 0 3577 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice38 : Part6Nat.slice 0 3577 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice39 : Part6Nat.slice 0 3577 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice40 : Part6Nat.slice 0 3577 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice41 : Part6Nat.slice 0 3577 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice42 : Part6Nat.slice 0 3577 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice43 : Part6Nat.slice 0 3577 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice44 : Part6Nat.slice 0 3577 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice45 : Part6Nat.slice 0 3577 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice46 : Part6Nat.slice 0 3577 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice47 : Part6Nat.slice 0 3577 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice48 : Part6Nat.slice 0 3577 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice49 : Part6Nat.slice 0 3577 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice50 : Part6Nat.slice 0 3577 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice51 : Part6Nat.slice 0 3577 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice52 : Part6Nat.slice 0 3577 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice53 : Part6Nat.slice 0 3577 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice54 : Part6Nat.slice 0 3577 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice55 : Part6Nat.slice 0 3577 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice56 : Part6Nat.slice 0 3577 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice57 : Part6Nat.slice 0 3577 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice58 : Part6Nat.slice 0 3577 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice59 : Part6Nat.slice 0 3577 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice60 : Part6Nat.slice 0 3577 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice61 : Part6Nat.slice 0 3577 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice62 : Part6Nat.slice 0 3577 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice63 : Part6Nat.slice 0 3577 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice64 : Part6Nat.slice 0 3577 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice65 : Part6Nat.slice 0 3577 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice66 : Part6Nat.slice 0 3577 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice67 : Part6Nat.slice 0 3577 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice68 : Part6Nat.slice 0 3577 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice69 : Part6Nat.slice 0 3577 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice70 : Part6Nat.slice 0 3577 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice71 : Part6Nat.slice 0 3577 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice72 : Part6Nat.slice 0 3577 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice73 : Part6Nat.slice 0 3577 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice74 : Part6Nat.slice 0 3577 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice75 : Part6Nat.slice 0 3577 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice76 : Part6Nat.slice 0 3577 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice77 : Part6Nat.slice 0 3577 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice78 : Part6Nat.slice 0 3577 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice79 : Part6Nat.slice 0 3577 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice80 : Part6Nat.slice 0 3577 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice81 : Part6Nat.slice 0 3577 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice82 : Part6Nat.slice 0 3577 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice83 : Part6Nat.slice 0 3577 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice84 : Part6Nat.slice 0 3577 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice85 : Part6Nat.slice 0 3577 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice86 : Part6Nat.slice 0 3577 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice87 : Part6Nat.slice 0 3577 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice88 : Part6Nat.slice 0 3577 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice89 : Part6Nat.slice 0 3577 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice90 : Part6Nat.slice 0 3577 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice91 : Part6Nat.slice 0 3577 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice92 : Part6Nat.slice 0 3577 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice93 : Part6Nat.slice 0 3577 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice94 : Part6Nat.slice 0 3577 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice95 : Part6Nat.slice 0 3577 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice96 : Part6Nat.slice 0 3577 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice97 : Part6Nat.slice 0 3577 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice98 : Part6Nat.slice 0 3577 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice99 : Part6Nat.slice 0 3577 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice100 : Part6Nat.slice 0 3577 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice101 : Part6Nat.slice 0 3577 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice102 : Part6Nat.slice 0 3577 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice103 : Part6Nat.slice 0 3577 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice104 : Part6Nat.slice 0 3577 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice105 : Part6Nat.slice 0 3577 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice106 : Part6Nat.slice 0 3577 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice107 : Part6Nat.slice 0 3577 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice108 : Part6Nat.slice 0 3577 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice109 : Part6Nat.slice 0 3577 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice110 : Part6Nat.slice 0 3577 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice111 : Part6Nat.slice 0 3577 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice112 : Part6Nat.slice 0 3577 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice113 : Part6Nat.slice 0 3577 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice114 : Part6Nat.slice 0 3577 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice115 : Part6Nat.slice 0 3577 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice116 : Part6Nat.slice 0 3577 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice117 : Part6Nat.slice 0 3577 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice118 : Part6Nat.slice 0 3577 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice119 : Part6Nat.slice 0 3577 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice120 : Part6Nat.slice 0 3577 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice121 : Part6Nat.slice 0 3577 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice122 : Part6Nat.slice 0 3577 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice123 : Part6Nat.slice 0 3577 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice124 : Part6Nat.slice 0 3577 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice125 : Part6Nat.slice 0 3577 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice126 : Part6Nat.slice 0 3577 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice127 : Part6Nat.slice 0 3577 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice128 : Part6Nat.slice 0 3577 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice129 : Part6Nat.slice 0 3577 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice130 : Part6Nat.slice 0 3577 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice131 : Part6Nat.slice 0 3577 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice132 : Part6Nat.slice 0 3577 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice133 : Part6Nat.slice 0 3577 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice134 : Part6Nat.slice 0 3577 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice135 : Part6Nat.slice 0 3577 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice136 : Part6Nat.slice 0 3577 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice137 : Part6Nat.slice 0 3577 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice138 : Part6Nat.slice 0 3577 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice139 : Part6Nat.slice 0 3577 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice140 : Part6Nat.slice 0 3577 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice141 : Part6Nat.slice 0 3577 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice142 : Part6Nat.slice 0 3577 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice143 : Part6Nat.slice 0 3577 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice144 : Part6Nat.slice 0 3577 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice145 : Part6Nat.slice 0 3577 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice146 : Part6Nat.slice 0 3577 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice147 : Part6Nat.slice 0 3577 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice148 : Part6Nat.slice 0 3577 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice149 : Part6Nat.slice 0 3577 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice150 : Part6Nat.slice 0 3577 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice151 : Part6Nat.slice 0 3577 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice152 : Part6Nat.slice 0 3577 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice153 : Part6Nat.slice 0 3577 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice154 : Part6Nat.slice 0 3577 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice155 : Part6Nat.slice 0 3577 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice156 : Part6Nat.slice 0 3577 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice157 : Part6Nat.slice 0 3577 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice158 : Part6Nat.slice 0 3577 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice159 : Part6Nat.slice 0 3577 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice160 : Part6Nat.slice 0 3577 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice161 : Part6Nat.slice 0 3577 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice162 : Part6Nat.slice 0 3577 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice163 : Part6Nat.slice 0 3577 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice164 : Part6Nat.slice 0 3577 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice165 : Part6Nat.slice 0 3577 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice166 : Part6Nat.slice 0 3577 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice167 : Part6Nat.slice 0 3577 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice168 : Part6Nat.slice 0 3577 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice169 : Part6Nat.slice 0 3577 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice170 : Part6Nat.slice 0 3577 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice171 : Part6Nat.slice 0 3577 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice172 : Part6Nat.slice 0 3577 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice173 : Part6Nat.slice 0 3577 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice174 : Part6Nat.slice 0 3577 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice175 : Part6Nat.slice 0 3577 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice176 : Part6Nat.slice 0 3577 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice177 : Part6Nat.slice 0 3577 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice178 : Part6Nat.slice 0 3577 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice179 : Part6Nat.slice 0 3577 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice180 : Part6Nat.slice 0 3577 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice181 : Part6Nat.slice 0 3577 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice182 : Part6Nat.slice 0 3577 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice183 : Part6Nat.slice 0 3577 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice184 : Part6Nat.slice 0 3577 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice185 : Part6Nat.slice 0 3577 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice186 : Part6Nat.slice 0 3577 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice187 : Part6Nat.slice 0 3577 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice188 : Part6Nat.slice 0 3577 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice189 : Part6Nat.slice 0 3577 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice190 : Part6Nat.slice 0 3577 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice191 : Part6Nat.slice 0 3577 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice192 : Part6Nat.slice 0 3577 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice193 : Part6Nat.slice 0 3577 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice194 : Part6Nat.slice 0 3577 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice195 : Part6Nat.slice 0 3577 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice196 : Part6Nat.slice 0 3577 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice197 : Part6Nat.slice 0 3577 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice198 : Part6Nat.slice 0 3577 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice199 : Part6Nat.slice 0 3577 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice200 : Part6Nat.slice 0 3577 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice201 : Part6Nat.slice 0 3577 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point206slice202 : Part6Nat.slice 0 3577 202 = true := by
  decide +kernel

public theorem point206 : stepCheck 0 3577 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point206slice0
  · exact point206slice1
  · exact point206slice2
  · exact point206slice3
  · exact point206slice4
  · exact point206slice5
  · exact point206slice6
  · exact point206slice7
  · exact point206slice8
  · exact point206slice9
  · exact point206slice10
  · exact point206slice11
  · exact point206slice12
  · exact point206slice13
  · exact point206slice14
  · exact point206slice15
  · exact point206slice16
  · exact point206slice17
  · exact point206slice18
  · exact point206slice19
  · exact point206slice20
  · exact point206slice21
  · exact point206slice22
  · exact point206slice23
  · exact point206slice24
  · exact point206slice25
  · exact point206slice26
  · exact point206slice27
  · exact point206slice28
  · exact point206slice29
  · exact point206slice30
  · exact point206slice31
  · exact point206slice32
  · exact point206slice33
  · exact point206slice34
  · exact point206slice35
  · exact point206slice36
  · exact point206slice37
  · exact point206slice38
  · exact point206slice39
  · exact point206slice40
  · exact point206slice41
  · exact point206slice42
  · exact point206slice43
  · exact point206slice44
  · exact point206slice45
  · exact point206slice46
  · exact point206slice47
  · exact point206slice48
  · exact point206slice49
  · exact point206slice50
  · exact point206slice51
  · exact point206slice52
  · exact point206slice53
  · exact point206slice54
  · exact point206slice55
  · exact point206slice56
  · exact point206slice57
  · exact point206slice58
  · exact point206slice59
  · exact point206slice60
  · exact point206slice61
  · exact point206slice62
  · exact point206slice63
  · exact point206slice64
  · exact point206slice65
  · exact point206slice66
  · exact point206slice67
  · exact point206slice68
  · exact point206slice69
  · exact point206slice70
  · exact point206slice71
  · exact point206slice72
  · exact point206slice73
  · exact point206slice74
  · exact point206slice75
  · exact point206slice76
  · exact point206slice77
  · exact point206slice78
  · exact point206slice79
  · exact point206slice80
  · exact point206slice81
  · exact point206slice82
  · exact point206slice83
  · exact point206slice84
  · exact point206slice85
  · exact point206slice86
  · exact point206slice87
  · exact point206slice88
  · exact point206slice89
  · exact point206slice90
  · exact point206slice91
  · exact point206slice92
  · exact point206slice93
  · exact point206slice94
  · exact point206slice95
  · exact point206slice96
  · exact point206slice97
  · exact point206slice98
  · exact point206slice99
  · exact point206slice100
  · exact point206slice101
  · exact point206slice102
  · exact point206slice103
  · exact point206slice104
  · exact point206slice105
  · exact point206slice106
  · exact point206slice107
  · exact point206slice108
  · exact point206slice109
  · exact point206slice110
  · exact point206slice111
  · exact point206slice112
  · exact point206slice113
  · exact point206slice114
  · exact point206slice115
  · exact point206slice116
  · exact point206slice117
  · exact point206slice118
  · exact point206slice119
  · exact point206slice120
  · exact point206slice121
  · exact point206slice122
  · exact point206slice123
  · exact point206slice124
  · exact point206slice125
  · exact point206slice126
  · exact point206slice127
  · exact point206slice128
  · exact point206slice129
  · exact point206slice130
  · exact point206slice131
  · exact point206slice132
  · exact point206slice133
  · exact point206slice134
  · exact point206slice135
  · exact point206slice136
  · exact point206slice137
  · exact point206slice138
  · exact point206slice139
  · exact point206slice140
  · exact point206slice141
  · exact point206slice142
  · exact point206slice143
  · exact point206slice144
  · exact point206slice145
  · exact point206slice146
  · exact point206slice147
  · exact point206slice148
  · exact point206slice149
  · exact point206slice150
  · exact point206slice151
  · exact point206slice152
  · exact point206slice153
  · exact point206slice154
  · exact point206slice155
  · exact point206slice156
  · exact point206slice157
  · exact point206slice158
  · exact point206slice159
  · exact point206slice160
  · exact point206slice161
  · exact point206slice162
  · exact point206slice163
  · exact point206slice164
  · exact point206slice165
  · exact point206slice166
  · exact point206slice167
  · exact point206slice168
  · exact point206slice169
  · exact point206slice170
  · exact point206slice171
  · exact point206slice172
  · exact point206slice173
  · exact point206slice174
  · exact point206slice175
  · exact point206slice176
  · exact point206slice177
  · exact point206slice178
  · exact point206slice179
  · exact point206slice180
  · exact point206slice181
  · exact point206slice182
  · exact point206slice183
  · exact point206slice184
  · exact point206slice185
  · exact point206slice186
  · exact point206slice187
  · exact point206slice188
  · exact point206slice189
  · exact point206slice190
  · exact point206slice191
  · exact point206slice192
  · exact point206slice193
  · exact point206slice194
  · exact point206slice195
  · exact point206slice196
  · exact point206slice197
  · exact point206slice198
  · exact point206slice199
  · exact point206slice200
  · exact point206slice201
  · exact point206slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
