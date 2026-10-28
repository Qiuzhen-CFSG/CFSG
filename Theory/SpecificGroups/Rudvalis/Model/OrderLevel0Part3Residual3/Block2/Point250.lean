module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 250

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point250slice0 : Part6Nat.slice 0 3989 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice1 : Part6Nat.slice 0 3989 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice2 : Part6Nat.slice 0 3989 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice3 : Part6Nat.slice 0 3989 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice4 : Part6Nat.slice 0 3989 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice5 : Part6Nat.slice 0 3989 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice6 : Part6Nat.slice 0 3989 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice7 : Part6Nat.slice 0 3989 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice8 : Part6Nat.slice 0 3989 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice9 : Part6Nat.slice 0 3989 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice10 : Part6Nat.slice 0 3989 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice11 : Part6Nat.slice 0 3989 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice12 : Part6Nat.slice 0 3989 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice13 : Part6Nat.slice 0 3989 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice14 : Part6Nat.slice 0 3989 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice15 : Part6Nat.slice 0 3989 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice16 : Part6Nat.slice 0 3989 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice17 : Part6Nat.slice 0 3989 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice18 : Part6Nat.slice 0 3989 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice19 : Part6Nat.slice 0 3989 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice20 : Part6Nat.slice 0 3989 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice21 : Part6Nat.slice 0 3989 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice22 : Part6Nat.slice 0 3989 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice23 : Part6Nat.slice 0 3989 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice24 : Part6Nat.slice 0 3989 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice25 : Part6Nat.slice 0 3989 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice26 : Part6Nat.slice 0 3989 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice27 : Part6Nat.slice 0 3989 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice28 : Part6Nat.slice 0 3989 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice29 : Part6Nat.slice 0 3989 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice30 : Part6Nat.slice 0 3989 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice31 : Part6Nat.slice 0 3989 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice32 : Part6Nat.slice 0 3989 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice33 : Part6Nat.slice 0 3989 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice34 : Part6Nat.slice 0 3989 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice35 : Part6Nat.slice 0 3989 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice36 : Part6Nat.slice 0 3989 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice37 : Part6Nat.slice 0 3989 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice38 : Part6Nat.slice 0 3989 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice39 : Part6Nat.slice 0 3989 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice40 : Part6Nat.slice 0 3989 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice41 : Part6Nat.slice 0 3989 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice42 : Part6Nat.slice 0 3989 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice43 : Part6Nat.slice 0 3989 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice44 : Part6Nat.slice 0 3989 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice45 : Part6Nat.slice 0 3989 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice46 : Part6Nat.slice 0 3989 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice47 : Part6Nat.slice 0 3989 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice48 : Part6Nat.slice 0 3989 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice49 : Part6Nat.slice 0 3989 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice50 : Part6Nat.slice 0 3989 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice51 : Part6Nat.slice 0 3989 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice52 : Part6Nat.slice 0 3989 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice53 : Part6Nat.slice 0 3989 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice54 : Part6Nat.slice 0 3989 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice55 : Part6Nat.slice 0 3989 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice56 : Part6Nat.slice 0 3989 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice57 : Part6Nat.slice 0 3989 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice58 : Part6Nat.slice 0 3989 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice59 : Part6Nat.slice 0 3989 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice60 : Part6Nat.slice 0 3989 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice61 : Part6Nat.slice 0 3989 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice62 : Part6Nat.slice 0 3989 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice63 : Part6Nat.slice 0 3989 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice64 : Part6Nat.slice 0 3989 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice65 : Part6Nat.slice 0 3989 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice66 : Part6Nat.slice 0 3989 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice67 : Part6Nat.slice 0 3989 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice68 : Part6Nat.slice 0 3989 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice69 : Part6Nat.slice 0 3989 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice70 : Part6Nat.slice 0 3989 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice71 : Part6Nat.slice 0 3989 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice72 : Part6Nat.slice 0 3989 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice73 : Part6Nat.slice 0 3989 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice74 : Part6Nat.slice 0 3989 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice75 : Part6Nat.slice 0 3989 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice76 : Part6Nat.slice 0 3989 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice77 : Part6Nat.slice 0 3989 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice78 : Part6Nat.slice 0 3989 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice79 : Part6Nat.slice 0 3989 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice80 : Part6Nat.slice 0 3989 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice81 : Part6Nat.slice 0 3989 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice82 : Part6Nat.slice 0 3989 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice83 : Part6Nat.slice 0 3989 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice84 : Part6Nat.slice 0 3989 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice85 : Part6Nat.slice 0 3989 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice86 : Part6Nat.slice 0 3989 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice87 : Part6Nat.slice 0 3989 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice88 : Part6Nat.slice 0 3989 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice89 : Part6Nat.slice 0 3989 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice90 : Part6Nat.slice 0 3989 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice91 : Part6Nat.slice 0 3989 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice92 : Part6Nat.slice 0 3989 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice93 : Part6Nat.slice 0 3989 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice94 : Part6Nat.slice 0 3989 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice95 : Part6Nat.slice 0 3989 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice96 : Part6Nat.slice 0 3989 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice97 : Part6Nat.slice 0 3989 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice98 : Part6Nat.slice 0 3989 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice99 : Part6Nat.slice 0 3989 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice100 : Part6Nat.slice 0 3989 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice101 : Part6Nat.slice 0 3989 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice102 : Part6Nat.slice 0 3989 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice103 : Part6Nat.slice 0 3989 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice104 : Part6Nat.slice 0 3989 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice105 : Part6Nat.slice 0 3989 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice106 : Part6Nat.slice 0 3989 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice107 : Part6Nat.slice 0 3989 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice108 : Part6Nat.slice 0 3989 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice109 : Part6Nat.slice 0 3989 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice110 : Part6Nat.slice 0 3989 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice111 : Part6Nat.slice 0 3989 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice112 : Part6Nat.slice 0 3989 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice113 : Part6Nat.slice 0 3989 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice114 : Part6Nat.slice 0 3989 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice115 : Part6Nat.slice 0 3989 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice116 : Part6Nat.slice 0 3989 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice117 : Part6Nat.slice 0 3989 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice118 : Part6Nat.slice 0 3989 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice119 : Part6Nat.slice 0 3989 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice120 : Part6Nat.slice 0 3989 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice121 : Part6Nat.slice 0 3989 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice122 : Part6Nat.slice 0 3989 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice123 : Part6Nat.slice 0 3989 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice124 : Part6Nat.slice 0 3989 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice125 : Part6Nat.slice 0 3989 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice126 : Part6Nat.slice 0 3989 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice127 : Part6Nat.slice 0 3989 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice128 : Part6Nat.slice 0 3989 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice129 : Part6Nat.slice 0 3989 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice130 : Part6Nat.slice 0 3989 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice131 : Part6Nat.slice 0 3989 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice132 : Part6Nat.slice 0 3989 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice133 : Part6Nat.slice 0 3989 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice134 : Part6Nat.slice 0 3989 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice135 : Part6Nat.slice 0 3989 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice136 : Part6Nat.slice 0 3989 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice137 : Part6Nat.slice 0 3989 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice138 : Part6Nat.slice 0 3989 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice139 : Part6Nat.slice 0 3989 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice140 : Part6Nat.slice 0 3989 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice141 : Part6Nat.slice 0 3989 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice142 : Part6Nat.slice 0 3989 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice143 : Part6Nat.slice 0 3989 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice144 : Part6Nat.slice 0 3989 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice145 : Part6Nat.slice 0 3989 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice146 : Part6Nat.slice 0 3989 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice147 : Part6Nat.slice 0 3989 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice148 : Part6Nat.slice 0 3989 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice149 : Part6Nat.slice 0 3989 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice150 : Part6Nat.slice 0 3989 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice151 : Part6Nat.slice 0 3989 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice152 : Part6Nat.slice 0 3989 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice153 : Part6Nat.slice 0 3989 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice154 : Part6Nat.slice 0 3989 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice155 : Part6Nat.slice 0 3989 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice156 : Part6Nat.slice 0 3989 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice157 : Part6Nat.slice 0 3989 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice158 : Part6Nat.slice 0 3989 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice159 : Part6Nat.slice 0 3989 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice160 : Part6Nat.slice 0 3989 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice161 : Part6Nat.slice 0 3989 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice162 : Part6Nat.slice 0 3989 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice163 : Part6Nat.slice 0 3989 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice164 : Part6Nat.slice 0 3989 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice165 : Part6Nat.slice 0 3989 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice166 : Part6Nat.slice 0 3989 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice167 : Part6Nat.slice 0 3989 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice168 : Part6Nat.slice 0 3989 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice169 : Part6Nat.slice 0 3989 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice170 : Part6Nat.slice 0 3989 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice171 : Part6Nat.slice 0 3989 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice172 : Part6Nat.slice 0 3989 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice173 : Part6Nat.slice 0 3989 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice174 : Part6Nat.slice 0 3989 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice175 : Part6Nat.slice 0 3989 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice176 : Part6Nat.slice 0 3989 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice177 : Part6Nat.slice 0 3989 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice178 : Part6Nat.slice 0 3989 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice179 : Part6Nat.slice 0 3989 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice180 : Part6Nat.slice 0 3989 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice181 : Part6Nat.slice 0 3989 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice182 : Part6Nat.slice 0 3989 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice183 : Part6Nat.slice 0 3989 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice184 : Part6Nat.slice 0 3989 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice185 : Part6Nat.slice 0 3989 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice186 : Part6Nat.slice 0 3989 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice187 : Part6Nat.slice 0 3989 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice188 : Part6Nat.slice 0 3989 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice189 : Part6Nat.slice 0 3989 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice190 : Part6Nat.slice 0 3989 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice191 : Part6Nat.slice 0 3989 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice192 : Part6Nat.slice 0 3989 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice193 : Part6Nat.slice 0 3989 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice194 : Part6Nat.slice 0 3989 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice195 : Part6Nat.slice 0 3989 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice196 : Part6Nat.slice 0 3989 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice197 : Part6Nat.slice 0 3989 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice198 : Part6Nat.slice 0 3989 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice199 : Part6Nat.slice 0 3989 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice200 : Part6Nat.slice 0 3989 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice201 : Part6Nat.slice 0 3989 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point250slice202 : Part6Nat.slice 0 3989 202 = true := by
  decide +kernel

public theorem point250 : stepCheck 0 3989 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point250slice0
  · exact point250slice1
  · exact point250slice2
  · exact point250slice3
  · exact point250slice4
  · exact point250slice5
  · exact point250slice6
  · exact point250slice7
  · exact point250slice8
  · exact point250slice9
  · exact point250slice10
  · exact point250slice11
  · exact point250slice12
  · exact point250slice13
  · exact point250slice14
  · exact point250slice15
  · exact point250slice16
  · exact point250slice17
  · exact point250slice18
  · exact point250slice19
  · exact point250slice20
  · exact point250slice21
  · exact point250slice22
  · exact point250slice23
  · exact point250slice24
  · exact point250slice25
  · exact point250slice26
  · exact point250slice27
  · exact point250slice28
  · exact point250slice29
  · exact point250slice30
  · exact point250slice31
  · exact point250slice32
  · exact point250slice33
  · exact point250slice34
  · exact point250slice35
  · exact point250slice36
  · exact point250slice37
  · exact point250slice38
  · exact point250slice39
  · exact point250slice40
  · exact point250slice41
  · exact point250slice42
  · exact point250slice43
  · exact point250slice44
  · exact point250slice45
  · exact point250slice46
  · exact point250slice47
  · exact point250slice48
  · exact point250slice49
  · exact point250slice50
  · exact point250slice51
  · exact point250slice52
  · exact point250slice53
  · exact point250slice54
  · exact point250slice55
  · exact point250slice56
  · exact point250slice57
  · exact point250slice58
  · exact point250slice59
  · exact point250slice60
  · exact point250slice61
  · exact point250slice62
  · exact point250slice63
  · exact point250slice64
  · exact point250slice65
  · exact point250slice66
  · exact point250slice67
  · exact point250slice68
  · exact point250slice69
  · exact point250slice70
  · exact point250slice71
  · exact point250slice72
  · exact point250slice73
  · exact point250slice74
  · exact point250slice75
  · exact point250slice76
  · exact point250slice77
  · exact point250slice78
  · exact point250slice79
  · exact point250slice80
  · exact point250slice81
  · exact point250slice82
  · exact point250slice83
  · exact point250slice84
  · exact point250slice85
  · exact point250slice86
  · exact point250slice87
  · exact point250slice88
  · exact point250slice89
  · exact point250slice90
  · exact point250slice91
  · exact point250slice92
  · exact point250slice93
  · exact point250slice94
  · exact point250slice95
  · exact point250slice96
  · exact point250slice97
  · exact point250slice98
  · exact point250slice99
  · exact point250slice100
  · exact point250slice101
  · exact point250slice102
  · exact point250slice103
  · exact point250slice104
  · exact point250slice105
  · exact point250slice106
  · exact point250slice107
  · exact point250slice108
  · exact point250slice109
  · exact point250slice110
  · exact point250slice111
  · exact point250slice112
  · exact point250slice113
  · exact point250slice114
  · exact point250slice115
  · exact point250slice116
  · exact point250slice117
  · exact point250slice118
  · exact point250slice119
  · exact point250slice120
  · exact point250slice121
  · exact point250slice122
  · exact point250slice123
  · exact point250slice124
  · exact point250slice125
  · exact point250slice126
  · exact point250slice127
  · exact point250slice128
  · exact point250slice129
  · exact point250slice130
  · exact point250slice131
  · exact point250slice132
  · exact point250slice133
  · exact point250slice134
  · exact point250slice135
  · exact point250slice136
  · exact point250slice137
  · exact point250slice138
  · exact point250slice139
  · exact point250slice140
  · exact point250slice141
  · exact point250slice142
  · exact point250slice143
  · exact point250slice144
  · exact point250slice145
  · exact point250slice146
  · exact point250slice147
  · exact point250slice148
  · exact point250slice149
  · exact point250slice150
  · exact point250slice151
  · exact point250slice152
  · exact point250slice153
  · exact point250slice154
  · exact point250slice155
  · exact point250slice156
  · exact point250slice157
  · exact point250slice158
  · exact point250slice159
  · exact point250slice160
  · exact point250slice161
  · exact point250slice162
  · exact point250slice163
  · exact point250slice164
  · exact point250slice165
  · exact point250slice166
  · exact point250slice167
  · exact point250slice168
  · exact point250slice169
  · exact point250slice170
  · exact point250slice171
  · exact point250slice172
  · exact point250slice173
  · exact point250slice174
  · exact point250slice175
  · exact point250slice176
  · exact point250slice177
  · exact point250slice178
  · exact point250slice179
  · exact point250slice180
  · exact point250slice181
  · exact point250slice182
  · exact point250slice183
  · exact point250slice184
  · exact point250slice185
  · exact point250slice186
  · exact point250slice187
  · exact point250slice188
  · exact point250slice189
  · exact point250slice190
  · exact point250slice191
  · exact point250slice192
  · exact point250slice193
  · exact point250slice194
  · exact point250slice195
  · exact point250slice196
  · exact point250slice197
  · exact point250slice198
  · exact point250slice199
  · exact point250slice200
  · exact point250slice201
  · exact point250slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
