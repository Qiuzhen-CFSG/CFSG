module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 230

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point230slice0 : Part6Nat.slice 0 3852 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice1 : Part6Nat.slice 0 3852 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice2 : Part6Nat.slice 0 3852 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice3 : Part6Nat.slice 0 3852 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice4 : Part6Nat.slice 0 3852 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice5 : Part6Nat.slice 0 3852 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice6 : Part6Nat.slice 0 3852 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice7 : Part6Nat.slice 0 3852 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice8 : Part6Nat.slice 0 3852 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice9 : Part6Nat.slice 0 3852 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice10 : Part6Nat.slice 0 3852 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice11 : Part6Nat.slice 0 3852 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice12 : Part6Nat.slice 0 3852 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice13 : Part6Nat.slice 0 3852 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice14 : Part6Nat.slice 0 3852 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice15 : Part6Nat.slice 0 3852 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice16 : Part6Nat.slice 0 3852 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice17 : Part6Nat.slice 0 3852 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice18 : Part6Nat.slice 0 3852 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice19 : Part6Nat.slice 0 3852 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice20 : Part6Nat.slice 0 3852 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice21 : Part6Nat.slice 0 3852 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice22 : Part6Nat.slice 0 3852 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice23 : Part6Nat.slice 0 3852 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice24 : Part6Nat.slice 0 3852 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice25 : Part6Nat.slice 0 3852 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice26 : Part6Nat.slice 0 3852 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice27 : Part6Nat.slice 0 3852 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice28 : Part6Nat.slice 0 3852 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice29 : Part6Nat.slice 0 3852 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice30 : Part6Nat.slice 0 3852 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice31 : Part6Nat.slice 0 3852 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice32 : Part6Nat.slice 0 3852 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice33 : Part6Nat.slice 0 3852 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice34 : Part6Nat.slice 0 3852 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice35 : Part6Nat.slice 0 3852 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice36 : Part6Nat.slice 0 3852 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice37 : Part6Nat.slice 0 3852 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice38 : Part6Nat.slice 0 3852 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice39 : Part6Nat.slice 0 3852 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice40 : Part6Nat.slice 0 3852 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice41 : Part6Nat.slice 0 3852 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice42 : Part6Nat.slice 0 3852 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice43 : Part6Nat.slice 0 3852 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice44 : Part6Nat.slice 0 3852 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice45 : Part6Nat.slice 0 3852 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice46 : Part6Nat.slice 0 3852 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice47 : Part6Nat.slice 0 3852 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice48 : Part6Nat.slice 0 3852 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice49 : Part6Nat.slice 0 3852 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice50 : Part6Nat.slice 0 3852 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice51 : Part6Nat.slice 0 3852 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice52 : Part6Nat.slice 0 3852 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice53 : Part6Nat.slice 0 3852 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice54 : Part6Nat.slice 0 3852 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice55 : Part6Nat.slice 0 3852 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice56 : Part6Nat.slice 0 3852 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice57 : Part6Nat.slice 0 3852 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice58 : Part6Nat.slice 0 3852 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice59 : Part6Nat.slice 0 3852 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice60 : Part6Nat.slice 0 3852 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice61 : Part6Nat.slice 0 3852 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice62 : Part6Nat.slice 0 3852 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice63 : Part6Nat.slice 0 3852 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice64 : Part6Nat.slice 0 3852 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice65 : Part6Nat.slice 0 3852 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice66 : Part6Nat.slice 0 3852 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice67 : Part6Nat.slice 0 3852 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice68 : Part6Nat.slice 0 3852 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice69 : Part6Nat.slice 0 3852 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice70 : Part6Nat.slice 0 3852 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice71 : Part6Nat.slice 0 3852 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice72 : Part6Nat.slice 0 3852 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice73 : Part6Nat.slice 0 3852 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice74 : Part6Nat.slice 0 3852 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice75 : Part6Nat.slice 0 3852 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice76 : Part6Nat.slice 0 3852 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice77 : Part6Nat.slice 0 3852 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice78 : Part6Nat.slice 0 3852 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice79 : Part6Nat.slice 0 3852 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice80 : Part6Nat.slice 0 3852 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice81 : Part6Nat.slice 0 3852 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice82 : Part6Nat.slice 0 3852 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice83 : Part6Nat.slice 0 3852 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice84 : Part6Nat.slice 0 3852 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice85 : Part6Nat.slice 0 3852 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice86 : Part6Nat.slice 0 3852 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice87 : Part6Nat.slice 0 3852 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice88 : Part6Nat.slice 0 3852 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice89 : Part6Nat.slice 0 3852 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice90 : Part6Nat.slice 0 3852 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice91 : Part6Nat.slice 0 3852 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice92 : Part6Nat.slice 0 3852 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice93 : Part6Nat.slice 0 3852 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice94 : Part6Nat.slice 0 3852 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice95 : Part6Nat.slice 0 3852 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice96 : Part6Nat.slice 0 3852 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice97 : Part6Nat.slice 0 3852 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice98 : Part6Nat.slice 0 3852 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice99 : Part6Nat.slice 0 3852 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice100 : Part6Nat.slice 0 3852 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice101 : Part6Nat.slice 0 3852 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice102 : Part6Nat.slice 0 3852 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice103 : Part6Nat.slice 0 3852 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice104 : Part6Nat.slice 0 3852 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice105 : Part6Nat.slice 0 3852 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice106 : Part6Nat.slice 0 3852 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice107 : Part6Nat.slice 0 3852 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice108 : Part6Nat.slice 0 3852 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice109 : Part6Nat.slice 0 3852 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice110 : Part6Nat.slice 0 3852 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice111 : Part6Nat.slice 0 3852 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice112 : Part6Nat.slice 0 3852 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice113 : Part6Nat.slice 0 3852 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice114 : Part6Nat.slice 0 3852 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice115 : Part6Nat.slice 0 3852 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice116 : Part6Nat.slice 0 3852 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice117 : Part6Nat.slice 0 3852 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice118 : Part6Nat.slice 0 3852 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice119 : Part6Nat.slice 0 3852 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice120 : Part6Nat.slice 0 3852 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice121 : Part6Nat.slice 0 3852 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice122 : Part6Nat.slice 0 3852 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice123 : Part6Nat.slice 0 3852 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice124 : Part6Nat.slice 0 3852 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice125 : Part6Nat.slice 0 3852 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice126 : Part6Nat.slice 0 3852 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice127 : Part6Nat.slice 0 3852 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice128 : Part6Nat.slice 0 3852 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice129 : Part6Nat.slice 0 3852 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice130 : Part6Nat.slice 0 3852 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice131 : Part6Nat.slice 0 3852 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice132 : Part6Nat.slice 0 3852 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice133 : Part6Nat.slice 0 3852 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice134 : Part6Nat.slice 0 3852 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice135 : Part6Nat.slice 0 3852 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice136 : Part6Nat.slice 0 3852 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice137 : Part6Nat.slice 0 3852 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice138 : Part6Nat.slice 0 3852 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice139 : Part6Nat.slice 0 3852 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice140 : Part6Nat.slice 0 3852 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice141 : Part6Nat.slice 0 3852 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice142 : Part6Nat.slice 0 3852 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice143 : Part6Nat.slice 0 3852 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice144 : Part6Nat.slice 0 3852 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice145 : Part6Nat.slice 0 3852 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice146 : Part6Nat.slice 0 3852 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice147 : Part6Nat.slice 0 3852 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice148 : Part6Nat.slice 0 3852 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice149 : Part6Nat.slice 0 3852 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice150 : Part6Nat.slice 0 3852 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice151 : Part6Nat.slice 0 3852 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice152 : Part6Nat.slice 0 3852 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice153 : Part6Nat.slice 0 3852 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice154 : Part6Nat.slice 0 3852 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice155 : Part6Nat.slice 0 3852 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice156 : Part6Nat.slice 0 3852 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice157 : Part6Nat.slice 0 3852 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice158 : Part6Nat.slice 0 3852 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice159 : Part6Nat.slice 0 3852 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice160 : Part6Nat.slice 0 3852 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice161 : Part6Nat.slice 0 3852 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice162 : Part6Nat.slice 0 3852 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice163 : Part6Nat.slice 0 3852 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice164 : Part6Nat.slice 0 3852 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice165 : Part6Nat.slice 0 3852 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice166 : Part6Nat.slice 0 3852 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice167 : Part6Nat.slice 0 3852 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice168 : Part6Nat.slice 0 3852 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice169 : Part6Nat.slice 0 3852 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice170 : Part6Nat.slice 0 3852 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice171 : Part6Nat.slice 0 3852 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice172 : Part6Nat.slice 0 3852 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice173 : Part6Nat.slice 0 3852 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice174 : Part6Nat.slice 0 3852 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice175 : Part6Nat.slice 0 3852 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice176 : Part6Nat.slice 0 3852 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice177 : Part6Nat.slice 0 3852 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice178 : Part6Nat.slice 0 3852 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice179 : Part6Nat.slice 0 3852 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice180 : Part6Nat.slice 0 3852 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice181 : Part6Nat.slice 0 3852 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice182 : Part6Nat.slice 0 3852 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice183 : Part6Nat.slice 0 3852 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice184 : Part6Nat.slice 0 3852 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice185 : Part6Nat.slice 0 3852 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice186 : Part6Nat.slice 0 3852 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice187 : Part6Nat.slice 0 3852 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice188 : Part6Nat.slice 0 3852 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice189 : Part6Nat.slice 0 3852 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice190 : Part6Nat.slice 0 3852 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice191 : Part6Nat.slice 0 3852 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice192 : Part6Nat.slice 0 3852 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice193 : Part6Nat.slice 0 3852 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice194 : Part6Nat.slice 0 3852 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice195 : Part6Nat.slice 0 3852 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice196 : Part6Nat.slice 0 3852 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice197 : Part6Nat.slice 0 3852 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice198 : Part6Nat.slice 0 3852 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice199 : Part6Nat.slice 0 3852 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice200 : Part6Nat.slice 0 3852 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice201 : Part6Nat.slice 0 3852 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point230slice202 : Part6Nat.slice 0 3852 202 = true := by
  decide +kernel

public theorem point230 : stepCheck 0 3852 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point230slice0
  · exact point230slice1
  · exact point230slice2
  · exact point230slice3
  · exact point230slice4
  · exact point230slice5
  · exact point230slice6
  · exact point230slice7
  · exact point230slice8
  · exact point230slice9
  · exact point230slice10
  · exact point230slice11
  · exact point230slice12
  · exact point230slice13
  · exact point230slice14
  · exact point230slice15
  · exact point230slice16
  · exact point230slice17
  · exact point230slice18
  · exact point230slice19
  · exact point230slice20
  · exact point230slice21
  · exact point230slice22
  · exact point230slice23
  · exact point230slice24
  · exact point230slice25
  · exact point230slice26
  · exact point230slice27
  · exact point230slice28
  · exact point230slice29
  · exact point230slice30
  · exact point230slice31
  · exact point230slice32
  · exact point230slice33
  · exact point230slice34
  · exact point230slice35
  · exact point230slice36
  · exact point230slice37
  · exact point230slice38
  · exact point230slice39
  · exact point230slice40
  · exact point230slice41
  · exact point230slice42
  · exact point230slice43
  · exact point230slice44
  · exact point230slice45
  · exact point230slice46
  · exact point230slice47
  · exact point230slice48
  · exact point230slice49
  · exact point230slice50
  · exact point230slice51
  · exact point230slice52
  · exact point230slice53
  · exact point230slice54
  · exact point230slice55
  · exact point230slice56
  · exact point230slice57
  · exact point230slice58
  · exact point230slice59
  · exact point230slice60
  · exact point230slice61
  · exact point230slice62
  · exact point230slice63
  · exact point230slice64
  · exact point230slice65
  · exact point230slice66
  · exact point230slice67
  · exact point230slice68
  · exact point230slice69
  · exact point230slice70
  · exact point230slice71
  · exact point230slice72
  · exact point230slice73
  · exact point230slice74
  · exact point230slice75
  · exact point230slice76
  · exact point230slice77
  · exact point230slice78
  · exact point230slice79
  · exact point230slice80
  · exact point230slice81
  · exact point230slice82
  · exact point230slice83
  · exact point230slice84
  · exact point230slice85
  · exact point230slice86
  · exact point230slice87
  · exact point230slice88
  · exact point230slice89
  · exact point230slice90
  · exact point230slice91
  · exact point230slice92
  · exact point230slice93
  · exact point230slice94
  · exact point230slice95
  · exact point230slice96
  · exact point230slice97
  · exact point230slice98
  · exact point230slice99
  · exact point230slice100
  · exact point230slice101
  · exact point230slice102
  · exact point230slice103
  · exact point230slice104
  · exact point230slice105
  · exact point230slice106
  · exact point230slice107
  · exact point230slice108
  · exact point230slice109
  · exact point230slice110
  · exact point230slice111
  · exact point230slice112
  · exact point230slice113
  · exact point230slice114
  · exact point230slice115
  · exact point230slice116
  · exact point230slice117
  · exact point230slice118
  · exact point230slice119
  · exact point230slice120
  · exact point230slice121
  · exact point230slice122
  · exact point230slice123
  · exact point230slice124
  · exact point230slice125
  · exact point230slice126
  · exact point230slice127
  · exact point230slice128
  · exact point230slice129
  · exact point230slice130
  · exact point230slice131
  · exact point230slice132
  · exact point230slice133
  · exact point230slice134
  · exact point230slice135
  · exact point230slice136
  · exact point230slice137
  · exact point230slice138
  · exact point230slice139
  · exact point230slice140
  · exact point230slice141
  · exact point230slice142
  · exact point230slice143
  · exact point230slice144
  · exact point230slice145
  · exact point230slice146
  · exact point230slice147
  · exact point230slice148
  · exact point230slice149
  · exact point230slice150
  · exact point230slice151
  · exact point230slice152
  · exact point230slice153
  · exact point230slice154
  · exact point230slice155
  · exact point230slice156
  · exact point230slice157
  · exact point230slice158
  · exact point230slice159
  · exact point230slice160
  · exact point230slice161
  · exact point230slice162
  · exact point230slice163
  · exact point230slice164
  · exact point230slice165
  · exact point230slice166
  · exact point230slice167
  · exact point230slice168
  · exact point230slice169
  · exact point230slice170
  · exact point230slice171
  · exact point230slice172
  · exact point230slice173
  · exact point230slice174
  · exact point230slice175
  · exact point230slice176
  · exact point230slice177
  · exact point230slice178
  · exact point230slice179
  · exact point230slice180
  · exact point230slice181
  · exact point230slice182
  · exact point230slice183
  · exact point230slice184
  · exact point230slice185
  · exact point230slice186
  · exact point230slice187
  · exact point230slice188
  · exact point230slice189
  · exact point230slice190
  · exact point230slice191
  · exact point230slice192
  · exact point230slice193
  · exact point230slice194
  · exact point230slice195
  · exact point230slice196
  · exact point230slice197
  · exact point230slice198
  · exact point230slice199
  · exact point230slice200
  · exact point230slice201
  · exact point230slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
