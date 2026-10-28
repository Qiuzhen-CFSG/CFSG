module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 225

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point225slice0 : Part6Nat.slice 0 3841 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice1 : Part6Nat.slice 0 3841 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice2 : Part6Nat.slice 0 3841 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice3 : Part6Nat.slice 0 3841 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice4 : Part6Nat.slice 0 3841 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice5 : Part6Nat.slice 0 3841 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice6 : Part6Nat.slice 0 3841 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice7 : Part6Nat.slice 0 3841 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice8 : Part6Nat.slice 0 3841 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice9 : Part6Nat.slice 0 3841 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice10 : Part6Nat.slice 0 3841 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice11 : Part6Nat.slice 0 3841 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice12 : Part6Nat.slice 0 3841 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice13 : Part6Nat.slice 0 3841 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice14 : Part6Nat.slice 0 3841 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice15 : Part6Nat.slice 0 3841 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice16 : Part6Nat.slice 0 3841 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice17 : Part6Nat.slice 0 3841 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice18 : Part6Nat.slice 0 3841 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice19 : Part6Nat.slice 0 3841 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice20 : Part6Nat.slice 0 3841 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice21 : Part6Nat.slice 0 3841 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice22 : Part6Nat.slice 0 3841 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice23 : Part6Nat.slice 0 3841 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice24 : Part6Nat.slice 0 3841 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice25 : Part6Nat.slice 0 3841 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice26 : Part6Nat.slice 0 3841 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice27 : Part6Nat.slice 0 3841 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice28 : Part6Nat.slice 0 3841 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice29 : Part6Nat.slice 0 3841 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice30 : Part6Nat.slice 0 3841 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice31 : Part6Nat.slice 0 3841 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice32 : Part6Nat.slice 0 3841 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice33 : Part6Nat.slice 0 3841 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice34 : Part6Nat.slice 0 3841 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice35 : Part6Nat.slice 0 3841 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice36 : Part6Nat.slice 0 3841 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice37 : Part6Nat.slice 0 3841 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice38 : Part6Nat.slice 0 3841 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice39 : Part6Nat.slice 0 3841 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice40 : Part6Nat.slice 0 3841 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice41 : Part6Nat.slice 0 3841 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice42 : Part6Nat.slice 0 3841 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice43 : Part6Nat.slice 0 3841 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice44 : Part6Nat.slice 0 3841 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice45 : Part6Nat.slice 0 3841 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice46 : Part6Nat.slice 0 3841 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice47 : Part6Nat.slice 0 3841 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice48 : Part6Nat.slice 0 3841 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice49 : Part6Nat.slice 0 3841 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice50 : Part6Nat.slice 0 3841 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice51 : Part6Nat.slice 0 3841 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice52 : Part6Nat.slice 0 3841 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice53 : Part6Nat.slice 0 3841 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice54 : Part6Nat.slice 0 3841 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice55 : Part6Nat.slice 0 3841 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice56 : Part6Nat.slice 0 3841 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice57 : Part6Nat.slice 0 3841 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice58 : Part6Nat.slice 0 3841 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice59 : Part6Nat.slice 0 3841 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice60 : Part6Nat.slice 0 3841 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice61 : Part6Nat.slice 0 3841 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice62 : Part6Nat.slice 0 3841 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice63 : Part6Nat.slice 0 3841 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice64 : Part6Nat.slice 0 3841 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice65 : Part6Nat.slice 0 3841 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice66 : Part6Nat.slice 0 3841 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice67 : Part6Nat.slice 0 3841 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice68 : Part6Nat.slice 0 3841 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice69 : Part6Nat.slice 0 3841 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice70 : Part6Nat.slice 0 3841 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice71 : Part6Nat.slice 0 3841 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice72 : Part6Nat.slice 0 3841 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice73 : Part6Nat.slice 0 3841 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice74 : Part6Nat.slice 0 3841 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice75 : Part6Nat.slice 0 3841 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice76 : Part6Nat.slice 0 3841 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice77 : Part6Nat.slice 0 3841 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice78 : Part6Nat.slice 0 3841 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice79 : Part6Nat.slice 0 3841 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice80 : Part6Nat.slice 0 3841 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice81 : Part6Nat.slice 0 3841 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice82 : Part6Nat.slice 0 3841 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice83 : Part6Nat.slice 0 3841 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice84 : Part6Nat.slice 0 3841 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice85 : Part6Nat.slice 0 3841 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice86 : Part6Nat.slice 0 3841 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice87 : Part6Nat.slice 0 3841 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice88 : Part6Nat.slice 0 3841 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice89 : Part6Nat.slice 0 3841 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice90 : Part6Nat.slice 0 3841 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice91 : Part6Nat.slice 0 3841 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice92 : Part6Nat.slice 0 3841 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice93 : Part6Nat.slice 0 3841 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice94 : Part6Nat.slice 0 3841 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice95 : Part6Nat.slice 0 3841 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice96 : Part6Nat.slice 0 3841 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice97 : Part6Nat.slice 0 3841 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice98 : Part6Nat.slice 0 3841 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice99 : Part6Nat.slice 0 3841 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice100 : Part6Nat.slice 0 3841 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice101 : Part6Nat.slice 0 3841 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice102 : Part6Nat.slice 0 3841 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice103 : Part6Nat.slice 0 3841 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice104 : Part6Nat.slice 0 3841 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice105 : Part6Nat.slice 0 3841 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice106 : Part6Nat.slice 0 3841 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice107 : Part6Nat.slice 0 3841 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice108 : Part6Nat.slice 0 3841 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice109 : Part6Nat.slice 0 3841 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice110 : Part6Nat.slice 0 3841 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice111 : Part6Nat.slice 0 3841 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice112 : Part6Nat.slice 0 3841 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice113 : Part6Nat.slice 0 3841 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice114 : Part6Nat.slice 0 3841 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice115 : Part6Nat.slice 0 3841 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice116 : Part6Nat.slice 0 3841 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice117 : Part6Nat.slice 0 3841 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice118 : Part6Nat.slice 0 3841 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice119 : Part6Nat.slice 0 3841 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice120 : Part6Nat.slice 0 3841 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice121 : Part6Nat.slice 0 3841 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice122 : Part6Nat.slice 0 3841 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice123 : Part6Nat.slice 0 3841 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice124 : Part6Nat.slice 0 3841 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice125 : Part6Nat.slice 0 3841 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice126 : Part6Nat.slice 0 3841 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice127 : Part6Nat.slice 0 3841 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice128 : Part6Nat.slice 0 3841 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice129 : Part6Nat.slice 0 3841 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice130 : Part6Nat.slice 0 3841 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice131 : Part6Nat.slice 0 3841 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice132 : Part6Nat.slice 0 3841 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice133 : Part6Nat.slice 0 3841 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice134 : Part6Nat.slice 0 3841 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice135 : Part6Nat.slice 0 3841 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice136 : Part6Nat.slice 0 3841 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice137 : Part6Nat.slice 0 3841 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice138 : Part6Nat.slice 0 3841 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice139 : Part6Nat.slice 0 3841 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice140 : Part6Nat.slice 0 3841 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice141 : Part6Nat.slice 0 3841 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice142 : Part6Nat.slice 0 3841 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice143 : Part6Nat.slice 0 3841 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice144 : Part6Nat.slice 0 3841 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice145 : Part6Nat.slice 0 3841 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice146 : Part6Nat.slice 0 3841 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice147 : Part6Nat.slice 0 3841 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice148 : Part6Nat.slice 0 3841 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice149 : Part6Nat.slice 0 3841 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice150 : Part6Nat.slice 0 3841 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice151 : Part6Nat.slice 0 3841 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice152 : Part6Nat.slice 0 3841 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice153 : Part6Nat.slice 0 3841 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice154 : Part6Nat.slice 0 3841 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice155 : Part6Nat.slice 0 3841 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice156 : Part6Nat.slice 0 3841 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice157 : Part6Nat.slice 0 3841 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice158 : Part6Nat.slice 0 3841 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice159 : Part6Nat.slice 0 3841 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice160 : Part6Nat.slice 0 3841 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice161 : Part6Nat.slice 0 3841 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice162 : Part6Nat.slice 0 3841 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice163 : Part6Nat.slice 0 3841 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice164 : Part6Nat.slice 0 3841 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice165 : Part6Nat.slice 0 3841 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice166 : Part6Nat.slice 0 3841 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice167 : Part6Nat.slice 0 3841 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice168 : Part6Nat.slice 0 3841 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice169 : Part6Nat.slice 0 3841 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice170 : Part6Nat.slice 0 3841 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice171 : Part6Nat.slice 0 3841 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice172 : Part6Nat.slice 0 3841 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice173 : Part6Nat.slice 0 3841 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice174 : Part6Nat.slice 0 3841 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice175 : Part6Nat.slice 0 3841 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice176 : Part6Nat.slice 0 3841 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice177 : Part6Nat.slice 0 3841 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice178 : Part6Nat.slice 0 3841 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice179 : Part6Nat.slice 0 3841 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice180 : Part6Nat.slice 0 3841 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice181 : Part6Nat.slice 0 3841 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice182 : Part6Nat.slice 0 3841 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice183 : Part6Nat.slice 0 3841 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice184 : Part6Nat.slice 0 3841 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice185 : Part6Nat.slice 0 3841 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice186 : Part6Nat.slice 0 3841 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice187 : Part6Nat.slice 0 3841 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice188 : Part6Nat.slice 0 3841 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice189 : Part6Nat.slice 0 3841 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice190 : Part6Nat.slice 0 3841 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice191 : Part6Nat.slice 0 3841 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice192 : Part6Nat.slice 0 3841 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice193 : Part6Nat.slice 0 3841 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice194 : Part6Nat.slice 0 3841 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice195 : Part6Nat.slice 0 3841 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice196 : Part6Nat.slice 0 3841 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice197 : Part6Nat.slice 0 3841 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice198 : Part6Nat.slice 0 3841 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice199 : Part6Nat.slice 0 3841 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice200 : Part6Nat.slice 0 3841 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice201 : Part6Nat.slice 0 3841 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point225slice202 : Part6Nat.slice 0 3841 202 = true := by
  decide +kernel

public theorem point225 : stepCheck 0 3841 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point225slice0
  · exact point225slice1
  · exact point225slice2
  · exact point225slice3
  · exact point225slice4
  · exact point225slice5
  · exact point225slice6
  · exact point225slice7
  · exact point225slice8
  · exact point225slice9
  · exact point225slice10
  · exact point225slice11
  · exact point225slice12
  · exact point225slice13
  · exact point225slice14
  · exact point225slice15
  · exact point225slice16
  · exact point225slice17
  · exact point225slice18
  · exact point225slice19
  · exact point225slice20
  · exact point225slice21
  · exact point225slice22
  · exact point225slice23
  · exact point225slice24
  · exact point225slice25
  · exact point225slice26
  · exact point225slice27
  · exact point225slice28
  · exact point225slice29
  · exact point225slice30
  · exact point225slice31
  · exact point225slice32
  · exact point225slice33
  · exact point225slice34
  · exact point225slice35
  · exact point225slice36
  · exact point225slice37
  · exact point225slice38
  · exact point225slice39
  · exact point225slice40
  · exact point225slice41
  · exact point225slice42
  · exact point225slice43
  · exact point225slice44
  · exact point225slice45
  · exact point225slice46
  · exact point225slice47
  · exact point225slice48
  · exact point225slice49
  · exact point225slice50
  · exact point225slice51
  · exact point225slice52
  · exact point225slice53
  · exact point225slice54
  · exact point225slice55
  · exact point225slice56
  · exact point225slice57
  · exact point225slice58
  · exact point225slice59
  · exact point225slice60
  · exact point225slice61
  · exact point225slice62
  · exact point225slice63
  · exact point225slice64
  · exact point225slice65
  · exact point225slice66
  · exact point225slice67
  · exact point225slice68
  · exact point225slice69
  · exact point225slice70
  · exact point225slice71
  · exact point225slice72
  · exact point225slice73
  · exact point225slice74
  · exact point225slice75
  · exact point225slice76
  · exact point225slice77
  · exact point225slice78
  · exact point225slice79
  · exact point225slice80
  · exact point225slice81
  · exact point225slice82
  · exact point225slice83
  · exact point225slice84
  · exact point225slice85
  · exact point225slice86
  · exact point225slice87
  · exact point225slice88
  · exact point225slice89
  · exact point225slice90
  · exact point225slice91
  · exact point225slice92
  · exact point225slice93
  · exact point225slice94
  · exact point225slice95
  · exact point225slice96
  · exact point225slice97
  · exact point225slice98
  · exact point225slice99
  · exact point225slice100
  · exact point225slice101
  · exact point225slice102
  · exact point225slice103
  · exact point225slice104
  · exact point225slice105
  · exact point225slice106
  · exact point225slice107
  · exact point225slice108
  · exact point225slice109
  · exact point225slice110
  · exact point225slice111
  · exact point225slice112
  · exact point225slice113
  · exact point225slice114
  · exact point225slice115
  · exact point225slice116
  · exact point225slice117
  · exact point225slice118
  · exact point225slice119
  · exact point225slice120
  · exact point225slice121
  · exact point225slice122
  · exact point225slice123
  · exact point225slice124
  · exact point225slice125
  · exact point225slice126
  · exact point225slice127
  · exact point225slice128
  · exact point225slice129
  · exact point225slice130
  · exact point225slice131
  · exact point225slice132
  · exact point225slice133
  · exact point225slice134
  · exact point225slice135
  · exact point225slice136
  · exact point225slice137
  · exact point225slice138
  · exact point225slice139
  · exact point225slice140
  · exact point225slice141
  · exact point225slice142
  · exact point225slice143
  · exact point225slice144
  · exact point225slice145
  · exact point225slice146
  · exact point225slice147
  · exact point225slice148
  · exact point225slice149
  · exact point225slice150
  · exact point225slice151
  · exact point225slice152
  · exact point225slice153
  · exact point225slice154
  · exact point225slice155
  · exact point225slice156
  · exact point225slice157
  · exact point225slice158
  · exact point225slice159
  · exact point225slice160
  · exact point225slice161
  · exact point225slice162
  · exact point225slice163
  · exact point225slice164
  · exact point225slice165
  · exact point225slice166
  · exact point225slice167
  · exact point225slice168
  · exact point225slice169
  · exact point225slice170
  · exact point225slice171
  · exact point225slice172
  · exact point225slice173
  · exact point225slice174
  · exact point225slice175
  · exact point225slice176
  · exact point225slice177
  · exact point225slice178
  · exact point225slice179
  · exact point225slice180
  · exact point225slice181
  · exact point225slice182
  · exact point225slice183
  · exact point225slice184
  · exact point225slice185
  · exact point225slice186
  · exact point225slice187
  · exact point225slice188
  · exact point225slice189
  · exact point225slice190
  · exact point225slice191
  · exact point225slice192
  · exact point225slice193
  · exact point225slice194
  · exact point225slice195
  · exact point225slice196
  · exact point225slice197
  · exact point225slice198
  · exact point225slice199
  · exact point225slice200
  · exact point225slice201
  · exact point225slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
