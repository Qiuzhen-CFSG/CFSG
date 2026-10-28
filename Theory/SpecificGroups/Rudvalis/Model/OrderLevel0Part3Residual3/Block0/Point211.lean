module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 211

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point211slice0 : Part6Nat.slice 1 3576 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice1 : Part6Nat.slice 1 3576 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice2 : Part6Nat.slice 1 3576 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice3 : Part6Nat.slice 1 3576 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice4 : Part6Nat.slice 1 3576 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice5 : Part6Nat.slice 1 3576 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice6 : Part6Nat.slice 1 3576 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice7 : Part6Nat.slice 1 3576 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice8 : Part6Nat.slice 1 3576 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice9 : Part6Nat.slice 1 3576 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice10 : Part6Nat.slice 1 3576 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice11 : Part6Nat.slice 1 3576 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice12 : Part6Nat.slice 1 3576 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice13 : Part6Nat.slice 1 3576 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice14 : Part6Nat.slice 1 3576 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice15 : Part6Nat.slice 1 3576 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice16 : Part6Nat.slice 1 3576 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice17 : Part6Nat.slice 1 3576 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice18 : Part6Nat.slice 1 3576 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice19 : Part6Nat.slice 1 3576 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice20 : Part6Nat.slice 1 3576 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice21 : Part6Nat.slice 1 3576 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice22 : Part6Nat.slice 1 3576 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice23 : Part6Nat.slice 1 3576 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice24 : Part6Nat.slice 1 3576 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice25 : Part6Nat.slice 1 3576 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice26 : Part6Nat.slice 1 3576 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice27 : Part6Nat.slice 1 3576 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice28 : Part6Nat.slice 1 3576 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice29 : Part6Nat.slice 1 3576 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice30 : Part6Nat.slice 1 3576 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice31 : Part6Nat.slice 1 3576 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice32 : Part6Nat.slice 1 3576 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice33 : Part6Nat.slice 1 3576 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice34 : Part6Nat.slice 1 3576 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice35 : Part6Nat.slice 1 3576 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice36 : Part6Nat.slice 1 3576 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice37 : Part6Nat.slice 1 3576 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice38 : Part6Nat.slice 1 3576 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice39 : Part6Nat.slice 1 3576 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice40 : Part6Nat.slice 1 3576 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice41 : Part6Nat.slice 1 3576 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice42 : Part6Nat.slice 1 3576 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice43 : Part6Nat.slice 1 3576 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice44 : Part6Nat.slice 1 3576 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice45 : Part6Nat.slice 1 3576 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice46 : Part6Nat.slice 1 3576 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice47 : Part6Nat.slice 1 3576 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice48 : Part6Nat.slice 1 3576 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice49 : Part6Nat.slice 1 3576 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice50 : Part6Nat.slice 1 3576 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice51 : Part6Nat.slice 1 3576 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice52 : Part6Nat.slice 1 3576 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice53 : Part6Nat.slice 1 3576 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice54 : Part6Nat.slice 1 3576 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice55 : Part6Nat.slice 1 3576 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice56 : Part6Nat.slice 1 3576 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice57 : Part6Nat.slice 1 3576 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice58 : Part6Nat.slice 1 3576 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice59 : Part6Nat.slice 1 3576 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice60 : Part6Nat.slice 1 3576 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice61 : Part6Nat.slice 1 3576 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice62 : Part6Nat.slice 1 3576 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice63 : Part6Nat.slice 1 3576 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice64 : Part6Nat.slice 1 3576 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice65 : Part6Nat.slice 1 3576 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice66 : Part6Nat.slice 1 3576 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice67 : Part6Nat.slice 1 3576 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice68 : Part6Nat.slice 1 3576 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice69 : Part6Nat.slice 1 3576 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice70 : Part6Nat.slice 1 3576 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice71 : Part6Nat.slice 1 3576 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice72 : Part6Nat.slice 1 3576 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice73 : Part6Nat.slice 1 3576 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice74 : Part6Nat.slice 1 3576 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice75 : Part6Nat.slice 1 3576 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice76 : Part6Nat.slice 1 3576 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice77 : Part6Nat.slice 1 3576 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice78 : Part6Nat.slice 1 3576 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice79 : Part6Nat.slice 1 3576 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice80 : Part6Nat.slice 1 3576 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice81 : Part6Nat.slice 1 3576 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice82 : Part6Nat.slice 1 3576 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice83 : Part6Nat.slice 1 3576 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice84 : Part6Nat.slice 1 3576 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice85 : Part6Nat.slice 1 3576 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice86 : Part6Nat.slice 1 3576 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice87 : Part6Nat.slice 1 3576 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice88 : Part6Nat.slice 1 3576 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice89 : Part6Nat.slice 1 3576 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice90 : Part6Nat.slice 1 3576 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice91 : Part6Nat.slice 1 3576 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice92 : Part6Nat.slice 1 3576 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice93 : Part6Nat.slice 1 3576 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice94 : Part6Nat.slice 1 3576 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice95 : Part6Nat.slice 1 3576 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice96 : Part6Nat.slice 1 3576 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice97 : Part6Nat.slice 1 3576 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice98 : Part6Nat.slice 1 3576 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice99 : Part6Nat.slice 1 3576 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice100 : Part6Nat.slice 1 3576 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice101 : Part6Nat.slice 1 3576 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice102 : Part6Nat.slice 1 3576 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice103 : Part6Nat.slice 1 3576 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice104 : Part6Nat.slice 1 3576 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice105 : Part6Nat.slice 1 3576 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice106 : Part6Nat.slice 1 3576 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice107 : Part6Nat.slice 1 3576 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice108 : Part6Nat.slice 1 3576 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice109 : Part6Nat.slice 1 3576 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice110 : Part6Nat.slice 1 3576 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice111 : Part6Nat.slice 1 3576 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice112 : Part6Nat.slice 1 3576 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice113 : Part6Nat.slice 1 3576 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice114 : Part6Nat.slice 1 3576 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice115 : Part6Nat.slice 1 3576 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice116 : Part6Nat.slice 1 3576 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice117 : Part6Nat.slice 1 3576 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice118 : Part6Nat.slice 1 3576 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice119 : Part6Nat.slice 1 3576 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice120 : Part6Nat.slice 1 3576 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice121 : Part6Nat.slice 1 3576 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice122 : Part6Nat.slice 1 3576 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice123 : Part6Nat.slice 1 3576 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice124 : Part6Nat.slice 1 3576 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice125 : Part6Nat.slice 1 3576 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice126 : Part6Nat.slice 1 3576 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice127 : Part6Nat.slice 1 3576 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice128 : Part6Nat.slice 1 3576 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice129 : Part6Nat.slice 1 3576 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice130 : Part6Nat.slice 1 3576 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice131 : Part6Nat.slice 1 3576 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice132 : Part6Nat.slice 1 3576 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice133 : Part6Nat.slice 1 3576 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice134 : Part6Nat.slice 1 3576 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice135 : Part6Nat.slice 1 3576 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice136 : Part6Nat.slice 1 3576 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice137 : Part6Nat.slice 1 3576 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice138 : Part6Nat.slice 1 3576 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice139 : Part6Nat.slice 1 3576 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice140 : Part6Nat.slice 1 3576 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice141 : Part6Nat.slice 1 3576 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice142 : Part6Nat.slice 1 3576 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice143 : Part6Nat.slice 1 3576 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice144 : Part6Nat.slice 1 3576 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice145 : Part6Nat.slice 1 3576 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice146 : Part6Nat.slice 1 3576 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice147 : Part6Nat.slice 1 3576 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice148 : Part6Nat.slice 1 3576 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice149 : Part6Nat.slice 1 3576 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice150 : Part6Nat.slice 1 3576 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice151 : Part6Nat.slice 1 3576 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice152 : Part6Nat.slice 1 3576 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice153 : Part6Nat.slice 1 3576 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice154 : Part6Nat.slice 1 3576 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice155 : Part6Nat.slice 1 3576 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice156 : Part6Nat.slice 1 3576 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice157 : Part6Nat.slice 1 3576 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice158 : Part6Nat.slice 1 3576 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice159 : Part6Nat.slice 1 3576 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice160 : Part6Nat.slice 1 3576 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice161 : Part6Nat.slice 1 3576 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice162 : Part6Nat.slice 1 3576 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice163 : Part6Nat.slice 1 3576 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice164 : Part6Nat.slice 1 3576 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice165 : Part6Nat.slice 1 3576 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice166 : Part6Nat.slice 1 3576 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice167 : Part6Nat.slice 1 3576 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice168 : Part6Nat.slice 1 3576 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice169 : Part6Nat.slice 1 3576 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice170 : Part6Nat.slice 1 3576 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice171 : Part6Nat.slice 1 3576 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice172 : Part6Nat.slice 1 3576 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice173 : Part6Nat.slice 1 3576 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice174 : Part6Nat.slice 1 3576 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice175 : Part6Nat.slice 1 3576 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice176 : Part6Nat.slice 1 3576 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice177 : Part6Nat.slice 1 3576 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice178 : Part6Nat.slice 1 3576 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice179 : Part6Nat.slice 1 3576 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice180 : Part6Nat.slice 1 3576 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice181 : Part6Nat.slice 1 3576 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice182 : Part6Nat.slice 1 3576 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice183 : Part6Nat.slice 1 3576 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice184 : Part6Nat.slice 1 3576 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice185 : Part6Nat.slice 1 3576 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice186 : Part6Nat.slice 1 3576 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice187 : Part6Nat.slice 1 3576 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice188 : Part6Nat.slice 1 3576 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice189 : Part6Nat.slice 1 3576 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice190 : Part6Nat.slice 1 3576 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice191 : Part6Nat.slice 1 3576 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice192 : Part6Nat.slice 1 3576 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice193 : Part6Nat.slice 1 3576 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice194 : Part6Nat.slice 1 3576 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice195 : Part6Nat.slice 1 3576 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice196 : Part6Nat.slice 1 3576 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice197 : Part6Nat.slice 1 3576 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice198 : Part6Nat.slice 1 3576 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice199 : Part6Nat.slice 1 3576 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice200 : Part6Nat.slice 1 3576 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice201 : Part6Nat.slice 1 3576 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point211slice202 : Part6Nat.slice 1 3576 202 = true := by
  decide +kernel

public theorem point211 : stepCheck 1 3576 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point211slice0
  · exact point211slice1
  · exact point211slice2
  · exact point211slice3
  · exact point211slice4
  · exact point211slice5
  · exact point211slice6
  · exact point211slice7
  · exact point211slice8
  · exact point211slice9
  · exact point211slice10
  · exact point211slice11
  · exact point211slice12
  · exact point211slice13
  · exact point211slice14
  · exact point211slice15
  · exact point211slice16
  · exact point211slice17
  · exact point211slice18
  · exact point211slice19
  · exact point211slice20
  · exact point211slice21
  · exact point211slice22
  · exact point211slice23
  · exact point211slice24
  · exact point211slice25
  · exact point211slice26
  · exact point211slice27
  · exact point211slice28
  · exact point211slice29
  · exact point211slice30
  · exact point211slice31
  · exact point211slice32
  · exact point211slice33
  · exact point211slice34
  · exact point211slice35
  · exact point211slice36
  · exact point211slice37
  · exact point211slice38
  · exact point211slice39
  · exact point211slice40
  · exact point211slice41
  · exact point211slice42
  · exact point211slice43
  · exact point211slice44
  · exact point211slice45
  · exact point211slice46
  · exact point211slice47
  · exact point211slice48
  · exact point211slice49
  · exact point211slice50
  · exact point211slice51
  · exact point211slice52
  · exact point211slice53
  · exact point211slice54
  · exact point211slice55
  · exact point211slice56
  · exact point211slice57
  · exact point211slice58
  · exact point211slice59
  · exact point211slice60
  · exact point211slice61
  · exact point211slice62
  · exact point211slice63
  · exact point211slice64
  · exact point211slice65
  · exact point211slice66
  · exact point211slice67
  · exact point211slice68
  · exact point211slice69
  · exact point211slice70
  · exact point211slice71
  · exact point211slice72
  · exact point211slice73
  · exact point211slice74
  · exact point211slice75
  · exact point211slice76
  · exact point211slice77
  · exact point211slice78
  · exact point211slice79
  · exact point211slice80
  · exact point211slice81
  · exact point211slice82
  · exact point211slice83
  · exact point211slice84
  · exact point211slice85
  · exact point211slice86
  · exact point211slice87
  · exact point211slice88
  · exact point211slice89
  · exact point211slice90
  · exact point211slice91
  · exact point211slice92
  · exact point211slice93
  · exact point211slice94
  · exact point211slice95
  · exact point211slice96
  · exact point211slice97
  · exact point211slice98
  · exact point211slice99
  · exact point211slice100
  · exact point211slice101
  · exact point211slice102
  · exact point211slice103
  · exact point211slice104
  · exact point211slice105
  · exact point211slice106
  · exact point211slice107
  · exact point211slice108
  · exact point211slice109
  · exact point211slice110
  · exact point211slice111
  · exact point211slice112
  · exact point211slice113
  · exact point211slice114
  · exact point211slice115
  · exact point211slice116
  · exact point211slice117
  · exact point211slice118
  · exact point211slice119
  · exact point211slice120
  · exact point211slice121
  · exact point211slice122
  · exact point211slice123
  · exact point211slice124
  · exact point211slice125
  · exact point211slice126
  · exact point211slice127
  · exact point211slice128
  · exact point211slice129
  · exact point211slice130
  · exact point211slice131
  · exact point211slice132
  · exact point211slice133
  · exact point211slice134
  · exact point211slice135
  · exact point211slice136
  · exact point211slice137
  · exact point211slice138
  · exact point211slice139
  · exact point211slice140
  · exact point211slice141
  · exact point211slice142
  · exact point211slice143
  · exact point211slice144
  · exact point211slice145
  · exact point211slice146
  · exact point211slice147
  · exact point211slice148
  · exact point211slice149
  · exact point211slice150
  · exact point211slice151
  · exact point211slice152
  · exact point211slice153
  · exact point211slice154
  · exact point211slice155
  · exact point211slice156
  · exact point211slice157
  · exact point211slice158
  · exact point211slice159
  · exact point211slice160
  · exact point211slice161
  · exact point211slice162
  · exact point211slice163
  · exact point211slice164
  · exact point211slice165
  · exact point211slice166
  · exact point211slice167
  · exact point211slice168
  · exact point211slice169
  · exact point211slice170
  · exact point211slice171
  · exact point211slice172
  · exact point211slice173
  · exact point211slice174
  · exact point211slice175
  · exact point211slice176
  · exact point211slice177
  · exact point211slice178
  · exact point211slice179
  · exact point211slice180
  · exact point211slice181
  · exact point211slice182
  · exact point211slice183
  · exact point211slice184
  · exact point211slice185
  · exact point211slice186
  · exact point211slice187
  · exact point211slice188
  · exact point211slice189
  · exact point211slice190
  · exact point211slice191
  · exact point211slice192
  · exact point211slice193
  · exact point211slice194
  · exact point211slice195
  · exact point211slice196
  · exact point211slice197
  · exact point211slice198
  · exact point211slice199
  · exact point211slice200
  · exact point211slice201
  · exact point211slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
