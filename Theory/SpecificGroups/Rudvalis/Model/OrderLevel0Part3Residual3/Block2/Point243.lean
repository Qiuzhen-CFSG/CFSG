module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 243

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point243slice0 : Part6Nat.slice 0 3980 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice1 : Part6Nat.slice 0 3980 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice2 : Part6Nat.slice 0 3980 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice3 : Part6Nat.slice 0 3980 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice4 : Part6Nat.slice 0 3980 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice5 : Part6Nat.slice 0 3980 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice6 : Part6Nat.slice 0 3980 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice7 : Part6Nat.slice 0 3980 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice8 : Part6Nat.slice 0 3980 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice9 : Part6Nat.slice 0 3980 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice10 : Part6Nat.slice 0 3980 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice11 : Part6Nat.slice 0 3980 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice12 : Part6Nat.slice 0 3980 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice13 : Part6Nat.slice 0 3980 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice14 : Part6Nat.slice 0 3980 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice15 : Part6Nat.slice 0 3980 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice16 : Part6Nat.slice 0 3980 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice17 : Part6Nat.slice 0 3980 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice18 : Part6Nat.slice 0 3980 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice19 : Part6Nat.slice 0 3980 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice20 : Part6Nat.slice 0 3980 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice21 : Part6Nat.slice 0 3980 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice22 : Part6Nat.slice 0 3980 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice23 : Part6Nat.slice 0 3980 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice24 : Part6Nat.slice 0 3980 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice25 : Part6Nat.slice 0 3980 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice26 : Part6Nat.slice 0 3980 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice27 : Part6Nat.slice 0 3980 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice28 : Part6Nat.slice 0 3980 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice29 : Part6Nat.slice 0 3980 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice30 : Part6Nat.slice 0 3980 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice31 : Part6Nat.slice 0 3980 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice32 : Part6Nat.slice 0 3980 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice33 : Part6Nat.slice 0 3980 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice34 : Part6Nat.slice 0 3980 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice35 : Part6Nat.slice 0 3980 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice36 : Part6Nat.slice 0 3980 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice37 : Part6Nat.slice 0 3980 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice38 : Part6Nat.slice 0 3980 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice39 : Part6Nat.slice 0 3980 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice40 : Part6Nat.slice 0 3980 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice41 : Part6Nat.slice 0 3980 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice42 : Part6Nat.slice 0 3980 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice43 : Part6Nat.slice 0 3980 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice44 : Part6Nat.slice 0 3980 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice45 : Part6Nat.slice 0 3980 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice46 : Part6Nat.slice 0 3980 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice47 : Part6Nat.slice 0 3980 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice48 : Part6Nat.slice 0 3980 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice49 : Part6Nat.slice 0 3980 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice50 : Part6Nat.slice 0 3980 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice51 : Part6Nat.slice 0 3980 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice52 : Part6Nat.slice 0 3980 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice53 : Part6Nat.slice 0 3980 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice54 : Part6Nat.slice 0 3980 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice55 : Part6Nat.slice 0 3980 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice56 : Part6Nat.slice 0 3980 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice57 : Part6Nat.slice 0 3980 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice58 : Part6Nat.slice 0 3980 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice59 : Part6Nat.slice 0 3980 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice60 : Part6Nat.slice 0 3980 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice61 : Part6Nat.slice 0 3980 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice62 : Part6Nat.slice 0 3980 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice63 : Part6Nat.slice 0 3980 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice64 : Part6Nat.slice 0 3980 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice65 : Part6Nat.slice 0 3980 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice66 : Part6Nat.slice 0 3980 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice67 : Part6Nat.slice 0 3980 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice68 : Part6Nat.slice 0 3980 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice69 : Part6Nat.slice 0 3980 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice70 : Part6Nat.slice 0 3980 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice71 : Part6Nat.slice 0 3980 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice72 : Part6Nat.slice 0 3980 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice73 : Part6Nat.slice 0 3980 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice74 : Part6Nat.slice 0 3980 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice75 : Part6Nat.slice 0 3980 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice76 : Part6Nat.slice 0 3980 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice77 : Part6Nat.slice 0 3980 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice78 : Part6Nat.slice 0 3980 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice79 : Part6Nat.slice 0 3980 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice80 : Part6Nat.slice 0 3980 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice81 : Part6Nat.slice 0 3980 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice82 : Part6Nat.slice 0 3980 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice83 : Part6Nat.slice 0 3980 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice84 : Part6Nat.slice 0 3980 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice85 : Part6Nat.slice 0 3980 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice86 : Part6Nat.slice 0 3980 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice87 : Part6Nat.slice 0 3980 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice88 : Part6Nat.slice 0 3980 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice89 : Part6Nat.slice 0 3980 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice90 : Part6Nat.slice 0 3980 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice91 : Part6Nat.slice 0 3980 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice92 : Part6Nat.slice 0 3980 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice93 : Part6Nat.slice 0 3980 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice94 : Part6Nat.slice 0 3980 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice95 : Part6Nat.slice 0 3980 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice96 : Part6Nat.slice 0 3980 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice97 : Part6Nat.slice 0 3980 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice98 : Part6Nat.slice 0 3980 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice99 : Part6Nat.slice 0 3980 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice100 : Part6Nat.slice 0 3980 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice101 : Part6Nat.slice 0 3980 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice102 : Part6Nat.slice 0 3980 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice103 : Part6Nat.slice 0 3980 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice104 : Part6Nat.slice 0 3980 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice105 : Part6Nat.slice 0 3980 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice106 : Part6Nat.slice 0 3980 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice107 : Part6Nat.slice 0 3980 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice108 : Part6Nat.slice 0 3980 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice109 : Part6Nat.slice 0 3980 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice110 : Part6Nat.slice 0 3980 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice111 : Part6Nat.slice 0 3980 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice112 : Part6Nat.slice 0 3980 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice113 : Part6Nat.slice 0 3980 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice114 : Part6Nat.slice 0 3980 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice115 : Part6Nat.slice 0 3980 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice116 : Part6Nat.slice 0 3980 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice117 : Part6Nat.slice 0 3980 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice118 : Part6Nat.slice 0 3980 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice119 : Part6Nat.slice 0 3980 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice120 : Part6Nat.slice 0 3980 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice121 : Part6Nat.slice 0 3980 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice122 : Part6Nat.slice 0 3980 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice123 : Part6Nat.slice 0 3980 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice124 : Part6Nat.slice 0 3980 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice125 : Part6Nat.slice 0 3980 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice126 : Part6Nat.slice 0 3980 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice127 : Part6Nat.slice 0 3980 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice128 : Part6Nat.slice 0 3980 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice129 : Part6Nat.slice 0 3980 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice130 : Part6Nat.slice 0 3980 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice131 : Part6Nat.slice 0 3980 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice132 : Part6Nat.slice 0 3980 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice133 : Part6Nat.slice 0 3980 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice134 : Part6Nat.slice 0 3980 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice135 : Part6Nat.slice 0 3980 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice136 : Part6Nat.slice 0 3980 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice137 : Part6Nat.slice 0 3980 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice138 : Part6Nat.slice 0 3980 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice139 : Part6Nat.slice 0 3980 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice140 : Part6Nat.slice 0 3980 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice141 : Part6Nat.slice 0 3980 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice142 : Part6Nat.slice 0 3980 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice143 : Part6Nat.slice 0 3980 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice144 : Part6Nat.slice 0 3980 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice145 : Part6Nat.slice 0 3980 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice146 : Part6Nat.slice 0 3980 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice147 : Part6Nat.slice 0 3980 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice148 : Part6Nat.slice 0 3980 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice149 : Part6Nat.slice 0 3980 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice150 : Part6Nat.slice 0 3980 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice151 : Part6Nat.slice 0 3980 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice152 : Part6Nat.slice 0 3980 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice153 : Part6Nat.slice 0 3980 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice154 : Part6Nat.slice 0 3980 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice155 : Part6Nat.slice 0 3980 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice156 : Part6Nat.slice 0 3980 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice157 : Part6Nat.slice 0 3980 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice158 : Part6Nat.slice 0 3980 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice159 : Part6Nat.slice 0 3980 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice160 : Part6Nat.slice 0 3980 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice161 : Part6Nat.slice 0 3980 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice162 : Part6Nat.slice 0 3980 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice163 : Part6Nat.slice 0 3980 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice164 : Part6Nat.slice 0 3980 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice165 : Part6Nat.slice 0 3980 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice166 : Part6Nat.slice 0 3980 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice167 : Part6Nat.slice 0 3980 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice168 : Part6Nat.slice 0 3980 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice169 : Part6Nat.slice 0 3980 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice170 : Part6Nat.slice 0 3980 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice171 : Part6Nat.slice 0 3980 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice172 : Part6Nat.slice 0 3980 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice173 : Part6Nat.slice 0 3980 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice174 : Part6Nat.slice 0 3980 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice175 : Part6Nat.slice 0 3980 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice176 : Part6Nat.slice 0 3980 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice177 : Part6Nat.slice 0 3980 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice178 : Part6Nat.slice 0 3980 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice179 : Part6Nat.slice 0 3980 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice180 : Part6Nat.slice 0 3980 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice181 : Part6Nat.slice 0 3980 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice182 : Part6Nat.slice 0 3980 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice183 : Part6Nat.slice 0 3980 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice184 : Part6Nat.slice 0 3980 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice185 : Part6Nat.slice 0 3980 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice186 : Part6Nat.slice 0 3980 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice187 : Part6Nat.slice 0 3980 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice188 : Part6Nat.slice 0 3980 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice189 : Part6Nat.slice 0 3980 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice190 : Part6Nat.slice 0 3980 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice191 : Part6Nat.slice 0 3980 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice192 : Part6Nat.slice 0 3980 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice193 : Part6Nat.slice 0 3980 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice194 : Part6Nat.slice 0 3980 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice195 : Part6Nat.slice 0 3980 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice196 : Part6Nat.slice 0 3980 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice197 : Part6Nat.slice 0 3980 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice198 : Part6Nat.slice 0 3980 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice199 : Part6Nat.slice 0 3980 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice200 : Part6Nat.slice 0 3980 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice201 : Part6Nat.slice 0 3980 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point243slice202 : Part6Nat.slice 0 3980 202 = true := by
  decide +kernel

public theorem point243 : stepCheck 0 3980 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point243slice0
  · exact point243slice1
  · exact point243slice2
  · exact point243slice3
  · exact point243slice4
  · exact point243slice5
  · exact point243slice6
  · exact point243slice7
  · exact point243slice8
  · exact point243slice9
  · exact point243slice10
  · exact point243slice11
  · exact point243slice12
  · exact point243slice13
  · exact point243slice14
  · exact point243slice15
  · exact point243slice16
  · exact point243slice17
  · exact point243slice18
  · exact point243slice19
  · exact point243slice20
  · exact point243slice21
  · exact point243slice22
  · exact point243slice23
  · exact point243slice24
  · exact point243slice25
  · exact point243slice26
  · exact point243slice27
  · exact point243slice28
  · exact point243slice29
  · exact point243slice30
  · exact point243slice31
  · exact point243slice32
  · exact point243slice33
  · exact point243slice34
  · exact point243slice35
  · exact point243slice36
  · exact point243slice37
  · exact point243slice38
  · exact point243slice39
  · exact point243slice40
  · exact point243slice41
  · exact point243slice42
  · exact point243slice43
  · exact point243slice44
  · exact point243slice45
  · exact point243slice46
  · exact point243slice47
  · exact point243slice48
  · exact point243slice49
  · exact point243slice50
  · exact point243slice51
  · exact point243slice52
  · exact point243slice53
  · exact point243slice54
  · exact point243slice55
  · exact point243slice56
  · exact point243slice57
  · exact point243slice58
  · exact point243slice59
  · exact point243slice60
  · exact point243slice61
  · exact point243slice62
  · exact point243slice63
  · exact point243slice64
  · exact point243slice65
  · exact point243slice66
  · exact point243slice67
  · exact point243slice68
  · exact point243slice69
  · exact point243slice70
  · exact point243slice71
  · exact point243slice72
  · exact point243slice73
  · exact point243slice74
  · exact point243slice75
  · exact point243slice76
  · exact point243slice77
  · exact point243slice78
  · exact point243slice79
  · exact point243slice80
  · exact point243slice81
  · exact point243slice82
  · exact point243slice83
  · exact point243slice84
  · exact point243slice85
  · exact point243slice86
  · exact point243slice87
  · exact point243slice88
  · exact point243slice89
  · exact point243slice90
  · exact point243slice91
  · exact point243slice92
  · exact point243slice93
  · exact point243slice94
  · exact point243slice95
  · exact point243slice96
  · exact point243slice97
  · exact point243slice98
  · exact point243slice99
  · exact point243slice100
  · exact point243slice101
  · exact point243slice102
  · exact point243slice103
  · exact point243slice104
  · exact point243slice105
  · exact point243slice106
  · exact point243slice107
  · exact point243slice108
  · exact point243slice109
  · exact point243slice110
  · exact point243slice111
  · exact point243slice112
  · exact point243slice113
  · exact point243slice114
  · exact point243slice115
  · exact point243slice116
  · exact point243slice117
  · exact point243slice118
  · exact point243slice119
  · exact point243slice120
  · exact point243slice121
  · exact point243slice122
  · exact point243slice123
  · exact point243slice124
  · exact point243slice125
  · exact point243slice126
  · exact point243slice127
  · exact point243slice128
  · exact point243slice129
  · exact point243slice130
  · exact point243slice131
  · exact point243slice132
  · exact point243slice133
  · exact point243slice134
  · exact point243slice135
  · exact point243slice136
  · exact point243slice137
  · exact point243slice138
  · exact point243slice139
  · exact point243slice140
  · exact point243slice141
  · exact point243slice142
  · exact point243slice143
  · exact point243slice144
  · exact point243slice145
  · exact point243slice146
  · exact point243slice147
  · exact point243slice148
  · exact point243slice149
  · exact point243slice150
  · exact point243slice151
  · exact point243slice152
  · exact point243slice153
  · exact point243slice154
  · exact point243slice155
  · exact point243slice156
  · exact point243slice157
  · exact point243slice158
  · exact point243slice159
  · exact point243slice160
  · exact point243slice161
  · exact point243slice162
  · exact point243slice163
  · exact point243slice164
  · exact point243slice165
  · exact point243slice166
  · exact point243slice167
  · exact point243slice168
  · exact point243slice169
  · exact point243slice170
  · exact point243slice171
  · exact point243slice172
  · exact point243slice173
  · exact point243slice174
  · exact point243slice175
  · exact point243slice176
  · exact point243slice177
  · exact point243slice178
  · exact point243slice179
  · exact point243slice180
  · exact point243slice181
  · exact point243slice182
  · exact point243slice183
  · exact point243slice184
  · exact point243slice185
  · exact point243slice186
  · exact point243slice187
  · exact point243slice188
  · exact point243slice189
  · exact point243slice190
  · exact point243slice191
  · exact point243slice192
  · exact point243slice193
  · exact point243slice194
  · exact point243slice195
  · exact point243slice196
  · exact point243slice197
  · exact point243slice198
  · exact point243slice199
  · exact point243slice200
  · exact point243slice201
  · exact point243slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
