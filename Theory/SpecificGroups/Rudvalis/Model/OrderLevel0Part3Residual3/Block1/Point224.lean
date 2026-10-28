module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 224

Check the prescribed transition on 203 slices of 20 points and assemble the
permutation identity using `Part6Nat.ofSlices`. Source: `OrderLevel0Data`
and `Part3Residual.target`; adapted from `GenerateLevel0Part3Residuals.py`.
Each slice is checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point224slice0 : Part6Nat.slice 0 3840 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice1 : Part6Nat.slice 0 3840 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice2 : Part6Nat.slice 0 3840 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice3 : Part6Nat.slice 0 3840 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice4 : Part6Nat.slice 0 3840 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice5 : Part6Nat.slice 0 3840 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice6 : Part6Nat.slice 0 3840 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice7 : Part6Nat.slice 0 3840 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice8 : Part6Nat.slice 0 3840 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice9 : Part6Nat.slice 0 3840 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice10 : Part6Nat.slice 0 3840 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice11 : Part6Nat.slice 0 3840 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice12 : Part6Nat.slice 0 3840 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice13 : Part6Nat.slice 0 3840 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice14 : Part6Nat.slice 0 3840 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice15 : Part6Nat.slice 0 3840 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice16 : Part6Nat.slice 0 3840 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice17 : Part6Nat.slice 0 3840 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice18 : Part6Nat.slice 0 3840 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice19 : Part6Nat.slice 0 3840 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice20 : Part6Nat.slice 0 3840 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice21 : Part6Nat.slice 0 3840 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice22 : Part6Nat.slice 0 3840 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice23 : Part6Nat.slice 0 3840 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice24 : Part6Nat.slice 0 3840 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice25 : Part6Nat.slice 0 3840 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice26 : Part6Nat.slice 0 3840 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice27 : Part6Nat.slice 0 3840 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice28 : Part6Nat.slice 0 3840 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice29 : Part6Nat.slice 0 3840 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice30 : Part6Nat.slice 0 3840 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice31 : Part6Nat.slice 0 3840 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice32 : Part6Nat.slice 0 3840 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice33 : Part6Nat.slice 0 3840 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice34 : Part6Nat.slice 0 3840 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice35 : Part6Nat.slice 0 3840 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice36 : Part6Nat.slice 0 3840 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice37 : Part6Nat.slice 0 3840 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice38 : Part6Nat.slice 0 3840 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice39 : Part6Nat.slice 0 3840 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice40 : Part6Nat.slice 0 3840 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice41 : Part6Nat.slice 0 3840 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice42 : Part6Nat.slice 0 3840 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice43 : Part6Nat.slice 0 3840 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice44 : Part6Nat.slice 0 3840 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice45 : Part6Nat.slice 0 3840 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice46 : Part6Nat.slice 0 3840 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice47 : Part6Nat.slice 0 3840 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice48 : Part6Nat.slice 0 3840 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice49 : Part6Nat.slice 0 3840 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice50 : Part6Nat.slice 0 3840 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice51 : Part6Nat.slice 0 3840 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice52 : Part6Nat.slice 0 3840 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice53 : Part6Nat.slice 0 3840 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice54 : Part6Nat.slice 0 3840 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice55 : Part6Nat.slice 0 3840 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice56 : Part6Nat.slice 0 3840 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice57 : Part6Nat.slice 0 3840 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice58 : Part6Nat.slice 0 3840 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice59 : Part6Nat.slice 0 3840 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice60 : Part6Nat.slice 0 3840 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice61 : Part6Nat.slice 0 3840 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice62 : Part6Nat.slice 0 3840 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice63 : Part6Nat.slice 0 3840 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice64 : Part6Nat.slice 0 3840 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice65 : Part6Nat.slice 0 3840 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice66 : Part6Nat.slice 0 3840 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice67 : Part6Nat.slice 0 3840 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice68 : Part6Nat.slice 0 3840 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice69 : Part6Nat.slice 0 3840 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice70 : Part6Nat.slice 0 3840 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice71 : Part6Nat.slice 0 3840 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice72 : Part6Nat.slice 0 3840 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice73 : Part6Nat.slice 0 3840 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice74 : Part6Nat.slice 0 3840 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice75 : Part6Nat.slice 0 3840 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice76 : Part6Nat.slice 0 3840 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice77 : Part6Nat.slice 0 3840 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice78 : Part6Nat.slice 0 3840 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice79 : Part6Nat.slice 0 3840 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice80 : Part6Nat.slice 0 3840 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice81 : Part6Nat.slice 0 3840 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice82 : Part6Nat.slice 0 3840 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice83 : Part6Nat.slice 0 3840 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice84 : Part6Nat.slice 0 3840 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice85 : Part6Nat.slice 0 3840 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice86 : Part6Nat.slice 0 3840 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice87 : Part6Nat.slice 0 3840 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice88 : Part6Nat.slice 0 3840 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice89 : Part6Nat.slice 0 3840 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice90 : Part6Nat.slice 0 3840 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice91 : Part6Nat.slice 0 3840 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice92 : Part6Nat.slice 0 3840 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice93 : Part6Nat.slice 0 3840 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice94 : Part6Nat.slice 0 3840 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice95 : Part6Nat.slice 0 3840 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice96 : Part6Nat.slice 0 3840 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice97 : Part6Nat.slice 0 3840 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice98 : Part6Nat.slice 0 3840 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice99 : Part6Nat.slice 0 3840 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice100 : Part6Nat.slice 0 3840 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice101 : Part6Nat.slice 0 3840 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice102 : Part6Nat.slice 0 3840 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice103 : Part6Nat.slice 0 3840 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice104 : Part6Nat.slice 0 3840 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice105 : Part6Nat.slice 0 3840 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice106 : Part6Nat.slice 0 3840 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice107 : Part6Nat.slice 0 3840 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice108 : Part6Nat.slice 0 3840 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice109 : Part6Nat.slice 0 3840 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice110 : Part6Nat.slice 0 3840 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice111 : Part6Nat.slice 0 3840 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice112 : Part6Nat.slice 0 3840 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice113 : Part6Nat.slice 0 3840 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice114 : Part6Nat.slice 0 3840 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice115 : Part6Nat.slice 0 3840 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice116 : Part6Nat.slice 0 3840 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice117 : Part6Nat.slice 0 3840 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice118 : Part6Nat.slice 0 3840 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice119 : Part6Nat.slice 0 3840 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice120 : Part6Nat.slice 0 3840 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice121 : Part6Nat.slice 0 3840 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice122 : Part6Nat.slice 0 3840 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice123 : Part6Nat.slice 0 3840 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice124 : Part6Nat.slice 0 3840 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice125 : Part6Nat.slice 0 3840 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice126 : Part6Nat.slice 0 3840 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice127 : Part6Nat.slice 0 3840 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice128 : Part6Nat.slice 0 3840 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice129 : Part6Nat.slice 0 3840 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice130 : Part6Nat.slice 0 3840 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice131 : Part6Nat.slice 0 3840 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice132 : Part6Nat.slice 0 3840 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice133 : Part6Nat.slice 0 3840 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice134 : Part6Nat.slice 0 3840 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice135 : Part6Nat.slice 0 3840 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice136 : Part6Nat.slice 0 3840 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice137 : Part6Nat.slice 0 3840 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice138 : Part6Nat.slice 0 3840 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice139 : Part6Nat.slice 0 3840 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice140 : Part6Nat.slice 0 3840 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice141 : Part6Nat.slice 0 3840 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice142 : Part6Nat.slice 0 3840 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice143 : Part6Nat.slice 0 3840 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice144 : Part6Nat.slice 0 3840 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice145 : Part6Nat.slice 0 3840 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice146 : Part6Nat.slice 0 3840 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice147 : Part6Nat.slice 0 3840 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice148 : Part6Nat.slice 0 3840 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice149 : Part6Nat.slice 0 3840 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice150 : Part6Nat.slice 0 3840 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice151 : Part6Nat.slice 0 3840 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice152 : Part6Nat.slice 0 3840 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice153 : Part6Nat.slice 0 3840 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice154 : Part6Nat.slice 0 3840 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice155 : Part6Nat.slice 0 3840 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice156 : Part6Nat.slice 0 3840 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice157 : Part6Nat.slice 0 3840 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice158 : Part6Nat.slice 0 3840 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice159 : Part6Nat.slice 0 3840 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice160 : Part6Nat.slice 0 3840 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice161 : Part6Nat.slice 0 3840 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice162 : Part6Nat.slice 0 3840 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice163 : Part6Nat.slice 0 3840 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice164 : Part6Nat.slice 0 3840 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice165 : Part6Nat.slice 0 3840 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice166 : Part6Nat.slice 0 3840 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice167 : Part6Nat.slice 0 3840 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice168 : Part6Nat.slice 0 3840 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice169 : Part6Nat.slice 0 3840 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice170 : Part6Nat.slice 0 3840 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice171 : Part6Nat.slice 0 3840 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice172 : Part6Nat.slice 0 3840 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice173 : Part6Nat.slice 0 3840 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice174 : Part6Nat.slice 0 3840 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice175 : Part6Nat.slice 0 3840 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice176 : Part6Nat.slice 0 3840 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice177 : Part6Nat.slice 0 3840 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice178 : Part6Nat.slice 0 3840 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice179 : Part6Nat.slice 0 3840 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice180 : Part6Nat.slice 0 3840 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice181 : Part6Nat.slice 0 3840 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice182 : Part6Nat.slice 0 3840 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice183 : Part6Nat.slice 0 3840 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice184 : Part6Nat.slice 0 3840 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice185 : Part6Nat.slice 0 3840 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice186 : Part6Nat.slice 0 3840 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice187 : Part6Nat.slice 0 3840 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice188 : Part6Nat.slice 0 3840 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice189 : Part6Nat.slice 0 3840 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice190 : Part6Nat.slice 0 3840 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice191 : Part6Nat.slice 0 3840 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice192 : Part6Nat.slice 0 3840 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice193 : Part6Nat.slice 0 3840 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice194 : Part6Nat.slice 0 3840 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice195 : Part6Nat.slice 0 3840 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice196 : Part6Nat.slice 0 3840 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice197 : Part6Nat.slice 0 3840 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice198 : Part6Nat.slice 0 3840 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice199 : Part6Nat.slice 0 3840 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice200 : Part6Nat.slice 0 3840 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice201 : Part6Nat.slice 0 3840 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point224slice202 : Part6Nat.slice 0 3840 202 = true := by
  decide +kernel

public theorem point224 : stepCheck 0 3840 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point224slice0
  · exact point224slice1
  · exact point224slice2
  · exact point224slice3
  · exact point224slice4
  · exact point224slice5
  · exact point224slice6
  · exact point224slice7
  · exact point224slice8
  · exact point224slice9
  · exact point224slice10
  · exact point224slice11
  · exact point224slice12
  · exact point224slice13
  · exact point224slice14
  · exact point224slice15
  · exact point224slice16
  · exact point224slice17
  · exact point224slice18
  · exact point224slice19
  · exact point224slice20
  · exact point224slice21
  · exact point224slice22
  · exact point224slice23
  · exact point224slice24
  · exact point224slice25
  · exact point224slice26
  · exact point224slice27
  · exact point224slice28
  · exact point224slice29
  · exact point224slice30
  · exact point224slice31
  · exact point224slice32
  · exact point224slice33
  · exact point224slice34
  · exact point224slice35
  · exact point224slice36
  · exact point224slice37
  · exact point224slice38
  · exact point224slice39
  · exact point224slice40
  · exact point224slice41
  · exact point224slice42
  · exact point224slice43
  · exact point224slice44
  · exact point224slice45
  · exact point224slice46
  · exact point224slice47
  · exact point224slice48
  · exact point224slice49
  · exact point224slice50
  · exact point224slice51
  · exact point224slice52
  · exact point224slice53
  · exact point224slice54
  · exact point224slice55
  · exact point224slice56
  · exact point224slice57
  · exact point224slice58
  · exact point224slice59
  · exact point224slice60
  · exact point224slice61
  · exact point224slice62
  · exact point224slice63
  · exact point224slice64
  · exact point224slice65
  · exact point224slice66
  · exact point224slice67
  · exact point224slice68
  · exact point224slice69
  · exact point224slice70
  · exact point224slice71
  · exact point224slice72
  · exact point224slice73
  · exact point224slice74
  · exact point224slice75
  · exact point224slice76
  · exact point224slice77
  · exact point224slice78
  · exact point224slice79
  · exact point224slice80
  · exact point224slice81
  · exact point224slice82
  · exact point224slice83
  · exact point224slice84
  · exact point224slice85
  · exact point224slice86
  · exact point224slice87
  · exact point224slice88
  · exact point224slice89
  · exact point224slice90
  · exact point224slice91
  · exact point224slice92
  · exact point224slice93
  · exact point224slice94
  · exact point224slice95
  · exact point224slice96
  · exact point224slice97
  · exact point224slice98
  · exact point224slice99
  · exact point224slice100
  · exact point224slice101
  · exact point224slice102
  · exact point224slice103
  · exact point224slice104
  · exact point224slice105
  · exact point224slice106
  · exact point224slice107
  · exact point224slice108
  · exact point224slice109
  · exact point224slice110
  · exact point224slice111
  · exact point224slice112
  · exact point224slice113
  · exact point224slice114
  · exact point224slice115
  · exact point224slice116
  · exact point224slice117
  · exact point224slice118
  · exact point224slice119
  · exact point224slice120
  · exact point224slice121
  · exact point224slice122
  · exact point224slice123
  · exact point224slice124
  · exact point224slice125
  · exact point224slice126
  · exact point224slice127
  · exact point224slice128
  · exact point224slice129
  · exact point224slice130
  · exact point224slice131
  · exact point224slice132
  · exact point224slice133
  · exact point224slice134
  · exact point224slice135
  · exact point224slice136
  · exact point224slice137
  · exact point224slice138
  · exact point224slice139
  · exact point224slice140
  · exact point224slice141
  · exact point224slice142
  · exact point224slice143
  · exact point224slice144
  · exact point224slice145
  · exact point224slice146
  · exact point224slice147
  · exact point224slice148
  · exact point224slice149
  · exact point224slice150
  · exact point224slice151
  · exact point224slice152
  · exact point224slice153
  · exact point224slice154
  · exact point224slice155
  · exact point224slice156
  · exact point224slice157
  · exact point224slice158
  · exact point224slice159
  · exact point224slice160
  · exact point224slice161
  · exact point224slice162
  · exact point224slice163
  · exact point224slice164
  · exact point224slice165
  · exact point224slice166
  · exact point224slice167
  · exact point224slice168
  · exact point224slice169
  · exact point224slice170
  · exact point224slice171
  · exact point224slice172
  · exact point224slice173
  · exact point224slice174
  · exact point224slice175
  · exact point224slice176
  · exact point224slice177
  · exact point224slice178
  · exact point224slice179
  · exact point224slice180
  · exact point224slice181
  · exact point224slice182
  · exact point224slice183
  · exact point224slice184
  · exact point224slice185
  · exact point224slice186
  · exact point224slice187
  · exact point224slice188
  · exact point224slice189
  · exact point224slice190
  · exact point224slice191
  · exact point224slice192
  · exact point224slice193
  · exact point224slice194
  · exact point224slice195
  · exact point224slice196
  · exact point224slice197
  · exact point224slice198
  · exact point224slice199
  · exact point224slice200
  · exact point224slice201
  · exact point224slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
