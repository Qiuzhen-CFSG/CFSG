module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2Blocks
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 201

Certify the prescribed forward-generator identity at residual index 201.
The 203 kernel-checked slices cover all 4060 points; `Part6Nat.ofSlices`
transfers these checks to the permutation identity. Source: `OrderLevel0Data`
and `Part3Residual.target`, with witness provenance in
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point201slice0 : Part6Nat.slice 1 3438 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice1 : Part6Nat.slice 1 3438 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice2 : Part6Nat.slice 1 3438 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice3 : Part6Nat.slice 1 3438 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice4 : Part6Nat.slice 1 3438 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice5 : Part6Nat.slice 1 3438 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice6 : Part6Nat.slice 1 3438 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice7 : Part6Nat.slice 1 3438 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice8 : Part6Nat.slice 1 3438 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice9 : Part6Nat.slice 1 3438 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice10 : Part6Nat.slice 1 3438 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice11 : Part6Nat.slice 1 3438 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice12 : Part6Nat.slice 1 3438 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice13 : Part6Nat.slice 1 3438 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice14 : Part6Nat.slice 1 3438 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice15 : Part6Nat.slice 1 3438 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice16 : Part6Nat.slice 1 3438 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice17 : Part6Nat.slice 1 3438 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice18 : Part6Nat.slice 1 3438 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice19 : Part6Nat.slice 1 3438 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice20 : Part6Nat.slice 1 3438 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice21 : Part6Nat.slice 1 3438 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice22 : Part6Nat.slice 1 3438 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice23 : Part6Nat.slice 1 3438 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice24 : Part6Nat.slice 1 3438 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice25 : Part6Nat.slice 1 3438 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice26 : Part6Nat.slice 1 3438 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice27 : Part6Nat.slice 1 3438 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice28 : Part6Nat.slice 1 3438 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice29 : Part6Nat.slice 1 3438 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice30 : Part6Nat.slice 1 3438 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice31 : Part6Nat.slice 1 3438 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice32 : Part6Nat.slice 1 3438 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice33 : Part6Nat.slice 1 3438 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice34 : Part6Nat.slice 1 3438 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice35 : Part6Nat.slice 1 3438 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice36 : Part6Nat.slice 1 3438 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice37 : Part6Nat.slice 1 3438 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice38 : Part6Nat.slice 1 3438 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice39 : Part6Nat.slice 1 3438 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice40 : Part6Nat.slice 1 3438 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice41 : Part6Nat.slice 1 3438 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice42 : Part6Nat.slice 1 3438 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice43 : Part6Nat.slice 1 3438 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice44 : Part6Nat.slice 1 3438 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice45 : Part6Nat.slice 1 3438 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice46 : Part6Nat.slice 1 3438 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice47 : Part6Nat.slice 1 3438 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice48 : Part6Nat.slice 1 3438 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice49 : Part6Nat.slice 1 3438 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice50 : Part6Nat.slice 1 3438 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice51 : Part6Nat.slice 1 3438 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice52 : Part6Nat.slice 1 3438 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice53 : Part6Nat.slice 1 3438 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice54 : Part6Nat.slice 1 3438 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice55 : Part6Nat.slice 1 3438 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice56 : Part6Nat.slice 1 3438 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice57 : Part6Nat.slice 1 3438 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice58 : Part6Nat.slice 1 3438 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice59 : Part6Nat.slice 1 3438 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice60 : Part6Nat.slice 1 3438 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice61 : Part6Nat.slice 1 3438 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice62 : Part6Nat.slice 1 3438 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice63 : Part6Nat.slice 1 3438 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice64 : Part6Nat.slice 1 3438 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice65 : Part6Nat.slice 1 3438 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice66 : Part6Nat.slice 1 3438 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice67 : Part6Nat.slice 1 3438 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice68 : Part6Nat.slice 1 3438 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice69 : Part6Nat.slice 1 3438 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice70 : Part6Nat.slice 1 3438 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice71 : Part6Nat.slice 1 3438 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice72 : Part6Nat.slice 1 3438 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice73 : Part6Nat.slice 1 3438 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice74 : Part6Nat.slice 1 3438 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice75 : Part6Nat.slice 1 3438 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice76 : Part6Nat.slice 1 3438 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice77 : Part6Nat.slice 1 3438 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice78 : Part6Nat.slice 1 3438 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice79 : Part6Nat.slice 1 3438 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice80 : Part6Nat.slice 1 3438 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice81 : Part6Nat.slice 1 3438 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice82 : Part6Nat.slice 1 3438 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice83 : Part6Nat.slice 1 3438 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice84 : Part6Nat.slice 1 3438 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice85 : Part6Nat.slice 1 3438 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice86 : Part6Nat.slice 1 3438 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice87 : Part6Nat.slice 1 3438 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice88 : Part6Nat.slice 1 3438 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice89 : Part6Nat.slice 1 3438 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice90 : Part6Nat.slice 1 3438 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice91 : Part6Nat.slice 1 3438 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice92 : Part6Nat.slice 1 3438 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice93 : Part6Nat.slice 1 3438 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice94 : Part6Nat.slice 1 3438 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice95 : Part6Nat.slice 1 3438 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice96 : Part6Nat.slice 1 3438 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice97 : Part6Nat.slice 1 3438 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice98 : Part6Nat.slice 1 3438 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice99 : Part6Nat.slice 1 3438 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice100 : Part6Nat.slice 1 3438 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice101 : Part6Nat.slice 1 3438 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice102 : Part6Nat.slice 1 3438 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice103 : Part6Nat.slice 1 3438 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice104 : Part6Nat.slice 1 3438 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice105 : Part6Nat.slice 1 3438 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice106 : Part6Nat.slice 1 3438 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice107 : Part6Nat.slice 1 3438 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice108 : Part6Nat.slice 1 3438 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice109 : Part6Nat.slice 1 3438 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice110 : Part6Nat.slice 1 3438 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice111 : Part6Nat.slice 1 3438 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice112 : Part6Nat.slice 1 3438 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice113 : Part6Nat.slice 1 3438 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice114 : Part6Nat.slice 1 3438 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice115 : Part6Nat.slice 1 3438 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice116 : Part6Nat.slice 1 3438 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice117 : Part6Nat.slice 1 3438 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice118 : Part6Nat.slice 1 3438 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice119 : Part6Nat.slice 1 3438 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice120 : Part6Nat.slice 1 3438 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice121 : Part6Nat.slice 1 3438 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice122 : Part6Nat.slice 1 3438 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice123 : Part6Nat.slice 1 3438 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice124 : Part6Nat.slice 1 3438 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice125 : Part6Nat.slice 1 3438 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice126 : Part6Nat.slice 1 3438 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice127 : Part6Nat.slice 1 3438 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice128 : Part6Nat.slice 1 3438 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice129 : Part6Nat.slice 1 3438 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice130 : Part6Nat.slice 1 3438 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice131 : Part6Nat.slice 1 3438 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice132 : Part6Nat.slice 1 3438 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice133 : Part6Nat.slice 1 3438 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice134 : Part6Nat.slice 1 3438 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice135 : Part6Nat.slice 1 3438 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice136 : Part6Nat.slice 1 3438 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice137 : Part6Nat.slice 1 3438 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice138 : Part6Nat.slice 1 3438 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice139 : Part6Nat.slice 1 3438 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice140 : Part6Nat.slice 1 3438 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice141 : Part6Nat.slice 1 3438 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice142 : Part6Nat.slice 1 3438 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice143 : Part6Nat.slice 1 3438 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice144 : Part6Nat.slice 1 3438 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice145 : Part6Nat.slice 1 3438 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice146 : Part6Nat.slice 1 3438 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice147 : Part6Nat.slice 1 3438 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice148 : Part6Nat.slice 1 3438 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice149 : Part6Nat.slice 1 3438 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice150 : Part6Nat.slice 1 3438 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice151 : Part6Nat.slice 1 3438 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice152 : Part6Nat.slice 1 3438 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice153 : Part6Nat.slice 1 3438 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice154 : Part6Nat.slice 1 3438 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice155 : Part6Nat.slice 1 3438 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice156 : Part6Nat.slice 1 3438 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice157 : Part6Nat.slice 1 3438 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice158 : Part6Nat.slice 1 3438 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice159 : Part6Nat.slice 1 3438 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice160 : Part6Nat.slice 1 3438 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice161 : Part6Nat.slice 1 3438 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice162 : Part6Nat.slice 1 3438 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice163 : Part6Nat.slice 1 3438 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice164 : Part6Nat.slice 1 3438 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice165 : Part6Nat.slice 1 3438 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice166 : Part6Nat.slice 1 3438 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice167 : Part6Nat.slice 1 3438 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice168 : Part6Nat.slice 1 3438 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice169 : Part6Nat.slice 1 3438 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice170 : Part6Nat.slice 1 3438 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice171 : Part6Nat.slice 1 3438 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice172 : Part6Nat.slice 1 3438 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice173 : Part6Nat.slice 1 3438 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice174 : Part6Nat.slice 1 3438 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice175 : Part6Nat.slice 1 3438 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice176 : Part6Nat.slice 1 3438 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice177 : Part6Nat.slice 1 3438 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice178 : Part6Nat.slice 1 3438 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice179 : Part6Nat.slice 1 3438 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice180 : Part6Nat.slice 1 3438 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice181 : Part6Nat.slice 1 3438 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice182 : Part6Nat.slice 1 3438 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice183 : Part6Nat.slice 1 3438 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice184 : Part6Nat.slice 1 3438 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice185 : Part6Nat.slice 1 3438 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice186 : Part6Nat.slice 1 3438 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice187 : Part6Nat.slice 1 3438 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice188 : Part6Nat.slice 1 3438 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice189 : Part6Nat.slice 1 3438 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice190 : Part6Nat.slice 1 3438 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice191 : Part6Nat.slice 1 3438 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice192 : Part6Nat.slice 1 3438 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice193 : Part6Nat.slice 1 3438 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice194 : Part6Nat.slice 1 3438 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice195 : Part6Nat.slice 1 3438 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice196 : Part6Nat.slice 1 3438 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice197 : Part6Nat.slice 1 3438 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice198 : Part6Nat.slice 1 3438 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice199 : Part6Nat.slice 1 3438 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice200 : Part6Nat.slice 1 3438 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice201 : Part6Nat.slice 1 3438 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point201slice202 : Part6Nat.slice 1 3438 202 = true := by
  decide +kernel

public theorem point201 : stepCheck 1 3438 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point201slice0
  · exact point201slice1
  · exact point201slice2
  · exact point201slice3
  · exact point201slice4
  · exact point201slice5
  · exact point201slice6
  · exact point201slice7
  · exact point201slice8
  · exact point201slice9
  · exact point201slice10
  · exact point201slice11
  · exact point201slice12
  · exact point201slice13
  · exact point201slice14
  · exact point201slice15
  · exact point201slice16
  · exact point201slice17
  · exact point201slice18
  · exact point201slice19
  · exact point201slice20
  · exact point201slice21
  · exact point201slice22
  · exact point201slice23
  · exact point201slice24
  · exact point201slice25
  · exact point201slice26
  · exact point201slice27
  · exact point201slice28
  · exact point201slice29
  · exact point201slice30
  · exact point201slice31
  · exact point201slice32
  · exact point201slice33
  · exact point201slice34
  · exact point201slice35
  · exact point201slice36
  · exact point201slice37
  · exact point201slice38
  · exact point201slice39
  · exact point201slice40
  · exact point201slice41
  · exact point201slice42
  · exact point201slice43
  · exact point201slice44
  · exact point201slice45
  · exact point201slice46
  · exact point201slice47
  · exact point201slice48
  · exact point201slice49
  · exact point201slice50
  · exact point201slice51
  · exact point201slice52
  · exact point201slice53
  · exact point201slice54
  · exact point201slice55
  · exact point201slice56
  · exact point201slice57
  · exact point201slice58
  · exact point201slice59
  · exact point201slice60
  · exact point201slice61
  · exact point201slice62
  · exact point201slice63
  · exact point201slice64
  · exact point201slice65
  · exact point201slice66
  · exact point201slice67
  · exact point201slice68
  · exact point201slice69
  · exact point201slice70
  · exact point201slice71
  · exact point201slice72
  · exact point201slice73
  · exact point201slice74
  · exact point201slice75
  · exact point201slice76
  · exact point201slice77
  · exact point201slice78
  · exact point201slice79
  · exact point201slice80
  · exact point201slice81
  · exact point201slice82
  · exact point201slice83
  · exact point201slice84
  · exact point201slice85
  · exact point201slice86
  · exact point201slice87
  · exact point201slice88
  · exact point201slice89
  · exact point201slice90
  · exact point201slice91
  · exact point201slice92
  · exact point201slice93
  · exact point201slice94
  · exact point201slice95
  · exact point201slice96
  · exact point201slice97
  · exact point201slice98
  · exact point201slice99
  · exact point201slice100
  · exact point201slice101
  · exact point201slice102
  · exact point201slice103
  · exact point201slice104
  · exact point201slice105
  · exact point201slice106
  · exact point201slice107
  · exact point201slice108
  · exact point201slice109
  · exact point201slice110
  · exact point201slice111
  · exact point201slice112
  · exact point201slice113
  · exact point201slice114
  · exact point201slice115
  · exact point201slice116
  · exact point201slice117
  · exact point201slice118
  · exact point201slice119
  · exact point201slice120
  · exact point201slice121
  · exact point201slice122
  · exact point201slice123
  · exact point201slice124
  · exact point201slice125
  · exact point201slice126
  · exact point201slice127
  · exact point201slice128
  · exact point201slice129
  · exact point201slice130
  · exact point201slice131
  · exact point201slice132
  · exact point201slice133
  · exact point201slice134
  · exact point201slice135
  · exact point201slice136
  · exact point201slice137
  · exact point201slice138
  · exact point201slice139
  · exact point201slice140
  · exact point201slice141
  · exact point201slice142
  · exact point201slice143
  · exact point201slice144
  · exact point201slice145
  · exact point201slice146
  · exact point201slice147
  · exact point201slice148
  · exact point201slice149
  · exact point201slice150
  · exact point201slice151
  · exact point201slice152
  · exact point201slice153
  · exact point201slice154
  · exact point201slice155
  · exact point201slice156
  · exact point201slice157
  · exact point201slice158
  · exact point201slice159
  · exact point201slice160
  · exact point201slice161
  · exact point201slice162
  · exact point201slice163
  · exact point201slice164
  · exact point201slice165
  · exact point201slice166
  · exact point201slice167
  · exact point201slice168
  · exact point201slice169
  · exact point201slice170
  · exact point201slice171
  · exact point201slice172
  · exact point201slice173
  · exact point201slice174
  · exact point201slice175
  · exact point201slice176
  · exact point201slice177
  · exact point201slice178
  · exact point201slice179
  · exact point201slice180
  · exact point201slice181
  · exact point201slice182
  · exact point201slice183
  · exact point201slice184
  · exact point201slice185
  · exact point201slice186
  · exact point201slice187
  · exact point201slice188
  · exact point201slice189
  · exact point201slice190
  · exact point201slice191
  · exact point201slice192
  · exact point201slice193
  · exact point201slice194
  · exact point201slice195
  · exact point201slice196
  · exact point201slice197
  · exact point201slice198
  · exact point201slice199
  · exact point201slice200
  · exact point201slice201
  · exact point201slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
