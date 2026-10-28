module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2Blocks
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 192

Certify the prescribed forward-generator identity at residual index 192.
The 203 kernel-checked slices cover all 4060 points; `Part6Nat.ofSlices`
transfers these checks to the permutation identity. Source: `OrderLevel0Data`
and `Part3Residual.target`, with witness provenance in
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point192slice0 : Part6Nat.slice 0 3438 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice1 : Part6Nat.slice 0 3438 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice2 : Part6Nat.slice 0 3438 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice3 : Part6Nat.slice 0 3438 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice4 : Part6Nat.slice 0 3438 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice5 : Part6Nat.slice 0 3438 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice6 : Part6Nat.slice 0 3438 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice7 : Part6Nat.slice 0 3438 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice8 : Part6Nat.slice 0 3438 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice9 : Part6Nat.slice 0 3438 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice10 : Part6Nat.slice 0 3438 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice11 : Part6Nat.slice 0 3438 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice12 : Part6Nat.slice 0 3438 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice13 : Part6Nat.slice 0 3438 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice14 : Part6Nat.slice 0 3438 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice15 : Part6Nat.slice 0 3438 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice16 : Part6Nat.slice 0 3438 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice17 : Part6Nat.slice 0 3438 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice18 : Part6Nat.slice 0 3438 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice19 : Part6Nat.slice 0 3438 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice20 : Part6Nat.slice 0 3438 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice21 : Part6Nat.slice 0 3438 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice22 : Part6Nat.slice 0 3438 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice23 : Part6Nat.slice 0 3438 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice24 : Part6Nat.slice 0 3438 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice25 : Part6Nat.slice 0 3438 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice26 : Part6Nat.slice 0 3438 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice27 : Part6Nat.slice 0 3438 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice28 : Part6Nat.slice 0 3438 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice29 : Part6Nat.slice 0 3438 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice30 : Part6Nat.slice 0 3438 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice31 : Part6Nat.slice 0 3438 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice32 : Part6Nat.slice 0 3438 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice33 : Part6Nat.slice 0 3438 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice34 : Part6Nat.slice 0 3438 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice35 : Part6Nat.slice 0 3438 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice36 : Part6Nat.slice 0 3438 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice37 : Part6Nat.slice 0 3438 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice38 : Part6Nat.slice 0 3438 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice39 : Part6Nat.slice 0 3438 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice40 : Part6Nat.slice 0 3438 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice41 : Part6Nat.slice 0 3438 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice42 : Part6Nat.slice 0 3438 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice43 : Part6Nat.slice 0 3438 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice44 : Part6Nat.slice 0 3438 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice45 : Part6Nat.slice 0 3438 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice46 : Part6Nat.slice 0 3438 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice47 : Part6Nat.slice 0 3438 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice48 : Part6Nat.slice 0 3438 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice49 : Part6Nat.slice 0 3438 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice50 : Part6Nat.slice 0 3438 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice51 : Part6Nat.slice 0 3438 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice52 : Part6Nat.slice 0 3438 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice53 : Part6Nat.slice 0 3438 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice54 : Part6Nat.slice 0 3438 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice55 : Part6Nat.slice 0 3438 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice56 : Part6Nat.slice 0 3438 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice57 : Part6Nat.slice 0 3438 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice58 : Part6Nat.slice 0 3438 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice59 : Part6Nat.slice 0 3438 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice60 : Part6Nat.slice 0 3438 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice61 : Part6Nat.slice 0 3438 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice62 : Part6Nat.slice 0 3438 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice63 : Part6Nat.slice 0 3438 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice64 : Part6Nat.slice 0 3438 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice65 : Part6Nat.slice 0 3438 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice66 : Part6Nat.slice 0 3438 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice67 : Part6Nat.slice 0 3438 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice68 : Part6Nat.slice 0 3438 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice69 : Part6Nat.slice 0 3438 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice70 : Part6Nat.slice 0 3438 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice71 : Part6Nat.slice 0 3438 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice72 : Part6Nat.slice 0 3438 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice73 : Part6Nat.slice 0 3438 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice74 : Part6Nat.slice 0 3438 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice75 : Part6Nat.slice 0 3438 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice76 : Part6Nat.slice 0 3438 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice77 : Part6Nat.slice 0 3438 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice78 : Part6Nat.slice 0 3438 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice79 : Part6Nat.slice 0 3438 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice80 : Part6Nat.slice 0 3438 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice81 : Part6Nat.slice 0 3438 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice82 : Part6Nat.slice 0 3438 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice83 : Part6Nat.slice 0 3438 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice84 : Part6Nat.slice 0 3438 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice85 : Part6Nat.slice 0 3438 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice86 : Part6Nat.slice 0 3438 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice87 : Part6Nat.slice 0 3438 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice88 : Part6Nat.slice 0 3438 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice89 : Part6Nat.slice 0 3438 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice90 : Part6Nat.slice 0 3438 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice91 : Part6Nat.slice 0 3438 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice92 : Part6Nat.slice 0 3438 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice93 : Part6Nat.slice 0 3438 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice94 : Part6Nat.slice 0 3438 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice95 : Part6Nat.slice 0 3438 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice96 : Part6Nat.slice 0 3438 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice97 : Part6Nat.slice 0 3438 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice98 : Part6Nat.slice 0 3438 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice99 : Part6Nat.slice 0 3438 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice100 : Part6Nat.slice 0 3438 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice101 : Part6Nat.slice 0 3438 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice102 : Part6Nat.slice 0 3438 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice103 : Part6Nat.slice 0 3438 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice104 : Part6Nat.slice 0 3438 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice105 : Part6Nat.slice 0 3438 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice106 : Part6Nat.slice 0 3438 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice107 : Part6Nat.slice 0 3438 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice108 : Part6Nat.slice 0 3438 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice109 : Part6Nat.slice 0 3438 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice110 : Part6Nat.slice 0 3438 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice111 : Part6Nat.slice 0 3438 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice112 : Part6Nat.slice 0 3438 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice113 : Part6Nat.slice 0 3438 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice114 : Part6Nat.slice 0 3438 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice115 : Part6Nat.slice 0 3438 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice116 : Part6Nat.slice 0 3438 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice117 : Part6Nat.slice 0 3438 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice118 : Part6Nat.slice 0 3438 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice119 : Part6Nat.slice 0 3438 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice120 : Part6Nat.slice 0 3438 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice121 : Part6Nat.slice 0 3438 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice122 : Part6Nat.slice 0 3438 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice123 : Part6Nat.slice 0 3438 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice124 : Part6Nat.slice 0 3438 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice125 : Part6Nat.slice 0 3438 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice126 : Part6Nat.slice 0 3438 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice127 : Part6Nat.slice 0 3438 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice128 : Part6Nat.slice 0 3438 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice129 : Part6Nat.slice 0 3438 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice130 : Part6Nat.slice 0 3438 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice131 : Part6Nat.slice 0 3438 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice132 : Part6Nat.slice 0 3438 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice133 : Part6Nat.slice 0 3438 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice134 : Part6Nat.slice 0 3438 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice135 : Part6Nat.slice 0 3438 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice136 : Part6Nat.slice 0 3438 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice137 : Part6Nat.slice 0 3438 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice138 : Part6Nat.slice 0 3438 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice139 : Part6Nat.slice 0 3438 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice140 : Part6Nat.slice 0 3438 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice141 : Part6Nat.slice 0 3438 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice142 : Part6Nat.slice 0 3438 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice143 : Part6Nat.slice 0 3438 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice144 : Part6Nat.slice 0 3438 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice145 : Part6Nat.slice 0 3438 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice146 : Part6Nat.slice 0 3438 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice147 : Part6Nat.slice 0 3438 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice148 : Part6Nat.slice 0 3438 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice149 : Part6Nat.slice 0 3438 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice150 : Part6Nat.slice 0 3438 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice151 : Part6Nat.slice 0 3438 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice152 : Part6Nat.slice 0 3438 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice153 : Part6Nat.slice 0 3438 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice154 : Part6Nat.slice 0 3438 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice155 : Part6Nat.slice 0 3438 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice156 : Part6Nat.slice 0 3438 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice157 : Part6Nat.slice 0 3438 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice158 : Part6Nat.slice 0 3438 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice159 : Part6Nat.slice 0 3438 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice160 : Part6Nat.slice 0 3438 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice161 : Part6Nat.slice 0 3438 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice162 : Part6Nat.slice 0 3438 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice163 : Part6Nat.slice 0 3438 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice164 : Part6Nat.slice 0 3438 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice165 : Part6Nat.slice 0 3438 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice166 : Part6Nat.slice 0 3438 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice167 : Part6Nat.slice 0 3438 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice168 : Part6Nat.slice 0 3438 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice169 : Part6Nat.slice 0 3438 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice170 : Part6Nat.slice 0 3438 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice171 : Part6Nat.slice 0 3438 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice172 : Part6Nat.slice 0 3438 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice173 : Part6Nat.slice 0 3438 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice174 : Part6Nat.slice 0 3438 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice175 : Part6Nat.slice 0 3438 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice176 : Part6Nat.slice 0 3438 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice177 : Part6Nat.slice 0 3438 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice178 : Part6Nat.slice 0 3438 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice179 : Part6Nat.slice 0 3438 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice180 : Part6Nat.slice 0 3438 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice181 : Part6Nat.slice 0 3438 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice182 : Part6Nat.slice 0 3438 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice183 : Part6Nat.slice 0 3438 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice184 : Part6Nat.slice 0 3438 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice185 : Part6Nat.slice 0 3438 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice186 : Part6Nat.slice 0 3438 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice187 : Part6Nat.slice 0 3438 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice188 : Part6Nat.slice 0 3438 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice189 : Part6Nat.slice 0 3438 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice190 : Part6Nat.slice 0 3438 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice191 : Part6Nat.slice 0 3438 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice192 : Part6Nat.slice 0 3438 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice193 : Part6Nat.slice 0 3438 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice194 : Part6Nat.slice 0 3438 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice195 : Part6Nat.slice 0 3438 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice196 : Part6Nat.slice 0 3438 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice197 : Part6Nat.slice 0 3438 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice198 : Part6Nat.slice 0 3438 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice199 : Part6Nat.slice 0 3438 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice200 : Part6Nat.slice 0 3438 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice201 : Part6Nat.slice 0 3438 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point192slice202 : Part6Nat.slice 0 3438 202 = true := by
  decide +kernel

public theorem point192 : stepCheck 0 3438 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point192slice0
  · exact point192slice1
  · exact point192slice2
  · exact point192slice3
  · exact point192slice4
  · exact point192slice5
  · exact point192slice6
  · exact point192slice7
  · exact point192slice8
  · exact point192slice9
  · exact point192slice10
  · exact point192slice11
  · exact point192slice12
  · exact point192slice13
  · exact point192slice14
  · exact point192slice15
  · exact point192slice16
  · exact point192slice17
  · exact point192slice18
  · exact point192slice19
  · exact point192slice20
  · exact point192slice21
  · exact point192slice22
  · exact point192slice23
  · exact point192slice24
  · exact point192slice25
  · exact point192slice26
  · exact point192slice27
  · exact point192slice28
  · exact point192slice29
  · exact point192slice30
  · exact point192slice31
  · exact point192slice32
  · exact point192slice33
  · exact point192slice34
  · exact point192slice35
  · exact point192slice36
  · exact point192slice37
  · exact point192slice38
  · exact point192slice39
  · exact point192slice40
  · exact point192slice41
  · exact point192slice42
  · exact point192slice43
  · exact point192slice44
  · exact point192slice45
  · exact point192slice46
  · exact point192slice47
  · exact point192slice48
  · exact point192slice49
  · exact point192slice50
  · exact point192slice51
  · exact point192slice52
  · exact point192slice53
  · exact point192slice54
  · exact point192slice55
  · exact point192slice56
  · exact point192slice57
  · exact point192slice58
  · exact point192slice59
  · exact point192slice60
  · exact point192slice61
  · exact point192slice62
  · exact point192slice63
  · exact point192slice64
  · exact point192slice65
  · exact point192slice66
  · exact point192slice67
  · exact point192slice68
  · exact point192slice69
  · exact point192slice70
  · exact point192slice71
  · exact point192slice72
  · exact point192slice73
  · exact point192slice74
  · exact point192slice75
  · exact point192slice76
  · exact point192slice77
  · exact point192slice78
  · exact point192slice79
  · exact point192slice80
  · exact point192slice81
  · exact point192slice82
  · exact point192slice83
  · exact point192slice84
  · exact point192slice85
  · exact point192slice86
  · exact point192slice87
  · exact point192slice88
  · exact point192slice89
  · exact point192slice90
  · exact point192slice91
  · exact point192slice92
  · exact point192slice93
  · exact point192slice94
  · exact point192slice95
  · exact point192slice96
  · exact point192slice97
  · exact point192slice98
  · exact point192slice99
  · exact point192slice100
  · exact point192slice101
  · exact point192slice102
  · exact point192slice103
  · exact point192slice104
  · exact point192slice105
  · exact point192slice106
  · exact point192slice107
  · exact point192slice108
  · exact point192slice109
  · exact point192slice110
  · exact point192slice111
  · exact point192slice112
  · exact point192slice113
  · exact point192slice114
  · exact point192slice115
  · exact point192slice116
  · exact point192slice117
  · exact point192slice118
  · exact point192slice119
  · exact point192slice120
  · exact point192slice121
  · exact point192slice122
  · exact point192slice123
  · exact point192slice124
  · exact point192slice125
  · exact point192slice126
  · exact point192slice127
  · exact point192slice128
  · exact point192slice129
  · exact point192slice130
  · exact point192slice131
  · exact point192slice132
  · exact point192slice133
  · exact point192slice134
  · exact point192slice135
  · exact point192slice136
  · exact point192slice137
  · exact point192slice138
  · exact point192slice139
  · exact point192slice140
  · exact point192slice141
  · exact point192slice142
  · exact point192slice143
  · exact point192slice144
  · exact point192slice145
  · exact point192slice146
  · exact point192slice147
  · exact point192slice148
  · exact point192slice149
  · exact point192slice150
  · exact point192slice151
  · exact point192slice152
  · exact point192slice153
  · exact point192slice154
  · exact point192slice155
  · exact point192slice156
  · exact point192slice157
  · exact point192slice158
  · exact point192slice159
  · exact point192slice160
  · exact point192slice161
  · exact point192slice162
  · exact point192slice163
  · exact point192slice164
  · exact point192slice165
  · exact point192slice166
  · exact point192slice167
  · exact point192slice168
  · exact point192slice169
  · exact point192slice170
  · exact point192slice171
  · exact point192slice172
  · exact point192slice173
  · exact point192slice174
  · exact point192slice175
  · exact point192slice176
  · exact point192slice177
  · exact point192slice178
  · exact point192slice179
  · exact point192slice180
  · exact point192slice181
  · exact point192slice182
  · exact point192slice183
  · exact point192slice184
  · exact point192slice185
  · exact point192slice186
  · exact point192slice187
  · exact point192slice188
  · exact point192slice189
  · exact point192slice190
  · exact point192slice191
  · exact point192slice192
  · exact point192slice193
  · exact point192slice194
  · exact point192slice195
  · exact point192slice196
  · exact point192slice197
  · exact point192slice198
  · exact point192slice199
  · exact point192slice200
  · exact point192slice201
  · exact point192slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
