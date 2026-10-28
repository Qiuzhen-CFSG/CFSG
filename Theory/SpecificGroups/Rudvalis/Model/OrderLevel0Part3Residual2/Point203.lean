module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2Blocks
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 203

Certify the prescribed forward-generator identity at residual index 203.
The 203 kernel-checked slices cover all 4060 points; `Part6Nat.ofSlices`
transfers these checks to the permutation identity. Source: `OrderLevel0Data`
and `Part3Residual.target`, with witness provenance in
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point203slice0 : Part6Nat.slice 0 3571 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice1 : Part6Nat.slice 0 3571 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice2 : Part6Nat.slice 0 3571 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice3 : Part6Nat.slice 0 3571 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice4 : Part6Nat.slice 0 3571 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice5 : Part6Nat.slice 0 3571 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice6 : Part6Nat.slice 0 3571 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice7 : Part6Nat.slice 0 3571 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice8 : Part6Nat.slice 0 3571 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice9 : Part6Nat.slice 0 3571 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice10 : Part6Nat.slice 0 3571 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice11 : Part6Nat.slice 0 3571 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice12 : Part6Nat.slice 0 3571 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice13 : Part6Nat.slice 0 3571 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice14 : Part6Nat.slice 0 3571 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice15 : Part6Nat.slice 0 3571 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice16 : Part6Nat.slice 0 3571 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice17 : Part6Nat.slice 0 3571 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice18 : Part6Nat.slice 0 3571 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice19 : Part6Nat.slice 0 3571 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice20 : Part6Nat.slice 0 3571 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice21 : Part6Nat.slice 0 3571 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice22 : Part6Nat.slice 0 3571 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice23 : Part6Nat.slice 0 3571 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice24 : Part6Nat.slice 0 3571 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice25 : Part6Nat.slice 0 3571 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice26 : Part6Nat.slice 0 3571 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice27 : Part6Nat.slice 0 3571 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice28 : Part6Nat.slice 0 3571 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice29 : Part6Nat.slice 0 3571 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice30 : Part6Nat.slice 0 3571 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice31 : Part6Nat.slice 0 3571 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice32 : Part6Nat.slice 0 3571 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice33 : Part6Nat.slice 0 3571 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice34 : Part6Nat.slice 0 3571 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice35 : Part6Nat.slice 0 3571 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice36 : Part6Nat.slice 0 3571 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice37 : Part6Nat.slice 0 3571 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice38 : Part6Nat.slice 0 3571 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice39 : Part6Nat.slice 0 3571 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice40 : Part6Nat.slice 0 3571 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice41 : Part6Nat.slice 0 3571 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice42 : Part6Nat.slice 0 3571 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice43 : Part6Nat.slice 0 3571 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice44 : Part6Nat.slice 0 3571 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice45 : Part6Nat.slice 0 3571 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice46 : Part6Nat.slice 0 3571 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice47 : Part6Nat.slice 0 3571 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice48 : Part6Nat.slice 0 3571 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice49 : Part6Nat.slice 0 3571 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice50 : Part6Nat.slice 0 3571 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice51 : Part6Nat.slice 0 3571 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice52 : Part6Nat.slice 0 3571 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice53 : Part6Nat.slice 0 3571 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice54 : Part6Nat.slice 0 3571 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice55 : Part6Nat.slice 0 3571 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice56 : Part6Nat.slice 0 3571 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice57 : Part6Nat.slice 0 3571 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice58 : Part6Nat.slice 0 3571 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice59 : Part6Nat.slice 0 3571 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice60 : Part6Nat.slice 0 3571 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice61 : Part6Nat.slice 0 3571 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice62 : Part6Nat.slice 0 3571 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice63 : Part6Nat.slice 0 3571 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice64 : Part6Nat.slice 0 3571 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice65 : Part6Nat.slice 0 3571 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice66 : Part6Nat.slice 0 3571 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice67 : Part6Nat.slice 0 3571 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice68 : Part6Nat.slice 0 3571 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice69 : Part6Nat.slice 0 3571 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice70 : Part6Nat.slice 0 3571 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice71 : Part6Nat.slice 0 3571 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice72 : Part6Nat.slice 0 3571 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice73 : Part6Nat.slice 0 3571 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice74 : Part6Nat.slice 0 3571 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice75 : Part6Nat.slice 0 3571 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice76 : Part6Nat.slice 0 3571 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice77 : Part6Nat.slice 0 3571 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice78 : Part6Nat.slice 0 3571 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice79 : Part6Nat.slice 0 3571 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice80 : Part6Nat.slice 0 3571 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice81 : Part6Nat.slice 0 3571 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice82 : Part6Nat.slice 0 3571 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice83 : Part6Nat.slice 0 3571 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice84 : Part6Nat.slice 0 3571 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice85 : Part6Nat.slice 0 3571 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice86 : Part6Nat.slice 0 3571 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice87 : Part6Nat.slice 0 3571 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice88 : Part6Nat.slice 0 3571 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice89 : Part6Nat.slice 0 3571 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice90 : Part6Nat.slice 0 3571 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice91 : Part6Nat.slice 0 3571 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice92 : Part6Nat.slice 0 3571 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice93 : Part6Nat.slice 0 3571 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice94 : Part6Nat.slice 0 3571 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice95 : Part6Nat.slice 0 3571 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice96 : Part6Nat.slice 0 3571 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice97 : Part6Nat.slice 0 3571 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice98 : Part6Nat.slice 0 3571 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice99 : Part6Nat.slice 0 3571 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice100 : Part6Nat.slice 0 3571 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice101 : Part6Nat.slice 0 3571 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice102 : Part6Nat.slice 0 3571 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice103 : Part6Nat.slice 0 3571 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice104 : Part6Nat.slice 0 3571 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice105 : Part6Nat.slice 0 3571 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice106 : Part6Nat.slice 0 3571 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice107 : Part6Nat.slice 0 3571 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice108 : Part6Nat.slice 0 3571 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice109 : Part6Nat.slice 0 3571 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice110 : Part6Nat.slice 0 3571 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice111 : Part6Nat.slice 0 3571 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice112 : Part6Nat.slice 0 3571 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice113 : Part6Nat.slice 0 3571 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice114 : Part6Nat.slice 0 3571 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice115 : Part6Nat.slice 0 3571 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice116 : Part6Nat.slice 0 3571 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice117 : Part6Nat.slice 0 3571 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice118 : Part6Nat.slice 0 3571 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice119 : Part6Nat.slice 0 3571 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice120 : Part6Nat.slice 0 3571 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice121 : Part6Nat.slice 0 3571 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice122 : Part6Nat.slice 0 3571 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice123 : Part6Nat.slice 0 3571 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice124 : Part6Nat.slice 0 3571 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice125 : Part6Nat.slice 0 3571 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice126 : Part6Nat.slice 0 3571 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice127 : Part6Nat.slice 0 3571 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice128 : Part6Nat.slice 0 3571 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice129 : Part6Nat.slice 0 3571 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice130 : Part6Nat.slice 0 3571 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice131 : Part6Nat.slice 0 3571 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice132 : Part6Nat.slice 0 3571 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice133 : Part6Nat.slice 0 3571 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice134 : Part6Nat.slice 0 3571 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice135 : Part6Nat.slice 0 3571 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice136 : Part6Nat.slice 0 3571 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice137 : Part6Nat.slice 0 3571 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice138 : Part6Nat.slice 0 3571 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice139 : Part6Nat.slice 0 3571 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice140 : Part6Nat.slice 0 3571 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice141 : Part6Nat.slice 0 3571 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice142 : Part6Nat.slice 0 3571 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice143 : Part6Nat.slice 0 3571 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice144 : Part6Nat.slice 0 3571 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice145 : Part6Nat.slice 0 3571 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice146 : Part6Nat.slice 0 3571 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice147 : Part6Nat.slice 0 3571 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice148 : Part6Nat.slice 0 3571 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice149 : Part6Nat.slice 0 3571 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice150 : Part6Nat.slice 0 3571 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice151 : Part6Nat.slice 0 3571 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice152 : Part6Nat.slice 0 3571 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice153 : Part6Nat.slice 0 3571 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice154 : Part6Nat.slice 0 3571 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice155 : Part6Nat.slice 0 3571 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice156 : Part6Nat.slice 0 3571 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice157 : Part6Nat.slice 0 3571 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice158 : Part6Nat.slice 0 3571 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice159 : Part6Nat.slice 0 3571 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice160 : Part6Nat.slice 0 3571 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice161 : Part6Nat.slice 0 3571 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice162 : Part6Nat.slice 0 3571 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice163 : Part6Nat.slice 0 3571 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice164 : Part6Nat.slice 0 3571 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice165 : Part6Nat.slice 0 3571 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice166 : Part6Nat.slice 0 3571 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice167 : Part6Nat.slice 0 3571 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice168 : Part6Nat.slice 0 3571 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice169 : Part6Nat.slice 0 3571 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice170 : Part6Nat.slice 0 3571 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice171 : Part6Nat.slice 0 3571 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice172 : Part6Nat.slice 0 3571 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice173 : Part6Nat.slice 0 3571 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice174 : Part6Nat.slice 0 3571 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice175 : Part6Nat.slice 0 3571 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice176 : Part6Nat.slice 0 3571 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice177 : Part6Nat.slice 0 3571 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice178 : Part6Nat.slice 0 3571 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice179 : Part6Nat.slice 0 3571 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice180 : Part6Nat.slice 0 3571 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice181 : Part6Nat.slice 0 3571 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice182 : Part6Nat.slice 0 3571 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice183 : Part6Nat.slice 0 3571 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice184 : Part6Nat.slice 0 3571 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice185 : Part6Nat.slice 0 3571 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice186 : Part6Nat.slice 0 3571 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice187 : Part6Nat.slice 0 3571 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice188 : Part6Nat.slice 0 3571 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice189 : Part6Nat.slice 0 3571 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice190 : Part6Nat.slice 0 3571 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice191 : Part6Nat.slice 0 3571 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice192 : Part6Nat.slice 0 3571 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice193 : Part6Nat.slice 0 3571 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice194 : Part6Nat.slice 0 3571 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice195 : Part6Nat.slice 0 3571 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice196 : Part6Nat.slice 0 3571 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice197 : Part6Nat.slice 0 3571 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice198 : Part6Nat.slice 0 3571 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice199 : Part6Nat.slice 0 3571 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice200 : Part6Nat.slice 0 3571 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice201 : Part6Nat.slice 0 3571 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point203slice202 : Part6Nat.slice 0 3571 202 = true := by
  decide +kernel

public theorem point203 : stepCheck 0 3571 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point203slice0
  · exact point203slice1
  · exact point203slice2
  · exact point203slice3
  · exact point203slice4
  · exact point203slice5
  · exact point203slice6
  · exact point203slice7
  · exact point203slice8
  · exact point203slice9
  · exact point203slice10
  · exact point203slice11
  · exact point203slice12
  · exact point203slice13
  · exact point203slice14
  · exact point203slice15
  · exact point203slice16
  · exact point203slice17
  · exact point203slice18
  · exact point203slice19
  · exact point203slice20
  · exact point203slice21
  · exact point203slice22
  · exact point203slice23
  · exact point203slice24
  · exact point203slice25
  · exact point203slice26
  · exact point203slice27
  · exact point203slice28
  · exact point203slice29
  · exact point203slice30
  · exact point203slice31
  · exact point203slice32
  · exact point203slice33
  · exact point203slice34
  · exact point203slice35
  · exact point203slice36
  · exact point203slice37
  · exact point203slice38
  · exact point203slice39
  · exact point203slice40
  · exact point203slice41
  · exact point203slice42
  · exact point203slice43
  · exact point203slice44
  · exact point203slice45
  · exact point203slice46
  · exact point203slice47
  · exact point203slice48
  · exact point203slice49
  · exact point203slice50
  · exact point203slice51
  · exact point203slice52
  · exact point203slice53
  · exact point203slice54
  · exact point203slice55
  · exact point203slice56
  · exact point203slice57
  · exact point203slice58
  · exact point203slice59
  · exact point203slice60
  · exact point203slice61
  · exact point203slice62
  · exact point203slice63
  · exact point203slice64
  · exact point203slice65
  · exact point203slice66
  · exact point203slice67
  · exact point203slice68
  · exact point203slice69
  · exact point203slice70
  · exact point203slice71
  · exact point203slice72
  · exact point203slice73
  · exact point203slice74
  · exact point203slice75
  · exact point203slice76
  · exact point203slice77
  · exact point203slice78
  · exact point203slice79
  · exact point203slice80
  · exact point203slice81
  · exact point203slice82
  · exact point203slice83
  · exact point203slice84
  · exact point203slice85
  · exact point203slice86
  · exact point203slice87
  · exact point203slice88
  · exact point203slice89
  · exact point203slice90
  · exact point203slice91
  · exact point203slice92
  · exact point203slice93
  · exact point203slice94
  · exact point203slice95
  · exact point203slice96
  · exact point203slice97
  · exact point203slice98
  · exact point203slice99
  · exact point203slice100
  · exact point203slice101
  · exact point203slice102
  · exact point203slice103
  · exact point203slice104
  · exact point203slice105
  · exact point203slice106
  · exact point203slice107
  · exact point203slice108
  · exact point203slice109
  · exact point203slice110
  · exact point203slice111
  · exact point203slice112
  · exact point203slice113
  · exact point203slice114
  · exact point203slice115
  · exact point203slice116
  · exact point203slice117
  · exact point203slice118
  · exact point203slice119
  · exact point203slice120
  · exact point203slice121
  · exact point203slice122
  · exact point203slice123
  · exact point203slice124
  · exact point203slice125
  · exact point203slice126
  · exact point203slice127
  · exact point203slice128
  · exact point203slice129
  · exact point203slice130
  · exact point203slice131
  · exact point203slice132
  · exact point203slice133
  · exact point203slice134
  · exact point203slice135
  · exact point203slice136
  · exact point203slice137
  · exact point203slice138
  · exact point203slice139
  · exact point203slice140
  · exact point203slice141
  · exact point203slice142
  · exact point203slice143
  · exact point203slice144
  · exact point203slice145
  · exact point203slice146
  · exact point203slice147
  · exact point203slice148
  · exact point203slice149
  · exact point203slice150
  · exact point203slice151
  · exact point203slice152
  · exact point203slice153
  · exact point203slice154
  · exact point203slice155
  · exact point203slice156
  · exact point203slice157
  · exact point203slice158
  · exact point203slice159
  · exact point203slice160
  · exact point203slice161
  · exact point203slice162
  · exact point203slice163
  · exact point203slice164
  · exact point203slice165
  · exact point203slice166
  · exact point203slice167
  · exact point203slice168
  · exact point203slice169
  · exact point203slice170
  · exact point203slice171
  · exact point203slice172
  · exact point203slice173
  · exact point203slice174
  · exact point203slice175
  · exact point203slice176
  · exact point203slice177
  · exact point203slice178
  · exact point203slice179
  · exact point203slice180
  · exact point203slice181
  · exact point203slice182
  · exact point203slice183
  · exact point203slice184
  · exact point203slice185
  · exact point203slice186
  · exact point203slice187
  · exact point203slice188
  · exact point203slice189
  · exact point203slice190
  · exact point203slice191
  · exact point203slice192
  · exact point203slice193
  · exact point203slice194
  · exact point203slice195
  · exact point203slice196
  · exact point203slice197
  · exact point203slice198
  · exact point203slice199
  · exact point203slice200
  · exact point203slice201
  · exact point203slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
