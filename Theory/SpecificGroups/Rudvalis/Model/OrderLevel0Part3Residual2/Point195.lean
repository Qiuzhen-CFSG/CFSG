module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2Blocks
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 195

Certify the prescribed forward-generator identity at residual index 195.
The 203 kernel-checked slices cover all 4060 points; `Part6Nat.ofSlices`
transfers these checks to the permutation identity. Source: `OrderLevel0Data`
and `Part3Residual.target`, with witness provenance in
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point195slice0 : Part6Nat.slice 1 3425 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice1 : Part6Nat.slice 1 3425 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice2 : Part6Nat.slice 1 3425 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice3 : Part6Nat.slice 1 3425 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice4 : Part6Nat.slice 1 3425 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice5 : Part6Nat.slice 1 3425 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice6 : Part6Nat.slice 1 3425 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice7 : Part6Nat.slice 1 3425 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice8 : Part6Nat.slice 1 3425 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice9 : Part6Nat.slice 1 3425 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice10 : Part6Nat.slice 1 3425 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice11 : Part6Nat.slice 1 3425 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice12 : Part6Nat.slice 1 3425 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice13 : Part6Nat.slice 1 3425 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice14 : Part6Nat.slice 1 3425 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice15 : Part6Nat.slice 1 3425 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice16 : Part6Nat.slice 1 3425 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice17 : Part6Nat.slice 1 3425 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice18 : Part6Nat.slice 1 3425 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice19 : Part6Nat.slice 1 3425 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice20 : Part6Nat.slice 1 3425 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice21 : Part6Nat.slice 1 3425 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice22 : Part6Nat.slice 1 3425 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice23 : Part6Nat.slice 1 3425 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice24 : Part6Nat.slice 1 3425 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice25 : Part6Nat.slice 1 3425 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice26 : Part6Nat.slice 1 3425 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice27 : Part6Nat.slice 1 3425 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice28 : Part6Nat.slice 1 3425 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice29 : Part6Nat.slice 1 3425 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice30 : Part6Nat.slice 1 3425 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice31 : Part6Nat.slice 1 3425 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice32 : Part6Nat.slice 1 3425 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice33 : Part6Nat.slice 1 3425 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice34 : Part6Nat.slice 1 3425 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice35 : Part6Nat.slice 1 3425 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice36 : Part6Nat.slice 1 3425 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice37 : Part6Nat.slice 1 3425 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice38 : Part6Nat.slice 1 3425 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice39 : Part6Nat.slice 1 3425 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice40 : Part6Nat.slice 1 3425 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice41 : Part6Nat.slice 1 3425 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice42 : Part6Nat.slice 1 3425 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice43 : Part6Nat.slice 1 3425 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice44 : Part6Nat.slice 1 3425 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice45 : Part6Nat.slice 1 3425 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice46 : Part6Nat.slice 1 3425 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice47 : Part6Nat.slice 1 3425 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice48 : Part6Nat.slice 1 3425 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice49 : Part6Nat.slice 1 3425 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice50 : Part6Nat.slice 1 3425 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice51 : Part6Nat.slice 1 3425 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice52 : Part6Nat.slice 1 3425 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice53 : Part6Nat.slice 1 3425 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice54 : Part6Nat.slice 1 3425 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice55 : Part6Nat.slice 1 3425 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice56 : Part6Nat.slice 1 3425 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice57 : Part6Nat.slice 1 3425 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice58 : Part6Nat.slice 1 3425 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice59 : Part6Nat.slice 1 3425 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice60 : Part6Nat.slice 1 3425 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice61 : Part6Nat.slice 1 3425 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice62 : Part6Nat.slice 1 3425 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice63 : Part6Nat.slice 1 3425 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice64 : Part6Nat.slice 1 3425 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice65 : Part6Nat.slice 1 3425 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice66 : Part6Nat.slice 1 3425 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice67 : Part6Nat.slice 1 3425 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice68 : Part6Nat.slice 1 3425 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice69 : Part6Nat.slice 1 3425 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice70 : Part6Nat.slice 1 3425 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice71 : Part6Nat.slice 1 3425 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice72 : Part6Nat.slice 1 3425 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice73 : Part6Nat.slice 1 3425 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice74 : Part6Nat.slice 1 3425 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice75 : Part6Nat.slice 1 3425 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice76 : Part6Nat.slice 1 3425 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice77 : Part6Nat.slice 1 3425 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice78 : Part6Nat.slice 1 3425 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice79 : Part6Nat.slice 1 3425 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice80 : Part6Nat.slice 1 3425 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice81 : Part6Nat.slice 1 3425 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice82 : Part6Nat.slice 1 3425 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice83 : Part6Nat.slice 1 3425 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice84 : Part6Nat.slice 1 3425 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice85 : Part6Nat.slice 1 3425 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice86 : Part6Nat.slice 1 3425 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice87 : Part6Nat.slice 1 3425 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice88 : Part6Nat.slice 1 3425 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice89 : Part6Nat.slice 1 3425 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice90 : Part6Nat.slice 1 3425 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice91 : Part6Nat.slice 1 3425 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice92 : Part6Nat.slice 1 3425 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice93 : Part6Nat.slice 1 3425 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice94 : Part6Nat.slice 1 3425 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice95 : Part6Nat.slice 1 3425 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice96 : Part6Nat.slice 1 3425 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice97 : Part6Nat.slice 1 3425 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice98 : Part6Nat.slice 1 3425 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice99 : Part6Nat.slice 1 3425 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice100 : Part6Nat.slice 1 3425 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice101 : Part6Nat.slice 1 3425 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice102 : Part6Nat.slice 1 3425 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice103 : Part6Nat.slice 1 3425 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice104 : Part6Nat.slice 1 3425 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice105 : Part6Nat.slice 1 3425 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice106 : Part6Nat.slice 1 3425 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice107 : Part6Nat.slice 1 3425 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice108 : Part6Nat.slice 1 3425 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice109 : Part6Nat.slice 1 3425 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice110 : Part6Nat.slice 1 3425 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice111 : Part6Nat.slice 1 3425 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice112 : Part6Nat.slice 1 3425 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice113 : Part6Nat.slice 1 3425 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice114 : Part6Nat.slice 1 3425 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice115 : Part6Nat.slice 1 3425 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice116 : Part6Nat.slice 1 3425 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice117 : Part6Nat.slice 1 3425 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice118 : Part6Nat.slice 1 3425 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice119 : Part6Nat.slice 1 3425 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice120 : Part6Nat.slice 1 3425 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice121 : Part6Nat.slice 1 3425 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice122 : Part6Nat.slice 1 3425 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice123 : Part6Nat.slice 1 3425 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice124 : Part6Nat.slice 1 3425 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice125 : Part6Nat.slice 1 3425 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice126 : Part6Nat.slice 1 3425 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice127 : Part6Nat.slice 1 3425 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice128 : Part6Nat.slice 1 3425 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice129 : Part6Nat.slice 1 3425 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice130 : Part6Nat.slice 1 3425 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice131 : Part6Nat.slice 1 3425 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice132 : Part6Nat.slice 1 3425 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice133 : Part6Nat.slice 1 3425 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice134 : Part6Nat.slice 1 3425 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice135 : Part6Nat.slice 1 3425 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice136 : Part6Nat.slice 1 3425 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice137 : Part6Nat.slice 1 3425 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice138 : Part6Nat.slice 1 3425 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice139 : Part6Nat.slice 1 3425 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice140 : Part6Nat.slice 1 3425 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice141 : Part6Nat.slice 1 3425 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice142 : Part6Nat.slice 1 3425 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice143 : Part6Nat.slice 1 3425 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice144 : Part6Nat.slice 1 3425 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice145 : Part6Nat.slice 1 3425 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice146 : Part6Nat.slice 1 3425 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice147 : Part6Nat.slice 1 3425 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice148 : Part6Nat.slice 1 3425 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice149 : Part6Nat.slice 1 3425 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice150 : Part6Nat.slice 1 3425 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice151 : Part6Nat.slice 1 3425 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice152 : Part6Nat.slice 1 3425 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice153 : Part6Nat.slice 1 3425 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice154 : Part6Nat.slice 1 3425 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice155 : Part6Nat.slice 1 3425 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice156 : Part6Nat.slice 1 3425 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice157 : Part6Nat.slice 1 3425 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice158 : Part6Nat.slice 1 3425 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice159 : Part6Nat.slice 1 3425 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice160 : Part6Nat.slice 1 3425 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice161 : Part6Nat.slice 1 3425 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice162 : Part6Nat.slice 1 3425 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice163 : Part6Nat.slice 1 3425 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice164 : Part6Nat.slice 1 3425 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice165 : Part6Nat.slice 1 3425 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice166 : Part6Nat.slice 1 3425 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice167 : Part6Nat.slice 1 3425 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice168 : Part6Nat.slice 1 3425 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice169 : Part6Nat.slice 1 3425 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice170 : Part6Nat.slice 1 3425 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice171 : Part6Nat.slice 1 3425 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice172 : Part6Nat.slice 1 3425 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice173 : Part6Nat.slice 1 3425 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice174 : Part6Nat.slice 1 3425 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice175 : Part6Nat.slice 1 3425 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice176 : Part6Nat.slice 1 3425 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice177 : Part6Nat.slice 1 3425 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice178 : Part6Nat.slice 1 3425 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice179 : Part6Nat.slice 1 3425 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice180 : Part6Nat.slice 1 3425 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice181 : Part6Nat.slice 1 3425 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice182 : Part6Nat.slice 1 3425 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice183 : Part6Nat.slice 1 3425 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice184 : Part6Nat.slice 1 3425 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice185 : Part6Nat.slice 1 3425 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice186 : Part6Nat.slice 1 3425 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice187 : Part6Nat.slice 1 3425 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice188 : Part6Nat.slice 1 3425 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice189 : Part6Nat.slice 1 3425 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice190 : Part6Nat.slice 1 3425 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice191 : Part6Nat.slice 1 3425 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice192 : Part6Nat.slice 1 3425 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice193 : Part6Nat.slice 1 3425 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice194 : Part6Nat.slice 1 3425 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice195 : Part6Nat.slice 1 3425 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice196 : Part6Nat.slice 1 3425 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice197 : Part6Nat.slice 1 3425 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice198 : Part6Nat.slice 1 3425 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice199 : Part6Nat.slice 1 3425 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice200 : Part6Nat.slice 1 3425 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice201 : Part6Nat.slice 1 3425 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point195slice202 : Part6Nat.slice 1 3425 202 = true := by
  decide +kernel

public theorem point195 : stepCheck 1 3425 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point195slice0
  · exact point195slice1
  · exact point195slice2
  · exact point195slice3
  · exact point195slice4
  · exact point195slice5
  · exact point195slice6
  · exact point195slice7
  · exact point195slice8
  · exact point195slice9
  · exact point195slice10
  · exact point195slice11
  · exact point195slice12
  · exact point195slice13
  · exact point195slice14
  · exact point195slice15
  · exact point195slice16
  · exact point195slice17
  · exact point195slice18
  · exact point195slice19
  · exact point195slice20
  · exact point195slice21
  · exact point195slice22
  · exact point195slice23
  · exact point195slice24
  · exact point195slice25
  · exact point195slice26
  · exact point195slice27
  · exact point195slice28
  · exact point195slice29
  · exact point195slice30
  · exact point195slice31
  · exact point195slice32
  · exact point195slice33
  · exact point195slice34
  · exact point195slice35
  · exact point195slice36
  · exact point195slice37
  · exact point195slice38
  · exact point195slice39
  · exact point195slice40
  · exact point195slice41
  · exact point195slice42
  · exact point195slice43
  · exact point195slice44
  · exact point195slice45
  · exact point195slice46
  · exact point195slice47
  · exact point195slice48
  · exact point195slice49
  · exact point195slice50
  · exact point195slice51
  · exact point195slice52
  · exact point195slice53
  · exact point195slice54
  · exact point195slice55
  · exact point195slice56
  · exact point195slice57
  · exact point195slice58
  · exact point195slice59
  · exact point195slice60
  · exact point195slice61
  · exact point195slice62
  · exact point195slice63
  · exact point195slice64
  · exact point195slice65
  · exact point195slice66
  · exact point195slice67
  · exact point195slice68
  · exact point195slice69
  · exact point195slice70
  · exact point195slice71
  · exact point195slice72
  · exact point195slice73
  · exact point195slice74
  · exact point195slice75
  · exact point195slice76
  · exact point195slice77
  · exact point195slice78
  · exact point195slice79
  · exact point195slice80
  · exact point195slice81
  · exact point195slice82
  · exact point195slice83
  · exact point195slice84
  · exact point195slice85
  · exact point195slice86
  · exact point195slice87
  · exact point195slice88
  · exact point195slice89
  · exact point195slice90
  · exact point195slice91
  · exact point195slice92
  · exact point195slice93
  · exact point195slice94
  · exact point195slice95
  · exact point195slice96
  · exact point195slice97
  · exact point195slice98
  · exact point195slice99
  · exact point195slice100
  · exact point195slice101
  · exact point195slice102
  · exact point195slice103
  · exact point195slice104
  · exact point195slice105
  · exact point195slice106
  · exact point195slice107
  · exact point195slice108
  · exact point195slice109
  · exact point195slice110
  · exact point195slice111
  · exact point195slice112
  · exact point195slice113
  · exact point195slice114
  · exact point195slice115
  · exact point195slice116
  · exact point195slice117
  · exact point195slice118
  · exact point195slice119
  · exact point195slice120
  · exact point195slice121
  · exact point195slice122
  · exact point195slice123
  · exact point195slice124
  · exact point195slice125
  · exact point195slice126
  · exact point195slice127
  · exact point195slice128
  · exact point195slice129
  · exact point195slice130
  · exact point195slice131
  · exact point195slice132
  · exact point195slice133
  · exact point195slice134
  · exact point195slice135
  · exact point195slice136
  · exact point195slice137
  · exact point195slice138
  · exact point195slice139
  · exact point195slice140
  · exact point195slice141
  · exact point195slice142
  · exact point195slice143
  · exact point195slice144
  · exact point195slice145
  · exact point195slice146
  · exact point195slice147
  · exact point195slice148
  · exact point195slice149
  · exact point195slice150
  · exact point195slice151
  · exact point195slice152
  · exact point195slice153
  · exact point195slice154
  · exact point195slice155
  · exact point195slice156
  · exact point195slice157
  · exact point195slice158
  · exact point195slice159
  · exact point195slice160
  · exact point195slice161
  · exact point195slice162
  · exact point195slice163
  · exact point195slice164
  · exact point195slice165
  · exact point195slice166
  · exact point195slice167
  · exact point195slice168
  · exact point195slice169
  · exact point195slice170
  · exact point195slice171
  · exact point195slice172
  · exact point195slice173
  · exact point195slice174
  · exact point195slice175
  · exact point195slice176
  · exact point195slice177
  · exact point195slice178
  · exact point195slice179
  · exact point195slice180
  · exact point195slice181
  · exact point195slice182
  · exact point195slice183
  · exact point195slice184
  · exact point195slice185
  · exact point195slice186
  · exact point195slice187
  · exact point195slice188
  · exact point195slice189
  · exact point195slice190
  · exact point195slice191
  · exact point195slice192
  · exact point195slice193
  · exact point195slice194
  · exact point195slice195
  · exact point195slice196
  · exact point195slice197
  · exact point195slice198
  · exact point195slice199
  · exact point195slice200
  · exact point195slice201
  · exact point195slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
