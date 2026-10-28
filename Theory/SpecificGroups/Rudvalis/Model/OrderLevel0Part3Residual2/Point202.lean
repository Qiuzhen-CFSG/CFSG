module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual2Blocks
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-3 residual transition 202

Certify the prescribed forward-generator identity at residual index 202.
The 203 kernel-checked slices cover all 4060 points; `Part6Nat.ofSlices`
transfers these checks to the permutation identity. Source: `OrderLevel0Data`
and `Part3Residual.target`, with witness provenance in
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
private theorem point202slice0 : Part6Nat.slice 0 3570 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice1 : Part6Nat.slice 0 3570 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice2 : Part6Nat.slice 0 3570 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice3 : Part6Nat.slice 0 3570 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice4 : Part6Nat.slice 0 3570 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice5 : Part6Nat.slice 0 3570 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice6 : Part6Nat.slice 0 3570 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice7 : Part6Nat.slice 0 3570 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice8 : Part6Nat.slice 0 3570 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice9 : Part6Nat.slice 0 3570 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice10 : Part6Nat.slice 0 3570 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice11 : Part6Nat.slice 0 3570 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice12 : Part6Nat.slice 0 3570 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice13 : Part6Nat.slice 0 3570 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice14 : Part6Nat.slice 0 3570 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice15 : Part6Nat.slice 0 3570 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice16 : Part6Nat.slice 0 3570 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice17 : Part6Nat.slice 0 3570 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice18 : Part6Nat.slice 0 3570 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice19 : Part6Nat.slice 0 3570 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice20 : Part6Nat.slice 0 3570 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice21 : Part6Nat.slice 0 3570 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice22 : Part6Nat.slice 0 3570 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice23 : Part6Nat.slice 0 3570 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice24 : Part6Nat.slice 0 3570 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice25 : Part6Nat.slice 0 3570 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice26 : Part6Nat.slice 0 3570 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice27 : Part6Nat.slice 0 3570 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice28 : Part6Nat.slice 0 3570 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice29 : Part6Nat.slice 0 3570 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice30 : Part6Nat.slice 0 3570 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice31 : Part6Nat.slice 0 3570 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice32 : Part6Nat.slice 0 3570 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice33 : Part6Nat.slice 0 3570 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice34 : Part6Nat.slice 0 3570 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice35 : Part6Nat.slice 0 3570 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice36 : Part6Nat.slice 0 3570 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice37 : Part6Nat.slice 0 3570 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice38 : Part6Nat.slice 0 3570 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice39 : Part6Nat.slice 0 3570 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice40 : Part6Nat.slice 0 3570 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice41 : Part6Nat.slice 0 3570 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice42 : Part6Nat.slice 0 3570 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice43 : Part6Nat.slice 0 3570 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice44 : Part6Nat.slice 0 3570 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice45 : Part6Nat.slice 0 3570 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice46 : Part6Nat.slice 0 3570 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice47 : Part6Nat.slice 0 3570 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice48 : Part6Nat.slice 0 3570 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice49 : Part6Nat.slice 0 3570 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice50 : Part6Nat.slice 0 3570 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice51 : Part6Nat.slice 0 3570 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice52 : Part6Nat.slice 0 3570 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice53 : Part6Nat.slice 0 3570 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice54 : Part6Nat.slice 0 3570 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice55 : Part6Nat.slice 0 3570 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice56 : Part6Nat.slice 0 3570 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice57 : Part6Nat.slice 0 3570 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice58 : Part6Nat.slice 0 3570 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice59 : Part6Nat.slice 0 3570 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice60 : Part6Nat.slice 0 3570 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice61 : Part6Nat.slice 0 3570 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice62 : Part6Nat.slice 0 3570 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice63 : Part6Nat.slice 0 3570 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice64 : Part6Nat.slice 0 3570 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice65 : Part6Nat.slice 0 3570 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice66 : Part6Nat.slice 0 3570 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice67 : Part6Nat.slice 0 3570 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice68 : Part6Nat.slice 0 3570 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice69 : Part6Nat.slice 0 3570 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice70 : Part6Nat.slice 0 3570 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice71 : Part6Nat.slice 0 3570 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice72 : Part6Nat.slice 0 3570 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice73 : Part6Nat.slice 0 3570 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice74 : Part6Nat.slice 0 3570 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice75 : Part6Nat.slice 0 3570 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice76 : Part6Nat.slice 0 3570 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice77 : Part6Nat.slice 0 3570 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice78 : Part6Nat.slice 0 3570 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice79 : Part6Nat.slice 0 3570 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice80 : Part6Nat.slice 0 3570 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice81 : Part6Nat.slice 0 3570 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice82 : Part6Nat.slice 0 3570 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice83 : Part6Nat.slice 0 3570 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice84 : Part6Nat.slice 0 3570 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice85 : Part6Nat.slice 0 3570 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice86 : Part6Nat.slice 0 3570 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice87 : Part6Nat.slice 0 3570 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice88 : Part6Nat.slice 0 3570 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice89 : Part6Nat.slice 0 3570 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice90 : Part6Nat.slice 0 3570 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice91 : Part6Nat.slice 0 3570 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice92 : Part6Nat.slice 0 3570 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice93 : Part6Nat.slice 0 3570 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice94 : Part6Nat.slice 0 3570 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice95 : Part6Nat.slice 0 3570 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice96 : Part6Nat.slice 0 3570 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice97 : Part6Nat.slice 0 3570 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice98 : Part6Nat.slice 0 3570 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice99 : Part6Nat.slice 0 3570 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice100 : Part6Nat.slice 0 3570 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice101 : Part6Nat.slice 0 3570 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice102 : Part6Nat.slice 0 3570 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice103 : Part6Nat.slice 0 3570 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice104 : Part6Nat.slice 0 3570 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice105 : Part6Nat.slice 0 3570 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice106 : Part6Nat.slice 0 3570 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice107 : Part6Nat.slice 0 3570 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice108 : Part6Nat.slice 0 3570 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice109 : Part6Nat.slice 0 3570 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice110 : Part6Nat.slice 0 3570 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice111 : Part6Nat.slice 0 3570 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice112 : Part6Nat.slice 0 3570 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice113 : Part6Nat.slice 0 3570 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice114 : Part6Nat.slice 0 3570 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice115 : Part6Nat.slice 0 3570 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice116 : Part6Nat.slice 0 3570 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice117 : Part6Nat.slice 0 3570 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice118 : Part6Nat.slice 0 3570 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice119 : Part6Nat.slice 0 3570 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice120 : Part6Nat.slice 0 3570 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice121 : Part6Nat.slice 0 3570 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice122 : Part6Nat.slice 0 3570 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice123 : Part6Nat.slice 0 3570 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice124 : Part6Nat.slice 0 3570 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice125 : Part6Nat.slice 0 3570 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice126 : Part6Nat.slice 0 3570 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice127 : Part6Nat.slice 0 3570 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice128 : Part6Nat.slice 0 3570 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice129 : Part6Nat.slice 0 3570 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice130 : Part6Nat.slice 0 3570 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice131 : Part6Nat.slice 0 3570 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice132 : Part6Nat.slice 0 3570 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice133 : Part6Nat.slice 0 3570 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice134 : Part6Nat.slice 0 3570 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice135 : Part6Nat.slice 0 3570 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice136 : Part6Nat.slice 0 3570 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice137 : Part6Nat.slice 0 3570 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice138 : Part6Nat.slice 0 3570 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice139 : Part6Nat.slice 0 3570 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice140 : Part6Nat.slice 0 3570 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice141 : Part6Nat.slice 0 3570 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice142 : Part6Nat.slice 0 3570 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice143 : Part6Nat.slice 0 3570 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice144 : Part6Nat.slice 0 3570 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice145 : Part6Nat.slice 0 3570 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice146 : Part6Nat.slice 0 3570 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice147 : Part6Nat.slice 0 3570 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice148 : Part6Nat.slice 0 3570 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice149 : Part6Nat.slice 0 3570 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice150 : Part6Nat.slice 0 3570 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice151 : Part6Nat.slice 0 3570 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice152 : Part6Nat.slice 0 3570 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice153 : Part6Nat.slice 0 3570 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice154 : Part6Nat.slice 0 3570 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice155 : Part6Nat.slice 0 3570 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice156 : Part6Nat.slice 0 3570 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice157 : Part6Nat.slice 0 3570 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice158 : Part6Nat.slice 0 3570 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice159 : Part6Nat.slice 0 3570 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice160 : Part6Nat.slice 0 3570 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice161 : Part6Nat.slice 0 3570 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice162 : Part6Nat.slice 0 3570 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice163 : Part6Nat.slice 0 3570 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice164 : Part6Nat.slice 0 3570 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice165 : Part6Nat.slice 0 3570 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice166 : Part6Nat.slice 0 3570 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice167 : Part6Nat.slice 0 3570 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice168 : Part6Nat.slice 0 3570 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice169 : Part6Nat.slice 0 3570 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice170 : Part6Nat.slice 0 3570 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice171 : Part6Nat.slice 0 3570 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice172 : Part6Nat.slice 0 3570 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice173 : Part6Nat.slice 0 3570 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice174 : Part6Nat.slice 0 3570 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice175 : Part6Nat.slice 0 3570 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice176 : Part6Nat.slice 0 3570 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice177 : Part6Nat.slice 0 3570 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice178 : Part6Nat.slice 0 3570 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice179 : Part6Nat.slice 0 3570 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice180 : Part6Nat.slice 0 3570 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice181 : Part6Nat.slice 0 3570 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice182 : Part6Nat.slice 0 3570 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice183 : Part6Nat.slice 0 3570 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice184 : Part6Nat.slice 0 3570 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice185 : Part6Nat.slice 0 3570 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice186 : Part6Nat.slice 0 3570 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice187 : Part6Nat.slice 0 3570 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice188 : Part6Nat.slice 0 3570 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice189 : Part6Nat.slice 0 3570 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice190 : Part6Nat.slice 0 3570 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice191 : Part6Nat.slice 0 3570 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice192 : Part6Nat.slice 0 3570 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice193 : Part6Nat.slice 0 3570 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice194 : Part6Nat.slice 0 3570 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice195 : Part6Nat.slice 0 3570 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice196 : Part6Nat.slice 0 3570 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice197 : Part6Nat.slice 0 3570 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice198 : Part6Nat.slice 0 3570 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice199 : Part6Nat.slice 0 3570 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice200 : Part6Nat.slice 0 3570 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice201 : Part6Nat.slice 0 3570 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point202slice202 : Part6Nat.slice 0 3570 202 = true := by
  decide +kernel

public theorem point202 : stepCheck 0 3570 := by
  apply Part6Nat.ofSlices
  intro c
  fin_cases c
  · exact point202slice0
  · exact point202slice1
  · exact point202slice2
  · exact point202slice3
  · exact point202slice4
  · exact point202slice5
  · exact point202slice6
  · exact point202slice7
  · exact point202slice8
  · exact point202slice9
  · exact point202slice10
  · exact point202slice11
  · exact point202slice12
  · exact point202slice13
  · exact point202slice14
  · exact point202slice15
  · exact point202slice16
  · exact point202slice17
  · exact point202slice18
  · exact point202slice19
  · exact point202slice20
  · exact point202slice21
  · exact point202slice22
  · exact point202slice23
  · exact point202slice24
  · exact point202slice25
  · exact point202slice26
  · exact point202slice27
  · exact point202slice28
  · exact point202slice29
  · exact point202slice30
  · exact point202slice31
  · exact point202slice32
  · exact point202slice33
  · exact point202slice34
  · exact point202slice35
  · exact point202slice36
  · exact point202slice37
  · exact point202slice38
  · exact point202slice39
  · exact point202slice40
  · exact point202slice41
  · exact point202slice42
  · exact point202slice43
  · exact point202slice44
  · exact point202slice45
  · exact point202slice46
  · exact point202slice47
  · exact point202slice48
  · exact point202slice49
  · exact point202slice50
  · exact point202slice51
  · exact point202slice52
  · exact point202slice53
  · exact point202slice54
  · exact point202slice55
  · exact point202slice56
  · exact point202slice57
  · exact point202slice58
  · exact point202slice59
  · exact point202slice60
  · exact point202slice61
  · exact point202slice62
  · exact point202slice63
  · exact point202slice64
  · exact point202slice65
  · exact point202slice66
  · exact point202slice67
  · exact point202slice68
  · exact point202slice69
  · exact point202slice70
  · exact point202slice71
  · exact point202slice72
  · exact point202slice73
  · exact point202slice74
  · exact point202slice75
  · exact point202slice76
  · exact point202slice77
  · exact point202slice78
  · exact point202slice79
  · exact point202slice80
  · exact point202slice81
  · exact point202slice82
  · exact point202slice83
  · exact point202slice84
  · exact point202slice85
  · exact point202slice86
  · exact point202slice87
  · exact point202slice88
  · exact point202slice89
  · exact point202slice90
  · exact point202slice91
  · exact point202slice92
  · exact point202slice93
  · exact point202slice94
  · exact point202slice95
  · exact point202slice96
  · exact point202slice97
  · exact point202slice98
  · exact point202slice99
  · exact point202slice100
  · exact point202slice101
  · exact point202slice102
  · exact point202slice103
  · exact point202slice104
  · exact point202slice105
  · exact point202slice106
  · exact point202slice107
  · exact point202slice108
  · exact point202slice109
  · exact point202slice110
  · exact point202slice111
  · exact point202slice112
  · exact point202slice113
  · exact point202slice114
  · exact point202slice115
  · exact point202slice116
  · exact point202slice117
  · exact point202slice118
  · exact point202slice119
  · exact point202slice120
  · exact point202slice121
  · exact point202slice122
  · exact point202slice123
  · exact point202slice124
  · exact point202slice125
  · exact point202slice126
  · exact point202slice127
  · exact point202slice128
  · exact point202slice129
  · exact point202slice130
  · exact point202slice131
  · exact point202slice132
  · exact point202slice133
  · exact point202slice134
  · exact point202slice135
  · exact point202slice136
  · exact point202slice137
  · exact point202slice138
  · exact point202slice139
  · exact point202slice140
  · exact point202slice141
  · exact point202slice142
  · exact point202slice143
  · exact point202slice144
  · exact point202slice145
  · exact point202slice146
  · exact point202slice147
  · exact point202slice148
  · exact point202slice149
  · exact point202slice150
  · exact point202slice151
  · exact point202slice152
  · exact point202slice153
  · exact point202slice154
  · exact point202slice155
  · exact point202slice156
  · exact point202slice157
  · exact point202slice158
  · exact point202slice159
  · exact point202slice160
  · exact point202slice161
  · exact point202slice162
  · exact point202slice163
  · exact point202slice164
  · exact point202slice165
  · exact point202slice166
  · exact point202slice167
  · exact point202slice168
  · exact point202slice169
  · exact point202slice170
  · exact point202slice171
  · exact point202slice172
  · exact point202slice173
  · exact point202slice174
  · exact point202slice175
  · exact point202slice176
  · exact point202slice177
  · exact point202slice178
  · exact point202slice179
  · exact point202slice180
  · exact point202slice181
  · exact point202slice182
  · exact point202slice183
  · exact point202slice184
  · exact point202slice185
  · exact point202slice186
  · exact point202slice187
  · exact point202slice188
  · exact point202slice189
  · exact point202slice190
  · exact point202slice191
  · exact point202slice192
  · exact point202slice193
  · exact point202slice194
  · exact point202slice195
  · exact point202slice196
  · exact point202slice197
  · exact point202slice198
  · exact point202slice199
  · exact point202slice200
  · exact point202slice201
  · exact point202slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
