module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part1
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 139

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap139 (x : Nat) : Nat := force t275 (t547 x)
private def leftPerm139 : Equiv.Perm (Fin 4060) := p275 * (p547)
private theorem leftMap139_eq (x : Fin 4060) :
    leftMap139 x.val = (leftPerm139 x).val := (compose (t := fun x => force t275 (t547 x)) (a := t275) (b := fun x => t547 x) (fun _ => rfl) c275 c547) x

private def rightMap139 (x : Nat) : Nat := force t137 (t234 x)
private def rightPerm139 : Equiv.Perm (Fin 4060) := p137 * (p234)
private theorem rightMap139_eq (x : Fin 4060) :
    rightMap139 x.val = (rightPerm139 x).val := (compose (t := fun x => force t137 (t234 x)) (a := t137) (b := fun x => t234 x) (fun _ => rfl) c137 c234) x

set_option maxHeartbeats 1600000 in
private theorem point139slice0 : Residual1Cache.slice leftMap139 rightMap139 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice1 : Residual1Cache.slice leftMap139 rightMap139 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice2 : Residual1Cache.slice leftMap139 rightMap139 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice3 : Residual1Cache.slice leftMap139 rightMap139 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice4 : Residual1Cache.slice leftMap139 rightMap139 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice5 : Residual1Cache.slice leftMap139 rightMap139 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice6 : Residual1Cache.slice leftMap139 rightMap139 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice7 : Residual1Cache.slice leftMap139 rightMap139 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice8 : Residual1Cache.slice leftMap139 rightMap139 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice9 : Residual1Cache.slice leftMap139 rightMap139 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice10 : Residual1Cache.slice leftMap139 rightMap139 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice11 : Residual1Cache.slice leftMap139 rightMap139 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice12 : Residual1Cache.slice leftMap139 rightMap139 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice13 : Residual1Cache.slice leftMap139 rightMap139 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice14 : Residual1Cache.slice leftMap139 rightMap139 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice15 : Residual1Cache.slice leftMap139 rightMap139 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice16 : Residual1Cache.slice leftMap139 rightMap139 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice17 : Residual1Cache.slice leftMap139 rightMap139 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice18 : Residual1Cache.slice leftMap139 rightMap139 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice19 : Residual1Cache.slice leftMap139 rightMap139 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice20 : Residual1Cache.slice leftMap139 rightMap139 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice21 : Residual1Cache.slice leftMap139 rightMap139 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice22 : Residual1Cache.slice leftMap139 rightMap139 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice23 : Residual1Cache.slice leftMap139 rightMap139 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice24 : Residual1Cache.slice leftMap139 rightMap139 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice25 : Residual1Cache.slice leftMap139 rightMap139 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice26 : Residual1Cache.slice leftMap139 rightMap139 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice27 : Residual1Cache.slice leftMap139 rightMap139 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice28 : Residual1Cache.slice leftMap139 rightMap139 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice29 : Residual1Cache.slice leftMap139 rightMap139 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice30 : Residual1Cache.slice leftMap139 rightMap139 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice31 : Residual1Cache.slice leftMap139 rightMap139 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice32 : Residual1Cache.slice leftMap139 rightMap139 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice33 : Residual1Cache.slice leftMap139 rightMap139 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice34 : Residual1Cache.slice leftMap139 rightMap139 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice35 : Residual1Cache.slice leftMap139 rightMap139 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice36 : Residual1Cache.slice leftMap139 rightMap139 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice37 : Residual1Cache.slice leftMap139 rightMap139 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice38 : Residual1Cache.slice leftMap139 rightMap139 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice39 : Residual1Cache.slice leftMap139 rightMap139 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice40 : Residual1Cache.slice leftMap139 rightMap139 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice41 : Residual1Cache.slice leftMap139 rightMap139 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice42 : Residual1Cache.slice leftMap139 rightMap139 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice43 : Residual1Cache.slice leftMap139 rightMap139 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice44 : Residual1Cache.slice leftMap139 rightMap139 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice45 : Residual1Cache.slice leftMap139 rightMap139 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice46 : Residual1Cache.slice leftMap139 rightMap139 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice47 : Residual1Cache.slice leftMap139 rightMap139 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice48 : Residual1Cache.slice leftMap139 rightMap139 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice49 : Residual1Cache.slice leftMap139 rightMap139 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice50 : Residual1Cache.slice leftMap139 rightMap139 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice51 : Residual1Cache.slice leftMap139 rightMap139 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice52 : Residual1Cache.slice leftMap139 rightMap139 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice53 : Residual1Cache.slice leftMap139 rightMap139 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice54 : Residual1Cache.slice leftMap139 rightMap139 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice55 : Residual1Cache.slice leftMap139 rightMap139 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice56 : Residual1Cache.slice leftMap139 rightMap139 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice57 : Residual1Cache.slice leftMap139 rightMap139 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice58 : Residual1Cache.slice leftMap139 rightMap139 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice59 : Residual1Cache.slice leftMap139 rightMap139 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice60 : Residual1Cache.slice leftMap139 rightMap139 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice61 : Residual1Cache.slice leftMap139 rightMap139 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice62 : Residual1Cache.slice leftMap139 rightMap139 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice63 : Residual1Cache.slice leftMap139 rightMap139 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice64 : Residual1Cache.slice leftMap139 rightMap139 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice65 : Residual1Cache.slice leftMap139 rightMap139 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice66 : Residual1Cache.slice leftMap139 rightMap139 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice67 : Residual1Cache.slice leftMap139 rightMap139 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice68 : Residual1Cache.slice leftMap139 rightMap139 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice69 : Residual1Cache.slice leftMap139 rightMap139 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice70 : Residual1Cache.slice leftMap139 rightMap139 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice71 : Residual1Cache.slice leftMap139 rightMap139 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice72 : Residual1Cache.slice leftMap139 rightMap139 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice73 : Residual1Cache.slice leftMap139 rightMap139 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice74 : Residual1Cache.slice leftMap139 rightMap139 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice75 : Residual1Cache.slice leftMap139 rightMap139 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice76 : Residual1Cache.slice leftMap139 rightMap139 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice77 : Residual1Cache.slice leftMap139 rightMap139 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice78 : Residual1Cache.slice leftMap139 rightMap139 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice79 : Residual1Cache.slice leftMap139 rightMap139 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice80 : Residual1Cache.slice leftMap139 rightMap139 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice81 : Residual1Cache.slice leftMap139 rightMap139 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice82 : Residual1Cache.slice leftMap139 rightMap139 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice83 : Residual1Cache.slice leftMap139 rightMap139 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice84 : Residual1Cache.slice leftMap139 rightMap139 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice85 : Residual1Cache.slice leftMap139 rightMap139 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice86 : Residual1Cache.slice leftMap139 rightMap139 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice87 : Residual1Cache.slice leftMap139 rightMap139 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice88 : Residual1Cache.slice leftMap139 rightMap139 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice89 : Residual1Cache.slice leftMap139 rightMap139 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice90 : Residual1Cache.slice leftMap139 rightMap139 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice91 : Residual1Cache.slice leftMap139 rightMap139 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice92 : Residual1Cache.slice leftMap139 rightMap139 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice93 : Residual1Cache.slice leftMap139 rightMap139 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice94 : Residual1Cache.slice leftMap139 rightMap139 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice95 : Residual1Cache.slice leftMap139 rightMap139 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice96 : Residual1Cache.slice leftMap139 rightMap139 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice97 : Residual1Cache.slice leftMap139 rightMap139 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice98 : Residual1Cache.slice leftMap139 rightMap139 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice99 : Residual1Cache.slice leftMap139 rightMap139 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice100 : Residual1Cache.slice leftMap139 rightMap139 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice101 : Residual1Cache.slice leftMap139 rightMap139 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice102 : Residual1Cache.slice leftMap139 rightMap139 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice103 : Residual1Cache.slice leftMap139 rightMap139 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice104 : Residual1Cache.slice leftMap139 rightMap139 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice105 : Residual1Cache.slice leftMap139 rightMap139 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice106 : Residual1Cache.slice leftMap139 rightMap139 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice107 : Residual1Cache.slice leftMap139 rightMap139 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice108 : Residual1Cache.slice leftMap139 rightMap139 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice109 : Residual1Cache.slice leftMap139 rightMap139 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice110 : Residual1Cache.slice leftMap139 rightMap139 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice111 : Residual1Cache.slice leftMap139 rightMap139 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice112 : Residual1Cache.slice leftMap139 rightMap139 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice113 : Residual1Cache.slice leftMap139 rightMap139 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice114 : Residual1Cache.slice leftMap139 rightMap139 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice115 : Residual1Cache.slice leftMap139 rightMap139 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice116 : Residual1Cache.slice leftMap139 rightMap139 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice117 : Residual1Cache.slice leftMap139 rightMap139 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice118 : Residual1Cache.slice leftMap139 rightMap139 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice119 : Residual1Cache.slice leftMap139 rightMap139 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice120 : Residual1Cache.slice leftMap139 rightMap139 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice121 : Residual1Cache.slice leftMap139 rightMap139 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice122 : Residual1Cache.slice leftMap139 rightMap139 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice123 : Residual1Cache.slice leftMap139 rightMap139 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice124 : Residual1Cache.slice leftMap139 rightMap139 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice125 : Residual1Cache.slice leftMap139 rightMap139 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice126 : Residual1Cache.slice leftMap139 rightMap139 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice127 : Residual1Cache.slice leftMap139 rightMap139 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice128 : Residual1Cache.slice leftMap139 rightMap139 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice129 : Residual1Cache.slice leftMap139 rightMap139 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice130 : Residual1Cache.slice leftMap139 rightMap139 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice131 : Residual1Cache.slice leftMap139 rightMap139 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice132 : Residual1Cache.slice leftMap139 rightMap139 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice133 : Residual1Cache.slice leftMap139 rightMap139 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice134 : Residual1Cache.slice leftMap139 rightMap139 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice135 : Residual1Cache.slice leftMap139 rightMap139 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice136 : Residual1Cache.slice leftMap139 rightMap139 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice137 : Residual1Cache.slice leftMap139 rightMap139 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice138 : Residual1Cache.slice leftMap139 rightMap139 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice139 : Residual1Cache.slice leftMap139 rightMap139 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice140 : Residual1Cache.slice leftMap139 rightMap139 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice141 : Residual1Cache.slice leftMap139 rightMap139 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice142 : Residual1Cache.slice leftMap139 rightMap139 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice143 : Residual1Cache.slice leftMap139 rightMap139 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice144 : Residual1Cache.slice leftMap139 rightMap139 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice145 : Residual1Cache.slice leftMap139 rightMap139 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice146 : Residual1Cache.slice leftMap139 rightMap139 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice147 : Residual1Cache.slice leftMap139 rightMap139 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice148 : Residual1Cache.slice leftMap139 rightMap139 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice149 : Residual1Cache.slice leftMap139 rightMap139 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice150 : Residual1Cache.slice leftMap139 rightMap139 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice151 : Residual1Cache.slice leftMap139 rightMap139 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice152 : Residual1Cache.slice leftMap139 rightMap139 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice153 : Residual1Cache.slice leftMap139 rightMap139 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice154 : Residual1Cache.slice leftMap139 rightMap139 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice155 : Residual1Cache.slice leftMap139 rightMap139 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice156 : Residual1Cache.slice leftMap139 rightMap139 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice157 : Residual1Cache.slice leftMap139 rightMap139 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice158 : Residual1Cache.slice leftMap139 rightMap139 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice159 : Residual1Cache.slice leftMap139 rightMap139 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice160 : Residual1Cache.slice leftMap139 rightMap139 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice161 : Residual1Cache.slice leftMap139 rightMap139 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice162 : Residual1Cache.slice leftMap139 rightMap139 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice163 : Residual1Cache.slice leftMap139 rightMap139 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice164 : Residual1Cache.slice leftMap139 rightMap139 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice165 : Residual1Cache.slice leftMap139 rightMap139 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice166 : Residual1Cache.slice leftMap139 rightMap139 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice167 : Residual1Cache.slice leftMap139 rightMap139 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice168 : Residual1Cache.slice leftMap139 rightMap139 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice169 : Residual1Cache.slice leftMap139 rightMap139 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice170 : Residual1Cache.slice leftMap139 rightMap139 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice171 : Residual1Cache.slice leftMap139 rightMap139 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice172 : Residual1Cache.slice leftMap139 rightMap139 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice173 : Residual1Cache.slice leftMap139 rightMap139 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice174 : Residual1Cache.slice leftMap139 rightMap139 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice175 : Residual1Cache.slice leftMap139 rightMap139 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice176 : Residual1Cache.slice leftMap139 rightMap139 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice177 : Residual1Cache.slice leftMap139 rightMap139 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice178 : Residual1Cache.slice leftMap139 rightMap139 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice179 : Residual1Cache.slice leftMap139 rightMap139 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice180 : Residual1Cache.slice leftMap139 rightMap139 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice181 : Residual1Cache.slice leftMap139 rightMap139 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice182 : Residual1Cache.slice leftMap139 rightMap139 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice183 : Residual1Cache.slice leftMap139 rightMap139 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice184 : Residual1Cache.slice leftMap139 rightMap139 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice185 : Residual1Cache.slice leftMap139 rightMap139 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice186 : Residual1Cache.slice leftMap139 rightMap139 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice187 : Residual1Cache.slice leftMap139 rightMap139 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice188 : Residual1Cache.slice leftMap139 rightMap139 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice189 : Residual1Cache.slice leftMap139 rightMap139 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice190 : Residual1Cache.slice leftMap139 rightMap139 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice191 : Residual1Cache.slice leftMap139 rightMap139 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice192 : Residual1Cache.slice leftMap139 rightMap139 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice193 : Residual1Cache.slice leftMap139 rightMap139 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice194 : Residual1Cache.slice leftMap139 rightMap139 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice195 : Residual1Cache.slice leftMap139 rightMap139 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice196 : Residual1Cache.slice leftMap139 rightMap139 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice197 : Residual1Cache.slice leftMap139 rightMap139 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice198 : Residual1Cache.slice leftMap139 rightMap139 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice199 : Residual1Cache.slice leftMap139 rightMap139 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice200 : Residual1Cache.slice leftMap139 rightMap139 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice201 : Residual1Cache.slice leftMap139 rightMap139 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point139slice202 : Residual1Cache.slice leftMap139 rightMap139 202 = true := by
  decide +kernel

private theorem point139_slices : ∀ c, Residual1Cache.slice leftMap139 rightMap139 c = true := by
  intro c
  fin_cases c
  · exact point139slice0
  · exact point139slice1
  · exact point139slice2
  · exact point139slice3
  · exact point139slice4
  · exact point139slice5
  · exact point139slice6
  · exact point139slice7
  · exact point139slice8
  · exact point139slice9
  · exact point139slice10
  · exact point139slice11
  · exact point139slice12
  · exact point139slice13
  · exact point139slice14
  · exact point139slice15
  · exact point139slice16
  · exact point139slice17
  · exact point139slice18
  · exact point139slice19
  · exact point139slice20
  · exact point139slice21
  · exact point139slice22
  · exact point139slice23
  · exact point139slice24
  · exact point139slice25
  · exact point139slice26
  · exact point139slice27
  · exact point139slice28
  · exact point139slice29
  · exact point139slice30
  · exact point139slice31
  · exact point139slice32
  · exact point139slice33
  · exact point139slice34
  · exact point139slice35
  · exact point139slice36
  · exact point139slice37
  · exact point139slice38
  · exact point139slice39
  · exact point139slice40
  · exact point139slice41
  · exact point139slice42
  · exact point139slice43
  · exact point139slice44
  · exact point139slice45
  · exact point139slice46
  · exact point139slice47
  · exact point139slice48
  · exact point139slice49
  · exact point139slice50
  · exact point139slice51
  · exact point139slice52
  · exact point139slice53
  · exact point139slice54
  · exact point139slice55
  · exact point139slice56
  · exact point139slice57
  · exact point139slice58
  · exact point139slice59
  · exact point139slice60
  · exact point139slice61
  · exact point139slice62
  · exact point139slice63
  · exact point139slice64
  · exact point139slice65
  · exact point139slice66
  · exact point139slice67
  · exact point139slice68
  · exact point139slice69
  · exact point139slice70
  · exact point139slice71
  · exact point139slice72
  · exact point139slice73
  · exact point139slice74
  · exact point139slice75
  · exact point139slice76
  · exact point139slice77
  · exact point139slice78
  · exact point139slice79
  · exact point139slice80
  · exact point139slice81
  · exact point139slice82
  · exact point139slice83
  · exact point139slice84
  · exact point139slice85
  · exact point139slice86
  · exact point139slice87
  · exact point139slice88
  · exact point139slice89
  · exact point139slice90
  · exact point139slice91
  · exact point139slice92
  · exact point139slice93
  · exact point139slice94
  · exact point139slice95
  · exact point139slice96
  · exact point139slice97
  · exact point139slice98
  · exact point139slice99
  · exact point139slice100
  · exact point139slice101
  · exact point139slice102
  · exact point139slice103
  · exact point139slice104
  · exact point139slice105
  · exact point139slice106
  · exact point139slice107
  · exact point139slice108
  · exact point139slice109
  · exact point139slice110
  · exact point139slice111
  · exact point139slice112
  · exact point139slice113
  · exact point139slice114
  · exact point139slice115
  · exact point139slice116
  · exact point139slice117
  · exact point139slice118
  · exact point139slice119
  · exact point139slice120
  · exact point139slice121
  · exact point139slice122
  · exact point139slice123
  · exact point139slice124
  · exact point139slice125
  · exact point139slice126
  · exact point139slice127
  · exact point139slice128
  · exact point139slice129
  · exact point139slice130
  · exact point139slice131
  · exact point139slice132
  · exact point139slice133
  · exact point139slice134
  · exact point139slice135
  · exact point139slice136
  · exact point139slice137
  · exact point139slice138
  · exact point139slice139
  · exact point139slice140
  · exact point139slice141
  · exact point139slice142
  · exact point139slice143
  · exact point139slice144
  · exact point139slice145
  · exact point139slice146
  · exact point139slice147
  · exact point139slice148
  · exact point139slice149
  · exact point139slice150
  · exact point139slice151
  · exact point139slice152
  · exact point139slice153
  · exact point139slice154
  · exact point139slice155
  · exact point139slice156
  · exact point139slice157
  · exact point139slice158
  · exact point139slice159
  · exact point139slice160
  · exact point139slice161
  · exact point139slice162
  · exact point139slice163
  · exact point139slice164
  · exact point139slice165
  · exact point139slice166
  · exact point139slice167
  · exact point139slice168
  · exact point139slice169
  · exact point139slice170
  · exact point139slice171
  · exact point139slice172
  · exact point139slice173
  · exact point139slice174
  · exact point139slice175
  · exact point139slice176
  · exact point139slice177
  · exact point139slice178
  · exact point139slice179
  · exact point139slice180
  · exact point139slice181
  · exact point139slice182
  · exact point139slice183
  · exact point139slice184
  · exact point139slice185
  · exact point139slice186
  · exact point139slice187
  · exact point139slice188
  · exact point139slice189
  · exact point139slice190
  · exact point139slice191
  · exact point139slice192
  · exact point139slice193
  · exact point139slice194
  · exact point139slice195
  · exact point139slice196
  · exact point139slice197
  · exact point139slice198
  · exact point139slice199
  · exact point139slice200
  · exact point139slice201
  · exact point139slice202

set_option maxHeartbeats 1600000 in
public theorem point139 : stepCheck 0 2847 := by
  have hleft : L0Gen 0 * L0Rep 2847 = leftPerm139 := by
    change L0Gen 0 * evalWord L0Gen [1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0] = leftPerm139
    simp only [leftPerm139, p547, p275, p67, p53, p47, p27, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2847) * evalWord L1Gen (L0Factor 0 2847) = rightPerm139 := by
    change evalWord L0Gen [1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 1, 0] * evalWord L1Gen [] = rightPerm139
    simp only [rightPerm139, p234, p137, p59, p47, p27, p20, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2847) x =
    (L0Rep (L0Act 0 2847) * evalWord L1Gen (L0Factor 0 2847)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap139_eq, ← rightMap139_eq]
  exact Residual1Cache.ofSlices point139_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
