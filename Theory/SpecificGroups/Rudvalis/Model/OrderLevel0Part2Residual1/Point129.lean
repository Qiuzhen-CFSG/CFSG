module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level13Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 129

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap129 (x : Nat) : Nat := force t67 (force t140 (force t67 (t153 x)))
private def leftPerm129 : Equiv.Perm (Fin 4060) := p67 * (p140 * (p67 * (p153)))
private theorem leftMap129_eq (x : Fin 4060) :
    leftMap129 x.val = (leftPerm129 x).val := (compose (t := fun x => force t67 (force t140 (force t67 (t153 x)))) (a := t67) (b := fun x => force t140 (force t67 (t153 x))) (fun _ => rfl) c67 (compose (t := fun x => force t140 (force t67 (t153 x))) (a := t140) (b := fun x => force t67 (t153 x)) (fun _ => rfl) c140 (compose (t := fun x => force t67 (t153 x)) (a := t67) (b := fun x => t153 x) (fun _ => rfl) c67 c153))) x

private def rightMap129 (x : Nat) : Nat := force t277 (force t283 (force t196 (force t94 (force t147 (t321 x)))))
private def rightPerm129 : Equiv.Perm (Fin 4060) := p277 * (p283 * (p196 * (p94 * (p147 * (p321)))))
private theorem rightMap129_eq (x : Fin 4060) :
    rightMap129 x.val = (rightPerm129 x).val := (compose (t := fun x => force t277 (force t283 (force t196 (force t94 (force t147 (t321 x)))))) (a := t277) (b := fun x => force t283 (force t196 (force t94 (force t147 (t321 x))))) (fun _ => rfl) c277 (compose (t := fun x => force t283 (force t196 (force t94 (force t147 (t321 x))))) (a := t283) (b := fun x => force t196 (force t94 (force t147 (t321 x)))) (fun _ => rfl) c283 (compose (t := fun x => force t196 (force t94 (force t147 (t321 x)))) (a := t196) (b := fun x => force t94 (force t147 (t321 x))) (fun _ => rfl) c196 (compose (t := fun x => force t94 (force t147 (t321 x))) (a := t94) (b := fun x => force t147 (t321 x)) (fun _ => rfl) c94 (compose (t := fun x => force t147 (t321 x)) (a := t147) (b := fun x => t321 x) (fun _ => rfl) c147 c321))))) x

set_option maxHeartbeats 1600000 in
private theorem point129slice0 : Residual1Cache.slice leftMap129 rightMap129 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice1 : Residual1Cache.slice leftMap129 rightMap129 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice2 : Residual1Cache.slice leftMap129 rightMap129 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice3 : Residual1Cache.slice leftMap129 rightMap129 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice4 : Residual1Cache.slice leftMap129 rightMap129 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice5 : Residual1Cache.slice leftMap129 rightMap129 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice6 : Residual1Cache.slice leftMap129 rightMap129 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice7 : Residual1Cache.slice leftMap129 rightMap129 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice8 : Residual1Cache.slice leftMap129 rightMap129 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice9 : Residual1Cache.slice leftMap129 rightMap129 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice10 : Residual1Cache.slice leftMap129 rightMap129 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice11 : Residual1Cache.slice leftMap129 rightMap129 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice12 : Residual1Cache.slice leftMap129 rightMap129 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice13 : Residual1Cache.slice leftMap129 rightMap129 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice14 : Residual1Cache.slice leftMap129 rightMap129 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice15 : Residual1Cache.slice leftMap129 rightMap129 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice16 : Residual1Cache.slice leftMap129 rightMap129 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice17 : Residual1Cache.slice leftMap129 rightMap129 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice18 : Residual1Cache.slice leftMap129 rightMap129 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice19 : Residual1Cache.slice leftMap129 rightMap129 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice20 : Residual1Cache.slice leftMap129 rightMap129 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice21 : Residual1Cache.slice leftMap129 rightMap129 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice22 : Residual1Cache.slice leftMap129 rightMap129 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice23 : Residual1Cache.slice leftMap129 rightMap129 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice24 : Residual1Cache.slice leftMap129 rightMap129 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice25 : Residual1Cache.slice leftMap129 rightMap129 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice26 : Residual1Cache.slice leftMap129 rightMap129 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice27 : Residual1Cache.slice leftMap129 rightMap129 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice28 : Residual1Cache.slice leftMap129 rightMap129 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice29 : Residual1Cache.slice leftMap129 rightMap129 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice30 : Residual1Cache.slice leftMap129 rightMap129 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice31 : Residual1Cache.slice leftMap129 rightMap129 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice32 : Residual1Cache.slice leftMap129 rightMap129 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice33 : Residual1Cache.slice leftMap129 rightMap129 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice34 : Residual1Cache.slice leftMap129 rightMap129 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice35 : Residual1Cache.slice leftMap129 rightMap129 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice36 : Residual1Cache.slice leftMap129 rightMap129 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice37 : Residual1Cache.slice leftMap129 rightMap129 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice38 : Residual1Cache.slice leftMap129 rightMap129 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice39 : Residual1Cache.slice leftMap129 rightMap129 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice40 : Residual1Cache.slice leftMap129 rightMap129 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice41 : Residual1Cache.slice leftMap129 rightMap129 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice42 : Residual1Cache.slice leftMap129 rightMap129 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice43 : Residual1Cache.slice leftMap129 rightMap129 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice44 : Residual1Cache.slice leftMap129 rightMap129 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice45 : Residual1Cache.slice leftMap129 rightMap129 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice46 : Residual1Cache.slice leftMap129 rightMap129 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice47 : Residual1Cache.slice leftMap129 rightMap129 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice48 : Residual1Cache.slice leftMap129 rightMap129 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice49 : Residual1Cache.slice leftMap129 rightMap129 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice50 : Residual1Cache.slice leftMap129 rightMap129 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice51 : Residual1Cache.slice leftMap129 rightMap129 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice52 : Residual1Cache.slice leftMap129 rightMap129 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice53 : Residual1Cache.slice leftMap129 rightMap129 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice54 : Residual1Cache.slice leftMap129 rightMap129 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice55 : Residual1Cache.slice leftMap129 rightMap129 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice56 : Residual1Cache.slice leftMap129 rightMap129 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice57 : Residual1Cache.slice leftMap129 rightMap129 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice58 : Residual1Cache.slice leftMap129 rightMap129 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice59 : Residual1Cache.slice leftMap129 rightMap129 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice60 : Residual1Cache.slice leftMap129 rightMap129 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice61 : Residual1Cache.slice leftMap129 rightMap129 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice62 : Residual1Cache.slice leftMap129 rightMap129 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice63 : Residual1Cache.slice leftMap129 rightMap129 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice64 : Residual1Cache.slice leftMap129 rightMap129 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice65 : Residual1Cache.slice leftMap129 rightMap129 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice66 : Residual1Cache.slice leftMap129 rightMap129 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice67 : Residual1Cache.slice leftMap129 rightMap129 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice68 : Residual1Cache.slice leftMap129 rightMap129 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice69 : Residual1Cache.slice leftMap129 rightMap129 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice70 : Residual1Cache.slice leftMap129 rightMap129 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice71 : Residual1Cache.slice leftMap129 rightMap129 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice72 : Residual1Cache.slice leftMap129 rightMap129 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice73 : Residual1Cache.slice leftMap129 rightMap129 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice74 : Residual1Cache.slice leftMap129 rightMap129 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice75 : Residual1Cache.slice leftMap129 rightMap129 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice76 : Residual1Cache.slice leftMap129 rightMap129 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice77 : Residual1Cache.slice leftMap129 rightMap129 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice78 : Residual1Cache.slice leftMap129 rightMap129 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice79 : Residual1Cache.slice leftMap129 rightMap129 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice80 : Residual1Cache.slice leftMap129 rightMap129 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice81 : Residual1Cache.slice leftMap129 rightMap129 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice82 : Residual1Cache.slice leftMap129 rightMap129 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice83 : Residual1Cache.slice leftMap129 rightMap129 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice84 : Residual1Cache.slice leftMap129 rightMap129 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice85 : Residual1Cache.slice leftMap129 rightMap129 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice86 : Residual1Cache.slice leftMap129 rightMap129 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice87 : Residual1Cache.slice leftMap129 rightMap129 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice88 : Residual1Cache.slice leftMap129 rightMap129 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice89 : Residual1Cache.slice leftMap129 rightMap129 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice90 : Residual1Cache.slice leftMap129 rightMap129 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice91 : Residual1Cache.slice leftMap129 rightMap129 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice92 : Residual1Cache.slice leftMap129 rightMap129 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice93 : Residual1Cache.slice leftMap129 rightMap129 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice94 : Residual1Cache.slice leftMap129 rightMap129 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice95 : Residual1Cache.slice leftMap129 rightMap129 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice96 : Residual1Cache.slice leftMap129 rightMap129 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice97 : Residual1Cache.slice leftMap129 rightMap129 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice98 : Residual1Cache.slice leftMap129 rightMap129 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice99 : Residual1Cache.slice leftMap129 rightMap129 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice100 : Residual1Cache.slice leftMap129 rightMap129 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice101 : Residual1Cache.slice leftMap129 rightMap129 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice102 : Residual1Cache.slice leftMap129 rightMap129 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice103 : Residual1Cache.slice leftMap129 rightMap129 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice104 : Residual1Cache.slice leftMap129 rightMap129 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice105 : Residual1Cache.slice leftMap129 rightMap129 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice106 : Residual1Cache.slice leftMap129 rightMap129 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice107 : Residual1Cache.slice leftMap129 rightMap129 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice108 : Residual1Cache.slice leftMap129 rightMap129 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice109 : Residual1Cache.slice leftMap129 rightMap129 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice110 : Residual1Cache.slice leftMap129 rightMap129 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice111 : Residual1Cache.slice leftMap129 rightMap129 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice112 : Residual1Cache.slice leftMap129 rightMap129 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice113 : Residual1Cache.slice leftMap129 rightMap129 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice114 : Residual1Cache.slice leftMap129 rightMap129 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice115 : Residual1Cache.slice leftMap129 rightMap129 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice116 : Residual1Cache.slice leftMap129 rightMap129 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice117 : Residual1Cache.slice leftMap129 rightMap129 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice118 : Residual1Cache.slice leftMap129 rightMap129 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice119 : Residual1Cache.slice leftMap129 rightMap129 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice120 : Residual1Cache.slice leftMap129 rightMap129 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice121 : Residual1Cache.slice leftMap129 rightMap129 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice122 : Residual1Cache.slice leftMap129 rightMap129 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice123 : Residual1Cache.slice leftMap129 rightMap129 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice124 : Residual1Cache.slice leftMap129 rightMap129 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice125 : Residual1Cache.slice leftMap129 rightMap129 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice126 : Residual1Cache.slice leftMap129 rightMap129 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice127 : Residual1Cache.slice leftMap129 rightMap129 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice128 : Residual1Cache.slice leftMap129 rightMap129 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice129 : Residual1Cache.slice leftMap129 rightMap129 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice130 : Residual1Cache.slice leftMap129 rightMap129 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice131 : Residual1Cache.slice leftMap129 rightMap129 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice132 : Residual1Cache.slice leftMap129 rightMap129 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice133 : Residual1Cache.slice leftMap129 rightMap129 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice134 : Residual1Cache.slice leftMap129 rightMap129 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice135 : Residual1Cache.slice leftMap129 rightMap129 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice136 : Residual1Cache.slice leftMap129 rightMap129 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice137 : Residual1Cache.slice leftMap129 rightMap129 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice138 : Residual1Cache.slice leftMap129 rightMap129 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice139 : Residual1Cache.slice leftMap129 rightMap129 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice140 : Residual1Cache.slice leftMap129 rightMap129 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice141 : Residual1Cache.slice leftMap129 rightMap129 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice142 : Residual1Cache.slice leftMap129 rightMap129 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice143 : Residual1Cache.slice leftMap129 rightMap129 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice144 : Residual1Cache.slice leftMap129 rightMap129 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice145 : Residual1Cache.slice leftMap129 rightMap129 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice146 : Residual1Cache.slice leftMap129 rightMap129 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice147 : Residual1Cache.slice leftMap129 rightMap129 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice148 : Residual1Cache.slice leftMap129 rightMap129 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice149 : Residual1Cache.slice leftMap129 rightMap129 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice150 : Residual1Cache.slice leftMap129 rightMap129 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice151 : Residual1Cache.slice leftMap129 rightMap129 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice152 : Residual1Cache.slice leftMap129 rightMap129 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice153 : Residual1Cache.slice leftMap129 rightMap129 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice154 : Residual1Cache.slice leftMap129 rightMap129 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice155 : Residual1Cache.slice leftMap129 rightMap129 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice156 : Residual1Cache.slice leftMap129 rightMap129 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice157 : Residual1Cache.slice leftMap129 rightMap129 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice158 : Residual1Cache.slice leftMap129 rightMap129 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice159 : Residual1Cache.slice leftMap129 rightMap129 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice160 : Residual1Cache.slice leftMap129 rightMap129 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice161 : Residual1Cache.slice leftMap129 rightMap129 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice162 : Residual1Cache.slice leftMap129 rightMap129 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice163 : Residual1Cache.slice leftMap129 rightMap129 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice164 : Residual1Cache.slice leftMap129 rightMap129 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice165 : Residual1Cache.slice leftMap129 rightMap129 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice166 : Residual1Cache.slice leftMap129 rightMap129 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice167 : Residual1Cache.slice leftMap129 rightMap129 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice168 : Residual1Cache.slice leftMap129 rightMap129 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice169 : Residual1Cache.slice leftMap129 rightMap129 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice170 : Residual1Cache.slice leftMap129 rightMap129 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice171 : Residual1Cache.slice leftMap129 rightMap129 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice172 : Residual1Cache.slice leftMap129 rightMap129 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice173 : Residual1Cache.slice leftMap129 rightMap129 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice174 : Residual1Cache.slice leftMap129 rightMap129 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice175 : Residual1Cache.slice leftMap129 rightMap129 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice176 : Residual1Cache.slice leftMap129 rightMap129 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice177 : Residual1Cache.slice leftMap129 rightMap129 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice178 : Residual1Cache.slice leftMap129 rightMap129 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice179 : Residual1Cache.slice leftMap129 rightMap129 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice180 : Residual1Cache.slice leftMap129 rightMap129 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice181 : Residual1Cache.slice leftMap129 rightMap129 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice182 : Residual1Cache.slice leftMap129 rightMap129 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice183 : Residual1Cache.slice leftMap129 rightMap129 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice184 : Residual1Cache.slice leftMap129 rightMap129 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice185 : Residual1Cache.slice leftMap129 rightMap129 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice186 : Residual1Cache.slice leftMap129 rightMap129 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice187 : Residual1Cache.slice leftMap129 rightMap129 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice188 : Residual1Cache.slice leftMap129 rightMap129 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice189 : Residual1Cache.slice leftMap129 rightMap129 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice190 : Residual1Cache.slice leftMap129 rightMap129 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice191 : Residual1Cache.slice leftMap129 rightMap129 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice192 : Residual1Cache.slice leftMap129 rightMap129 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice193 : Residual1Cache.slice leftMap129 rightMap129 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice194 : Residual1Cache.slice leftMap129 rightMap129 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice195 : Residual1Cache.slice leftMap129 rightMap129 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice196 : Residual1Cache.slice leftMap129 rightMap129 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice197 : Residual1Cache.slice leftMap129 rightMap129 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice198 : Residual1Cache.slice leftMap129 rightMap129 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice199 : Residual1Cache.slice leftMap129 rightMap129 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice200 : Residual1Cache.slice leftMap129 rightMap129 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice201 : Residual1Cache.slice leftMap129 rightMap129 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point129slice202 : Residual1Cache.slice leftMap129 rightMap129 202 = true := by
  decide +kernel

private theorem point129_slices : ∀ c, Residual1Cache.slice leftMap129 rightMap129 c = true := by
  intro c
  fin_cases c
  · exact point129slice0
  · exact point129slice1
  · exact point129slice2
  · exact point129slice3
  · exact point129slice4
  · exact point129slice5
  · exact point129slice6
  · exact point129slice7
  · exact point129slice8
  · exact point129slice9
  · exact point129slice10
  · exact point129slice11
  · exact point129slice12
  · exact point129slice13
  · exact point129slice14
  · exact point129slice15
  · exact point129slice16
  · exact point129slice17
  · exact point129slice18
  · exact point129slice19
  · exact point129slice20
  · exact point129slice21
  · exact point129slice22
  · exact point129slice23
  · exact point129slice24
  · exact point129slice25
  · exact point129slice26
  · exact point129slice27
  · exact point129slice28
  · exact point129slice29
  · exact point129slice30
  · exact point129slice31
  · exact point129slice32
  · exact point129slice33
  · exact point129slice34
  · exact point129slice35
  · exact point129slice36
  · exact point129slice37
  · exact point129slice38
  · exact point129slice39
  · exact point129slice40
  · exact point129slice41
  · exact point129slice42
  · exact point129slice43
  · exact point129slice44
  · exact point129slice45
  · exact point129slice46
  · exact point129slice47
  · exact point129slice48
  · exact point129slice49
  · exact point129slice50
  · exact point129slice51
  · exact point129slice52
  · exact point129slice53
  · exact point129slice54
  · exact point129slice55
  · exact point129slice56
  · exact point129slice57
  · exact point129slice58
  · exact point129slice59
  · exact point129slice60
  · exact point129slice61
  · exact point129slice62
  · exact point129slice63
  · exact point129slice64
  · exact point129slice65
  · exact point129slice66
  · exact point129slice67
  · exact point129slice68
  · exact point129slice69
  · exact point129slice70
  · exact point129slice71
  · exact point129slice72
  · exact point129slice73
  · exact point129slice74
  · exact point129slice75
  · exact point129slice76
  · exact point129slice77
  · exact point129slice78
  · exact point129slice79
  · exact point129slice80
  · exact point129slice81
  · exact point129slice82
  · exact point129slice83
  · exact point129slice84
  · exact point129slice85
  · exact point129slice86
  · exact point129slice87
  · exact point129slice88
  · exact point129slice89
  · exact point129slice90
  · exact point129slice91
  · exact point129slice92
  · exact point129slice93
  · exact point129slice94
  · exact point129slice95
  · exact point129slice96
  · exact point129slice97
  · exact point129slice98
  · exact point129slice99
  · exact point129slice100
  · exact point129slice101
  · exact point129slice102
  · exact point129slice103
  · exact point129slice104
  · exact point129slice105
  · exact point129slice106
  · exact point129slice107
  · exact point129slice108
  · exact point129slice109
  · exact point129slice110
  · exact point129slice111
  · exact point129slice112
  · exact point129slice113
  · exact point129slice114
  · exact point129slice115
  · exact point129slice116
  · exact point129slice117
  · exact point129slice118
  · exact point129slice119
  · exact point129slice120
  · exact point129slice121
  · exact point129slice122
  · exact point129slice123
  · exact point129slice124
  · exact point129slice125
  · exact point129slice126
  · exact point129slice127
  · exact point129slice128
  · exact point129slice129
  · exact point129slice130
  · exact point129slice131
  · exact point129slice132
  · exact point129slice133
  · exact point129slice134
  · exact point129slice135
  · exact point129slice136
  · exact point129slice137
  · exact point129slice138
  · exact point129slice139
  · exact point129slice140
  · exact point129slice141
  · exact point129slice142
  · exact point129slice143
  · exact point129slice144
  · exact point129slice145
  · exact point129slice146
  · exact point129slice147
  · exact point129slice148
  · exact point129slice149
  · exact point129slice150
  · exact point129slice151
  · exact point129slice152
  · exact point129slice153
  · exact point129slice154
  · exact point129slice155
  · exact point129slice156
  · exact point129slice157
  · exact point129slice158
  · exact point129slice159
  · exact point129slice160
  · exact point129slice161
  · exact point129slice162
  · exact point129slice163
  · exact point129slice164
  · exact point129slice165
  · exact point129slice166
  · exact point129slice167
  · exact point129slice168
  · exact point129slice169
  · exact point129slice170
  · exact point129slice171
  · exact point129slice172
  · exact point129slice173
  · exact point129slice174
  · exact point129slice175
  · exact point129slice176
  · exact point129slice177
  · exact point129slice178
  · exact point129slice179
  · exact point129slice180
  · exact point129slice181
  · exact point129slice182
  · exact point129slice183
  · exact point129slice184
  · exact point129slice185
  · exact point129slice186
  · exact point129slice187
  · exact point129slice188
  · exact point129slice189
  · exact point129slice190
  · exact point129slice191
  · exact point129slice192
  · exact point129slice193
  · exact point129slice194
  · exact point129slice195
  · exact point129slice196
  · exact point129slice197
  · exact point129slice198
  · exact point129slice199
  · exact point129slice200
  · exact point129slice201
  · exact point129slice202

set_option maxHeartbeats 1600000 in
public theorem point129 : stepCheck 0 2704 := by
  have hleft : L0Gen 0 * L0Rep 2704 = leftPerm129 := by
    change L0Gen 0 * evalWord L0Gen [1, 0, 3, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3] = leftPerm129
    simp only [leftPerm129, p153, p140, p67, p48, p47, p20, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2704) * evalWord L1Gen (L0Factor 0 2704) = rightPerm129 := by
    change evalWord L0Gen [1, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3] * evalWord L1Gen [1, 2, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm129
    simp only [rightPerm129, p321, p283, p277, p196, p147, p94, p62, p60, p56, p51, p49, p46, p45, p44, p43, p42, p41, p40, p39, p37, p36, p35, p34, p33, p32, p31, p30, p29, p28, p27, p26, p24, p23, p22, p21, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2704) x =
    (L0Rep (L0Act 0 2704) * evalWord L1Gen (L0Factor 0 2704)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap129_eq, ← rightMap129_eq]
  exact Residual1Cache.ofSlices point129_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
