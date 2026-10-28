module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level11Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 138

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap138 (x : Nat) : Nat := force t0 (force t150 (t53 x))
private def leftPerm138 : Equiv.Perm (Fin 4060) := p0 * (p150 * (p53))
private theorem leftMap138_eq (x : Fin 4060) :
    leftMap138 x.val = (leftPerm138 x).val := (compose (t := fun x => force t0 (force t150 (t53 x))) (a := t0) (b := fun x => force t150 (t53 x)) (fun _ => rfl) c0 (compose (t := fun x => force t150 (t53 x)) (a := t150) (b := fun x => t53 x) (fun _ => rfl) c150 c53)) x

private def rightMap138 (x : Nat) : Nat := force t68 (force t283 (force t199 (force t28 (force t18 (force t131 (force t33 (t106 x)))))))
private def rightPerm138 : Equiv.Perm (Fin 4060) := p68 * (p283 * (p199 * (p37 * (p18 * (p131 * (p33 * (p106)))))))
private theorem rightMap138_eq (x : Fin 4060) :
    rightMap138 x.val = (rightPerm138 x).val := (compose (t := fun x => force t68 (force t283 (force t199 (force t28 (force t18 (force t131 (force t33 (t106 x)))))))) (a := t68) (b := fun x => force t283 (force t199 (force t28 (force t18 (force t131 (force t33 (t106 x))))))) (fun _ => rfl) c68 (compose (t := fun x => force t283 (force t199 (force t28 (force t18 (force t131 (force t33 (t106 x))))))) (a := t283) (b := fun x => force t199 (force t28 (force t18 (force t131 (force t33 (t106 x)))))) (fun _ => rfl) c283 (compose (t := fun x => force t199 (force t28 (force t18 (force t131 (force t33 (t106 x)))))) (a := t199) (b := fun x => force t28 (force t18 (force t131 (force t33 (t106 x))))) (fun _ => rfl) c199 (compose (t := fun x => force t28 (force t18 (force t131 (force t33 (t106 x))))) (a := t28) (b := fun x => force t18 (force t131 (force t33 (t106 x)))) (fun _ => rfl) c37 (compose (t := fun x => force t18 (force t131 (force t33 (t106 x)))) (a := t18) (b := fun x => force t131 (force t33 (t106 x))) (fun _ => rfl) c18 (compose (t := fun x => force t131 (force t33 (t106 x))) (a := t131) (b := fun x => force t33 (t106 x)) (fun _ => rfl) c131 (compose (t := fun x => force t33 (t106 x)) (a := t33) (b := fun x => t106 x) (fun _ => rfl) c33 c106))))))) x

set_option maxHeartbeats 1600000 in
private theorem point138slice0 : Residual1Cache.slice leftMap138 rightMap138 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice1 : Residual1Cache.slice leftMap138 rightMap138 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice2 : Residual1Cache.slice leftMap138 rightMap138 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice3 : Residual1Cache.slice leftMap138 rightMap138 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice4 : Residual1Cache.slice leftMap138 rightMap138 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice5 : Residual1Cache.slice leftMap138 rightMap138 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice6 : Residual1Cache.slice leftMap138 rightMap138 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice7 : Residual1Cache.slice leftMap138 rightMap138 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice8 : Residual1Cache.slice leftMap138 rightMap138 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice9 : Residual1Cache.slice leftMap138 rightMap138 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice10 : Residual1Cache.slice leftMap138 rightMap138 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice11 : Residual1Cache.slice leftMap138 rightMap138 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice12 : Residual1Cache.slice leftMap138 rightMap138 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice13 : Residual1Cache.slice leftMap138 rightMap138 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice14 : Residual1Cache.slice leftMap138 rightMap138 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice15 : Residual1Cache.slice leftMap138 rightMap138 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice16 : Residual1Cache.slice leftMap138 rightMap138 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice17 : Residual1Cache.slice leftMap138 rightMap138 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice18 : Residual1Cache.slice leftMap138 rightMap138 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice19 : Residual1Cache.slice leftMap138 rightMap138 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice20 : Residual1Cache.slice leftMap138 rightMap138 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice21 : Residual1Cache.slice leftMap138 rightMap138 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice22 : Residual1Cache.slice leftMap138 rightMap138 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice23 : Residual1Cache.slice leftMap138 rightMap138 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice24 : Residual1Cache.slice leftMap138 rightMap138 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice25 : Residual1Cache.slice leftMap138 rightMap138 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice26 : Residual1Cache.slice leftMap138 rightMap138 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice27 : Residual1Cache.slice leftMap138 rightMap138 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice28 : Residual1Cache.slice leftMap138 rightMap138 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice29 : Residual1Cache.slice leftMap138 rightMap138 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice30 : Residual1Cache.slice leftMap138 rightMap138 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice31 : Residual1Cache.slice leftMap138 rightMap138 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice32 : Residual1Cache.slice leftMap138 rightMap138 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice33 : Residual1Cache.slice leftMap138 rightMap138 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice34 : Residual1Cache.slice leftMap138 rightMap138 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice35 : Residual1Cache.slice leftMap138 rightMap138 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice36 : Residual1Cache.slice leftMap138 rightMap138 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice37 : Residual1Cache.slice leftMap138 rightMap138 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice38 : Residual1Cache.slice leftMap138 rightMap138 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice39 : Residual1Cache.slice leftMap138 rightMap138 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice40 : Residual1Cache.slice leftMap138 rightMap138 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice41 : Residual1Cache.slice leftMap138 rightMap138 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice42 : Residual1Cache.slice leftMap138 rightMap138 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice43 : Residual1Cache.slice leftMap138 rightMap138 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice44 : Residual1Cache.slice leftMap138 rightMap138 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice45 : Residual1Cache.slice leftMap138 rightMap138 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice46 : Residual1Cache.slice leftMap138 rightMap138 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice47 : Residual1Cache.slice leftMap138 rightMap138 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice48 : Residual1Cache.slice leftMap138 rightMap138 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice49 : Residual1Cache.slice leftMap138 rightMap138 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice50 : Residual1Cache.slice leftMap138 rightMap138 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice51 : Residual1Cache.slice leftMap138 rightMap138 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice52 : Residual1Cache.slice leftMap138 rightMap138 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice53 : Residual1Cache.slice leftMap138 rightMap138 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice54 : Residual1Cache.slice leftMap138 rightMap138 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice55 : Residual1Cache.slice leftMap138 rightMap138 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice56 : Residual1Cache.slice leftMap138 rightMap138 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice57 : Residual1Cache.slice leftMap138 rightMap138 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice58 : Residual1Cache.slice leftMap138 rightMap138 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice59 : Residual1Cache.slice leftMap138 rightMap138 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice60 : Residual1Cache.slice leftMap138 rightMap138 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice61 : Residual1Cache.slice leftMap138 rightMap138 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice62 : Residual1Cache.slice leftMap138 rightMap138 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice63 : Residual1Cache.slice leftMap138 rightMap138 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice64 : Residual1Cache.slice leftMap138 rightMap138 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice65 : Residual1Cache.slice leftMap138 rightMap138 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice66 : Residual1Cache.slice leftMap138 rightMap138 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice67 : Residual1Cache.slice leftMap138 rightMap138 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice68 : Residual1Cache.slice leftMap138 rightMap138 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice69 : Residual1Cache.slice leftMap138 rightMap138 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice70 : Residual1Cache.slice leftMap138 rightMap138 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice71 : Residual1Cache.slice leftMap138 rightMap138 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice72 : Residual1Cache.slice leftMap138 rightMap138 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice73 : Residual1Cache.slice leftMap138 rightMap138 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice74 : Residual1Cache.slice leftMap138 rightMap138 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice75 : Residual1Cache.slice leftMap138 rightMap138 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice76 : Residual1Cache.slice leftMap138 rightMap138 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice77 : Residual1Cache.slice leftMap138 rightMap138 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice78 : Residual1Cache.slice leftMap138 rightMap138 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice79 : Residual1Cache.slice leftMap138 rightMap138 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice80 : Residual1Cache.slice leftMap138 rightMap138 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice81 : Residual1Cache.slice leftMap138 rightMap138 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice82 : Residual1Cache.slice leftMap138 rightMap138 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice83 : Residual1Cache.slice leftMap138 rightMap138 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice84 : Residual1Cache.slice leftMap138 rightMap138 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice85 : Residual1Cache.slice leftMap138 rightMap138 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice86 : Residual1Cache.slice leftMap138 rightMap138 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice87 : Residual1Cache.slice leftMap138 rightMap138 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice88 : Residual1Cache.slice leftMap138 rightMap138 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice89 : Residual1Cache.slice leftMap138 rightMap138 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice90 : Residual1Cache.slice leftMap138 rightMap138 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice91 : Residual1Cache.slice leftMap138 rightMap138 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice92 : Residual1Cache.slice leftMap138 rightMap138 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice93 : Residual1Cache.slice leftMap138 rightMap138 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice94 : Residual1Cache.slice leftMap138 rightMap138 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice95 : Residual1Cache.slice leftMap138 rightMap138 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice96 : Residual1Cache.slice leftMap138 rightMap138 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice97 : Residual1Cache.slice leftMap138 rightMap138 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice98 : Residual1Cache.slice leftMap138 rightMap138 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice99 : Residual1Cache.slice leftMap138 rightMap138 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice100 : Residual1Cache.slice leftMap138 rightMap138 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice101 : Residual1Cache.slice leftMap138 rightMap138 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice102 : Residual1Cache.slice leftMap138 rightMap138 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice103 : Residual1Cache.slice leftMap138 rightMap138 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice104 : Residual1Cache.slice leftMap138 rightMap138 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice105 : Residual1Cache.slice leftMap138 rightMap138 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice106 : Residual1Cache.slice leftMap138 rightMap138 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice107 : Residual1Cache.slice leftMap138 rightMap138 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice108 : Residual1Cache.slice leftMap138 rightMap138 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice109 : Residual1Cache.slice leftMap138 rightMap138 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice110 : Residual1Cache.slice leftMap138 rightMap138 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice111 : Residual1Cache.slice leftMap138 rightMap138 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice112 : Residual1Cache.slice leftMap138 rightMap138 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice113 : Residual1Cache.slice leftMap138 rightMap138 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice114 : Residual1Cache.slice leftMap138 rightMap138 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice115 : Residual1Cache.slice leftMap138 rightMap138 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice116 : Residual1Cache.slice leftMap138 rightMap138 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice117 : Residual1Cache.slice leftMap138 rightMap138 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice118 : Residual1Cache.slice leftMap138 rightMap138 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice119 : Residual1Cache.slice leftMap138 rightMap138 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice120 : Residual1Cache.slice leftMap138 rightMap138 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice121 : Residual1Cache.slice leftMap138 rightMap138 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice122 : Residual1Cache.slice leftMap138 rightMap138 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice123 : Residual1Cache.slice leftMap138 rightMap138 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice124 : Residual1Cache.slice leftMap138 rightMap138 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice125 : Residual1Cache.slice leftMap138 rightMap138 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice126 : Residual1Cache.slice leftMap138 rightMap138 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice127 : Residual1Cache.slice leftMap138 rightMap138 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice128 : Residual1Cache.slice leftMap138 rightMap138 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice129 : Residual1Cache.slice leftMap138 rightMap138 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice130 : Residual1Cache.slice leftMap138 rightMap138 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice131 : Residual1Cache.slice leftMap138 rightMap138 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice132 : Residual1Cache.slice leftMap138 rightMap138 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice133 : Residual1Cache.slice leftMap138 rightMap138 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice134 : Residual1Cache.slice leftMap138 rightMap138 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice135 : Residual1Cache.slice leftMap138 rightMap138 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice136 : Residual1Cache.slice leftMap138 rightMap138 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice137 : Residual1Cache.slice leftMap138 rightMap138 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice138 : Residual1Cache.slice leftMap138 rightMap138 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice139 : Residual1Cache.slice leftMap138 rightMap138 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice140 : Residual1Cache.slice leftMap138 rightMap138 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice141 : Residual1Cache.slice leftMap138 rightMap138 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice142 : Residual1Cache.slice leftMap138 rightMap138 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice143 : Residual1Cache.slice leftMap138 rightMap138 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice144 : Residual1Cache.slice leftMap138 rightMap138 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice145 : Residual1Cache.slice leftMap138 rightMap138 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice146 : Residual1Cache.slice leftMap138 rightMap138 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice147 : Residual1Cache.slice leftMap138 rightMap138 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice148 : Residual1Cache.slice leftMap138 rightMap138 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice149 : Residual1Cache.slice leftMap138 rightMap138 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice150 : Residual1Cache.slice leftMap138 rightMap138 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice151 : Residual1Cache.slice leftMap138 rightMap138 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice152 : Residual1Cache.slice leftMap138 rightMap138 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice153 : Residual1Cache.slice leftMap138 rightMap138 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice154 : Residual1Cache.slice leftMap138 rightMap138 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice155 : Residual1Cache.slice leftMap138 rightMap138 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice156 : Residual1Cache.slice leftMap138 rightMap138 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice157 : Residual1Cache.slice leftMap138 rightMap138 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice158 : Residual1Cache.slice leftMap138 rightMap138 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice159 : Residual1Cache.slice leftMap138 rightMap138 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice160 : Residual1Cache.slice leftMap138 rightMap138 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice161 : Residual1Cache.slice leftMap138 rightMap138 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice162 : Residual1Cache.slice leftMap138 rightMap138 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice163 : Residual1Cache.slice leftMap138 rightMap138 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice164 : Residual1Cache.slice leftMap138 rightMap138 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice165 : Residual1Cache.slice leftMap138 rightMap138 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice166 : Residual1Cache.slice leftMap138 rightMap138 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice167 : Residual1Cache.slice leftMap138 rightMap138 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice168 : Residual1Cache.slice leftMap138 rightMap138 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice169 : Residual1Cache.slice leftMap138 rightMap138 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice170 : Residual1Cache.slice leftMap138 rightMap138 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice171 : Residual1Cache.slice leftMap138 rightMap138 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice172 : Residual1Cache.slice leftMap138 rightMap138 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice173 : Residual1Cache.slice leftMap138 rightMap138 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice174 : Residual1Cache.slice leftMap138 rightMap138 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice175 : Residual1Cache.slice leftMap138 rightMap138 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice176 : Residual1Cache.slice leftMap138 rightMap138 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice177 : Residual1Cache.slice leftMap138 rightMap138 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice178 : Residual1Cache.slice leftMap138 rightMap138 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice179 : Residual1Cache.slice leftMap138 rightMap138 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice180 : Residual1Cache.slice leftMap138 rightMap138 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice181 : Residual1Cache.slice leftMap138 rightMap138 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice182 : Residual1Cache.slice leftMap138 rightMap138 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice183 : Residual1Cache.slice leftMap138 rightMap138 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice184 : Residual1Cache.slice leftMap138 rightMap138 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice185 : Residual1Cache.slice leftMap138 rightMap138 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice186 : Residual1Cache.slice leftMap138 rightMap138 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice187 : Residual1Cache.slice leftMap138 rightMap138 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice188 : Residual1Cache.slice leftMap138 rightMap138 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice189 : Residual1Cache.slice leftMap138 rightMap138 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice190 : Residual1Cache.slice leftMap138 rightMap138 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice191 : Residual1Cache.slice leftMap138 rightMap138 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice192 : Residual1Cache.slice leftMap138 rightMap138 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice193 : Residual1Cache.slice leftMap138 rightMap138 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice194 : Residual1Cache.slice leftMap138 rightMap138 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice195 : Residual1Cache.slice leftMap138 rightMap138 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice196 : Residual1Cache.slice leftMap138 rightMap138 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice197 : Residual1Cache.slice leftMap138 rightMap138 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice198 : Residual1Cache.slice leftMap138 rightMap138 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice199 : Residual1Cache.slice leftMap138 rightMap138 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice200 : Residual1Cache.slice leftMap138 rightMap138 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice201 : Residual1Cache.slice leftMap138 rightMap138 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point138slice202 : Residual1Cache.slice leftMap138 rightMap138 202 = true := by
  decide +kernel

private theorem point138_slices : ∀ c, Residual1Cache.slice leftMap138 rightMap138 c = true := by
  intro c
  fin_cases c
  · exact point138slice0
  · exact point138slice1
  · exact point138slice2
  · exact point138slice3
  · exact point138slice4
  · exact point138slice5
  · exact point138slice6
  · exact point138slice7
  · exact point138slice8
  · exact point138slice9
  · exact point138slice10
  · exact point138slice11
  · exact point138slice12
  · exact point138slice13
  · exact point138slice14
  · exact point138slice15
  · exact point138slice16
  · exact point138slice17
  · exact point138slice18
  · exact point138slice19
  · exact point138slice20
  · exact point138slice21
  · exact point138slice22
  · exact point138slice23
  · exact point138slice24
  · exact point138slice25
  · exact point138slice26
  · exact point138slice27
  · exact point138slice28
  · exact point138slice29
  · exact point138slice30
  · exact point138slice31
  · exact point138slice32
  · exact point138slice33
  · exact point138slice34
  · exact point138slice35
  · exact point138slice36
  · exact point138slice37
  · exact point138slice38
  · exact point138slice39
  · exact point138slice40
  · exact point138slice41
  · exact point138slice42
  · exact point138slice43
  · exact point138slice44
  · exact point138slice45
  · exact point138slice46
  · exact point138slice47
  · exact point138slice48
  · exact point138slice49
  · exact point138slice50
  · exact point138slice51
  · exact point138slice52
  · exact point138slice53
  · exact point138slice54
  · exact point138slice55
  · exact point138slice56
  · exact point138slice57
  · exact point138slice58
  · exact point138slice59
  · exact point138slice60
  · exact point138slice61
  · exact point138slice62
  · exact point138slice63
  · exact point138slice64
  · exact point138slice65
  · exact point138slice66
  · exact point138slice67
  · exact point138slice68
  · exact point138slice69
  · exact point138slice70
  · exact point138slice71
  · exact point138slice72
  · exact point138slice73
  · exact point138slice74
  · exact point138slice75
  · exact point138slice76
  · exact point138slice77
  · exact point138slice78
  · exact point138slice79
  · exact point138slice80
  · exact point138slice81
  · exact point138slice82
  · exact point138slice83
  · exact point138slice84
  · exact point138slice85
  · exact point138slice86
  · exact point138slice87
  · exact point138slice88
  · exact point138slice89
  · exact point138slice90
  · exact point138slice91
  · exact point138slice92
  · exact point138slice93
  · exact point138slice94
  · exact point138slice95
  · exact point138slice96
  · exact point138slice97
  · exact point138slice98
  · exact point138slice99
  · exact point138slice100
  · exact point138slice101
  · exact point138slice102
  · exact point138slice103
  · exact point138slice104
  · exact point138slice105
  · exact point138slice106
  · exact point138slice107
  · exact point138slice108
  · exact point138slice109
  · exact point138slice110
  · exact point138slice111
  · exact point138slice112
  · exact point138slice113
  · exact point138slice114
  · exact point138slice115
  · exact point138slice116
  · exact point138slice117
  · exact point138slice118
  · exact point138slice119
  · exact point138slice120
  · exact point138slice121
  · exact point138slice122
  · exact point138slice123
  · exact point138slice124
  · exact point138slice125
  · exact point138slice126
  · exact point138slice127
  · exact point138slice128
  · exact point138slice129
  · exact point138slice130
  · exact point138slice131
  · exact point138slice132
  · exact point138slice133
  · exact point138slice134
  · exact point138slice135
  · exact point138slice136
  · exact point138slice137
  · exact point138slice138
  · exact point138slice139
  · exact point138slice140
  · exact point138slice141
  · exact point138slice142
  · exact point138slice143
  · exact point138slice144
  · exact point138slice145
  · exact point138slice146
  · exact point138slice147
  · exact point138slice148
  · exact point138slice149
  · exact point138slice150
  · exact point138slice151
  · exact point138slice152
  · exact point138slice153
  · exact point138slice154
  · exact point138slice155
  · exact point138slice156
  · exact point138slice157
  · exact point138slice158
  · exact point138slice159
  · exact point138slice160
  · exact point138slice161
  · exact point138slice162
  · exact point138slice163
  · exact point138slice164
  · exact point138slice165
  · exact point138slice166
  · exact point138slice167
  · exact point138slice168
  · exact point138slice169
  · exact point138slice170
  · exact point138slice171
  · exact point138slice172
  · exact point138slice173
  · exact point138slice174
  · exact point138slice175
  · exact point138slice176
  · exact point138slice177
  · exact point138slice178
  · exact point138slice179
  · exact point138slice180
  · exact point138slice181
  · exact point138slice182
  · exact point138slice183
  · exact point138slice184
  · exact point138slice185
  · exact point138slice186
  · exact point138slice187
  · exact point138slice188
  · exact point138slice189
  · exact point138slice190
  · exact point138slice191
  · exact point138slice192
  · exact point138slice193
  · exact point138slice194
  · exact point138slice195
  · exact point138slice196
  · exact point138slice197
  · exact point138slice198
  · exact point138slice199
  · exact point138slice200
  · exact point138slice201
  · exact point138slice202

set_option maxHeartbeats 1600000 in
public theorem point138 : stepCheck 0 2846 := by
  have hleft : L0Gen 0 * L0Rep 2846 = leftPerm138 := by
    change L0Gen 0 * evalWord L0Gen [1, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0] = leftPerm138
    simp only [leftPerm138, p150, p53, p50, p47, p20, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2846) * evalWord L1Gen (L0Factor 0 2846) = rightPerm138 := by
    change evalWord L0Gen [1, 1, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3] * evalWord L1Gen [0, 1, 0, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3] = rightPerm138
    simp only [rightPerm138, p283, p199, p131, p106, p96, p68, p60, p46, p44, p43, p42, p40, p39, p37, p36, p35, p34, p33, p32, p30, p29, p28, p27, p24, p22, p21, p20, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2846) x =
    (L0Rep (L0Act 0 2846) * evalWord L1Gen (L0Factor 0 2846)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap138_eq, ← rightMap138_eq]
  exact Residual1Cache.ofSlices point138_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
