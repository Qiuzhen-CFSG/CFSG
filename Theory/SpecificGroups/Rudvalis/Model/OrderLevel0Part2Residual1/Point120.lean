module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level11Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 120

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap120 (x : Nat) : Nat := force t11 (force t92 (t80 x))
private def leftPerm120 : Equiv.Perm (Fin 4060) := p11 * (p92 * (p80))
private theorem leftMap120_eq (x : Fin 4060) :
    leftMap120 x.val = (leftPerm120 x).val := (compose (t := fun x => force t11 (force t92 (t80 x))) (a := t11) (b := fun x => force t92 (t80 x)) (fun _ => rfl) c11 (compose (t := fun x => force t92 (t80 x)) (a := t92) (b := fun x => t80 x) (fun _ => rfl) c92 c80)) x

private def rightMap120 (x : Nat) : Nat := force t283 (force t166 (force t499 (t504 x)))
private def rightPerm120 : Equiv.Perm (Fin 4060) := p283 * (p166 * (p499 * (p504)))
private theorem rightMap120_eq (x : Fin 4060) :
    rightMap120 x.val = (rightPerm120 x).val := (compose (t := fun x => force t283 (force t166 (force t499 (t504 x)))) (a := t283) (b := fun x => force t166 (force t499 (t504 x))) (fun _ => rfl) c283 (compose (t := fun x => force t166 (force t499 (t504 x))) (a := t166) (b := fun x => force t499 (t504 x)) (fun _ => rfl) c166 (compose (t := fun x => force t499 (t504 x)) (a := t499) (b := fun x => t504 x) (fun _ => rfl) c499 c504))) x

set_option maxHeartbeats 1600000 in
private theorem point120slice0 : Residual1Cache.slice leftMap120 rightMap120 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice1 : Residual1Cache.slice leftMap120 rightMap120 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice2 : Residual1Cache.slice leftMap120 rightMap120 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice3 : Residual1Cache.slice leftMap120 rightMap120 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice4 : Residual1Cache.slice leftMap120 rightMap120 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice5 : Residual1Cache.slice leftMap120 rightMap120 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice6 : Residual1Cache.slice leftMap120 rightMap120 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice7 : Residual1Cache.slice leftMap120 rightMap120 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice8 : Residual1Cache.slice leftMap120 rightMap120 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice9 : Residual1Cache.slice leftMap120 rightMap120 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice10 : Residual1Cache.slice leftMap120 rightMap120 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice11 : Residual1Cache.slice leftMap120 rightMap120 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice12 : Residual1Cache.slice leftMap120 rightMap120 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice13 : Residual1Cache.slice leftMap120 rightMap120 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice14 : Residual1Cache.slice leftMap120 rightMap120 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice15 : Residual1Cache.slice leftMap120 rightMap120 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice16 : Residual1Cache.slice leftMap120 rightMap120 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice17 : Residual1Cache.slice leftMap120 rightMap120 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice18 : Residual1Cache.slice leftMap120 rightMap120 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice19 : Residual1Cache.slice leftMap120 rightMap120 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice20 : Residual1Cache.slice leftMap120 rightMap120 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice21 : Residual1Cache.slice leftMap120 rightMap120 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice22 : Residual1Cache.slice leftMap120 rightMap120 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice23 : Residual1Cache.slice leftMap120 rightMap120 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice24 : Residual1Cache.slice leftMap120 rightMap120 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice25 : Residual1Cache.slice leftMap120 rightMap120 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice26 : Residual1Cache.slice leftMap120 rightMap120 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice27 : Residual1Cache.slice leftMap120 rightMap120 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice28 : Residual1Cache.slice leftMap120 rightMap120 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice29 : Residual1Cache.slice leftMap120 rightMap120 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice30 : Residual1Cache.slice leftMap120 rightMap120 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice31 : Residual1Cache.slice leftMap120 rightMap120 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice32 : Residual1Cache.slice leftMap120 rightMap120 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice33 : Residual1Cache.slice leftMap120 rightMap120 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice34 : Residual1Cache.slice leftMap120 rightMap120 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice35 : Residual1Cache.slice leftMap120 rightMap120 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice36 : Residual1Cache.slice leftMap120 rightMap120 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice37 : Residual1Cache.slice leftMap120 rightMap120 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice38 : Residual1Cache.slice leftMap120 rightMap120 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice39 : Residual1Cache.slice leftMap120 rightMap120 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice40 : Residual1Cache.slice leftMap120 rightMap120 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice41 : Residual1Cache.slice leftMap120 rightMap120 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice42 : Residual1Cache.slice leftMap120 rightMap120 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice43 : Residual1Cache.slice leftMap120 rightMap120 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice44 : Residual1Cache.slice leftMap120 rightMap120 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice45 : Residual1Cache.slice leftMap120 rightMap120 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice46 : Residual1Cache.slice leftMap120 rightMap120 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice47 : Residual1Cache.slice leftMap120 rightMap120 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice48 : Residual1Cache.slice leftMap120 rightMap120 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice49 : Residual1Cache.slice leftMap120 rightMap120 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice50 : Residual1Cache.slice leftMap120 rightMap120 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice51 : Residual1Cache.slice leftMap120 rightMap120 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice52 : Residual1Cache.slice leftMap120 rightMap120 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice53 : Residual1Cache.slice leftMap120 rightMap120 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice54 : Residual1Cache.slice leftMap120 rightMap120 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice55 : Residual1Cache.slice leftMap120 rightMap120 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice56 : Residual1Cache.slice leftMap120 rightMap120 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice57 : Residual1Cache.slice leftMap120 rightMap120 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice58 : Residual1Cache.slice leftMap120 rightMap120 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice59 : Residual1Cache.slice leftMap120 rightMap120 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice60 : Residual1Cache.slice leftMap120 rightMap120 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice61 : Residual1Cache.slice leftMap120 rightMap120 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice62 : Residual1Cache.slice leftMap120 rightMap120 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice63 : Residual1Cache.slice leftMap120 rightMap120 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice64 : Residual1Cache.slice leftMap120 rightMap120 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice65 : Residual1Cache.slice leftMap120 rightMap120 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice66 : Residual1Cache.slice leftMap120 rightMap120 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice67 : Residual1Cache.slice leftMap120 rightMap120 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice68 : Residual1Cache.slice leftMap120 rightMap120 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice69 : Residual1Cache.slice leftMap120 rightMap120 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice70 : Residual1Cache.slice leftMap120 rightMap120 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice71 : Residual1Cache.slice leftMap120 rightMap120 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice72 : Residual1Cache.slice leftMap120 rightMap120 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice73 : Residual1Cache.slice leftMap120 rightMap120 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice74 : Residual1Cache.slice leftMap120 rightMap120 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice75 : Residual1Cache.slice leftMap120 rightMap120 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice76 : Residual1Cache.slice leftMap120 rightMap120 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice77 : Residual1Cache.slice leftMap120 rightMap120 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice78 : Residual1Cache.slice leftMap120 rightMap120 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice79 : Residual1Cache.slice leftMap120 rightMap120 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice80 : Residual1Cache.slice leftMap120 rightMap120 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice81 : Residual1Cache.slice leftMap120 rightMap120 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice82 : Residual1Cache.slice leftMap120 rightMap120 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice83 : Residual1Cache.slice leftMap120 rightMap120 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice84 : Residual1Cache.slice leftMap120 rightMap120 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice85 : Residual1Cache.slice leftMap120 rightMap120 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice86 : Residual1Cache.slice leftMap120 rightMap120 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice87 : Residual1Cache.slice leftMap120 rightMap120 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice88 : Residual1Cache.slice leftMap120 rightMap120 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice89 : Residual1Cache.slice leftMap120 rightMap120 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice90 : Residual1Cache.slice leftMap120 rightMap120 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice91 : Residual1Cache.slice leftMap120 rightMap120 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice92 : Residual1Cache.slice leftMap120 rightMap120 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice93 : Residual1Cache.slice leftMap120 rightMap120 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice94 : Residual1Cache.slice leftMap120 rightMap120 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice95 : Residual1Cache.slice leftMap120 rightMap120 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice96 : Residual1Cache.slice leftMap120 rightMap120 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice97 : Residual1Cache.slice leftMap120 rightMap120 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice98 : Residual1Cache.slice leftMap120 rightMap120 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice99 : Residual1Cache.slice leftMap120 rightMap120 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice100 : Residual1Cache.slice leftMap120 rightMap120 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice101 : Residual1Cache.slice leftMap120 rightMap120 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice102 : Residual1Cache.slice leftMap120 rightMap120 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice103 : Residual1Cache.slice leftMap120 rightMap120 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice104 : Residual1Cache.slice leftMap120 rightMap120 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice105 : Residual1Cache.slice leftMap120 rightMap120 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice106 : Residual1Cache.slice leftMap120 rightMap120 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice107 : Residual1Cache.slice leftMap120 rightMap120 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice108 : Residual1Cache.slice leftMap120 rightMap120 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice109 : Residual1Cache.slice leftMap120 rightMap120 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice110 : Residual1Cache.slice leftMap120 rightMap120 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice111 : Residual1Cache.slice leftMap120 rightMap120 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice112 : Residual1Cache.slice leftMap120 rightMap120 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice113 : Residual1Cache.slice leftMap120 rightMap120 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice114 : Residual1Cache.slice leftMap120 rightMap120 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice115 : Residual1Cache.slice leftMap120 rightMap120 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice116 : Residual1Cache.slice leftMap120 rightMap120 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice117 : Residual1Cache.slice leftMap120 rightMap120 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice118 : Residual1Cache.slice leftMap120 rightMap120 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice119 : Residual1Cache.slice leftMap120 rightMap120 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice120 : Residual1Cache.slice leftMap120 rightMap120 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice121 : Residual1Cache.slice leftMap120 rightMap120 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice122 : Residual1Cache.slice leftMap120 rightMap120 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice123 : Residual1Cache.slice leftMap120 rightMap120 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice124 : Residual1Cache.slice leftMap120 rightMap120 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice125 : Residual1Cache.slice leftMap120 rightMap120 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice126 : Residual1Cache.slice leftMap120 rightMap120 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice127 : Residual1Cache.slice leftMap120 rightMap120 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice128 : Residual1Cache.slice leftMap120 rightMap120 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice129 : Residual1Cache.slice leftMap120 rightMap120 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice130 : Residual1Cache.slice leftMap120 rightMap120 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice131 : Residual1Cache.slice leftMap120 rightMap120 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice132 : Residual1Cache.slice leftMap120 rightMap120 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice133 : Residual1Cache.slice leftMap120 rightMap120 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice134 : Residual1Cache.slice leftMap120 rightMap120 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice135 : Residual1Cache.slice leftMap120 rightMap120 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice136 : Residual1Cache.slice leftMap120 rightMap120 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice137 : Residual1Cache.slice leftMap120 rightMap120 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice138 : Residual1Cache.slice leftMap120 rightMap120 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice139 : Residual1Cache.slice leftMap120 rightMap120 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice140 : Residual1Cache.slice leftMap120 rightMap120 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice141 : Residual1Cache.slice leftMap120 rightMap120 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice142 : Residual1Cache.slice leftMap120 rightMap120 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice143 : Residual1Cache.slice leftMap120 rightMap120 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice144 : Residual1Cache.slice leftMap120 rightMap120 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice145 : Residual1Cache.slice leftMap120 rightMap120 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice146 : Residual1Cache.slice leftMap120 rightMap120 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice147 : Residual1Cache.slice leftMap120 rightMap120 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice148 : Residual1Cache.slice leftMap120 rightMap120 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice149 : Residual1Cache.slice leftMap120 rightMap120 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice150 : Residual1Cache.slice leftMap120 rightMap120 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice151 : Residual1Cache.slice leftMap120 rightMap120 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice152 : Residual1Cache.slice leftMap120 rightMap120 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice153 : Residual1Cache.slice leftMap120 rightMap120 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice154 : Residual1Cache.slice leftMap120 rightMap120 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice155 : Residual1Cache.slice leftMap120 rightMap120 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice156 : Residual1Cache.slice leftMap120 rightMap120 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice157 : Residual1Cache.slice leftMap120 rightMap120 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice158 : Residual1Cache.slice leftMap120 rightMap120 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice159 : Residual1Cache.slice leftMap120 rightMap120 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice160 : Residual1Cache.slice leftMap120 rightMap120 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice161 : Residual1Cache.slice leftMap120 rightMap120 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice162 : Residual1Cache.slice leftMap120 rightMap120 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice163 : Residual1Cache.slice leftMap120 rightMap120 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice164 : Residual1Cache.slice leftMap120 rightMap120 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice165 : Residual1Cache.slice leftMap120 rightMap120 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice166 : Residual1Cache.slice leftMap120 rightMap120 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice167 : Residual1Cache.slice leftMap120 rightMap120 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice168 : Residual1Cache.slice leftMap120 rightMap120 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice169 : Residual1Cache.slice leftMap120 rightMap120 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice170 : Residual1Cache.slice leftMap120 rightMap120 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice171 : Residual1Cache.slice leftMap120 rightMap120 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice172 : Residual1Cache.slice leftMap120 rightMap120 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice173 : Residual1Cache.slice leftMap120 rightMap120 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice174 : Residual1Cache.slice leftMap120 rightMap120 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice175 : Residual1Cache.slice leftMap120 rightMap120 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice176 : Residual1Cache.slice leftMap120 rightMap120 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice177 : Residual1Cache.slice leftMap120 rightMap120 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice178 : Residual1Cache.slice leftMap120 rightMap120 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice179 : Residual1Cache.slice leftMap120 rightMap120 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice180 : Residual1Cache.slice leftMap120 rightMap120 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice181 : Residual1Cache.slice leftMap120 rightMap120 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice182 : Residual1Cache.slice leftMap120 rightMap120 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice183 : Residual1Cache.slice leftMap120 rightMap120 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice184 : Residual1Cache.slice leftMap120 rightMap120 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice185 : Residual1Cache.slice leftMap120 rightMap120 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice186 : Residual1Cache.slice leftMap120 rightMap120 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice187 : Residual1Cache.slice leftMap120 rightMap120 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice188 : Residual1Cache.slice leftMap120 rightMap120 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice189 : Residual1Cache.slice leftMap120 rightMap120 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice190 : Residual1Cache.slice leftMap120 rightMap120 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice191 : Residual1Cache.slice leftMap120 rightMap120 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice192 : Residual1Cache.slice leftMap120 rightMap120 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice193 : Residual1Cache.slice leftMap120 rightMap120 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice194 : Residual1Cache.slice leftMap120 rightMap120 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice195 : Residual1Cache.slice leftMap120 rightMap120 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice196 : Residual1Cache.slice leftMap120 rightMap120 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice197 : Residual1Cache.slice leftMap120 rightMap120 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice198 : Residual1Cache.slice leftMap120 rightMap120 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice199 : Residual1Cache.slice leftMap120 rightMap120 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice200 : Residual1Cache.slice leftMap120 rightMap120 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice201 : Residual1Cache.slice leftMap120 rightMap120 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point120slice202 : Residual1Cache.slice leftMap120 rightMap120 202 = true := by
  decide +kernel

private theorem point120_slices : ∀ c, Residual1Cache.slice leftMap120 rightMap120 c = true := by
  intro c
  fin_cases c
  · exact point120slice0
  · exact point120slice1
  · exact point120slice2
  · exact point120slice3
  · exact point120slice4
  · exact point120slice5
  · exact point120slice6
  · exact point120slice7
  · exact point120slice8
  · exact point120slice9
  · exact point120slice10
  · exact point120slice11
  · exact point120slice12
  · exact point120slice13
  · exact point120slice14
  · exact point120slice15
  · exact point120slice16
  · exact point120slice17
  · exact point120slice18
  · exact point120slice19
  · exact point120slice20
  · exact point120slice21
  · exact point120slice22
  · exact point120slice23
  · exact point120slice24
  · exact point120slice25
  · exact point120slice26
  · exact point120slice27
  · exact point120slice28
  · exact point120slice29
  · exact point120slice30
  · exact point120slice31
  · exact point120slice32
  · exact point120slice33
  · exact point120slice34
  · exact point120slice35
  · exact point120slice36
  · exact point120slice37
  · exact point120slice38
  · exact point120slice39
  · exact point120slice40
  · exact point120slice41
  · exact point120slice42
  · exact point120slice43
  · exact point120slice44
  · exact point120slice45
  · exact point120slice46
  · exact point120slice47
  · exact point120slice48
  · exact point120slice49
  · exact point120slice50
  · exact point120slice51
  · exact point120slice52
  · exact point120slice53
  · exact point120slice54
  · exact point120slice55
  · exact point120slice56
  · exact point120slice57
  · exact point120slice58
  · exact point120slice59
  · exact point120slice60
  · exact point120slice61
  · exact point120slice62
  · exact point120slice63
  · exact point120slice64
  · exact point120slice65
  · exact point120slice66
  · exact point120slice67
  · exact point120slice68
  · exact point120slice69
  · exact point120slice70
  · exact point120slice71
  · exact point120slice72
  · exact point120slice73
  · exact point120slice74
  · exact point120slice75
  · exact point120slice76
  · exact point120slice77
  · exact point120slice78
  · exact point120slice79
  · exact point120slice80
  · exact point120slice81
  · exact point120slice82
  · exact point120slice83
  · exact point120slice84
  · exact point120slice85
  · exact point120slice86
  · exact point120slice87
  · exact point120slice88
  · exact point120slice89
  · exact point120slice90
  · exact point120slice91
  · exact point120slice92
  · exact point120slice93
  · exact point120slice94
  · exact point120slice95
  · exact point120slice96
  · exact point120slice97
  · exact point120slice98
  · exact point120slice99
  · exact point120slice100
  · exact point120slice101
  · exact point120slice102
  · exact point120slice103
  · exact point120slice104
  · exact point120slice105
  · exact point120slice106
  · exact point120slice107
  · exact point120slice108
  · exact point120slice109
  · exact point120slice110
  · exact point120slice111
  · exact point120slice112
  · exact point120slice113
  · exact point120slice114
  · exact point120slice115
  · exact point120slice116
  · exact point120slice117
  · exact point120slice118
  · exact point120slice119
  · exact point120slice120
  · exact point120slice121
  · exact point120slice122
  · exact point120slice123
  · exact point120slice124
  · exact point120slice125
  · exact point120slice126
  · exact point120slice127
  · exact point120slice128
  · exact point120slice129
  · exact point120slice130
  · exact point120slice131
  · exact point120slice132
  · exact point120slice133
  · exact point120slice134
  · exact point120slice135
  · exact point120slice136
  · exact point120slice137
  · exact point120slice138
  · exact point120slice139
  · exact point120slice140
  · exact point120slice141
  · exact point120slice142
  · exact point120slice143
  · exact point120slice144
  · exact point120slice145
  · exact point120slice146
  · exact point120slice147
  · exact point120slice148
  · exact point120slice149
  · exact point120slice150
  · exact point120slice151
  · exact point120slice152
  · exact point120slice153
  · exact point120slice154
  · exact point120slice155
  · exact point120slice156
  · exact point120slice157
  · exact point120slice158
  · exact point120slice159
  · exact point120slice160
  · exact point120slice161
  · exact point120slice162
  · exact point120slice163
  · exact point120slice164
  · exact point120slice165
  · exact point120slice166
  · exact point120slice167
  · exact point120slice168
  · exact point120slice169
  · exact point120slice170
  · exact point120slice171
  · exact point120slice172
  · exact point120slice173
  · exact point120slice174
  · exact point120slice175
  · exact point120slice176
  · exact point120slice177
  · exact point120slice178
  · exact point120slice179
  · exact point120slice180
  · exact point120slice181
  · exact point120slice182
  · exact point120slice183
  · exact point120slice184
  · exact point120slice185
  · exact point120slice186
  · exact point120slice187
  · exact point120slice188
  · exact point120slice189
  · exact point120slice190
  · exact point120slice191
  · exact point120slice192
  · exact point120slice193
  · exact point120slice194
  · exact point120slice195
  · exact point120slice196
  · exact point120slice197
  · exact point120slice198
  · exact point120slice199
  · exact point120slice200
  · exact point120slice201
  · exact point120slice202

set_option maxHeartbeats 1600000 in
public theorem point120 : stepCheck 1 2568 := by
  have hleft : L0Gen 1 * L0Rep 2568 = leftPerm120 := by
    change L0Gen 1 * evalWord L0Gen [0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1] = leftPerm120
    simp only [leftPerm120, p92, p80, p54, p48, p30, p20, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2568) * evalWord L1Gen (L0Factor 1 2568) = rightPerm120 := by
    change evalWord L0Gen [3, 0, 3, 0, 1, 0, 3, 0, 1, 1, 0, 1, 0, 3] * evalWord L1Gen [0, 1, 0, 3, 0, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm120
    simp only [rightPerm120, p504, p503, p502, p501, p499, p283, p233, p166, p146, p78, p75, p74, p60, p45, p41, p39, p35, p34, p31, p30, p27, p26, p25, p23, p22, p21, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2568) x =
    (L0Rep (L0Act 1 2568) * evalWord L1Gen (L0Factor 1 2568)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap120_eq, ← rightMap120_eq]
  exact Residual1Cache.ofSlices point120_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
