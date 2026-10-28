module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 118

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap118 (x : Nat) : Nat := force t67 (force t102 (t80 x))
private def leftPerm118 : Equiv.Perm (Fin 4060) := p67 * (p102 * (p80))
private theorem leftMap118_eq (x : Fin 4060) :
    leftMap118 x.val = (leftPerm118 x).val := (compose (t := fun x => force t67 (force t102 (t80 x))) (a := t67) (b := fun x => force t102 (t80 x)) (fun _ => rfl) c67 (compose (t := fun x => force t102 (t80 x)) (a := t102) (b := fun x => t80 x) (fun _ => rfl) c102 c80)) x

private def rightMap118 (x : Nat) : Nat := force t30 (force t121 (force t0 (force t75 (force t42 (force t87 (force t58 (t38 x)))))))
private def rightPerm118 : Equiv.Perm (Fin 4060) := p30 * (p121 * (p0 * (p75 * (p42 * (p87 * (p58 * (p38)))))))
private theorem rightMap118_eq (x : Fin 4060) :
    rightMap118 x.val = (rightPerm118 x).val := (compose (t := fun x => force t30 (force t121 (force t0 (force t75 (force t42 (force t87 (force t58 (t38 x)))))))) (a := t30) (b := fun x => force t121 (force t0 (force t75 (force t42 (force t87 (force t58 (t38 x))))))) (fun _ => rfl) c30 (compose (t := fun x => force t121 (force t0 (force t75 (force t42 (force t87 (force t58 (t38 x))))))) (a := t121) (b := fun x => force t0 (force t75 (force t42 (force t87 (force t58 (t38 x)))))) (fun _ => rfl) c121 (compose (t := fun x => force t0 (force t75 (force t42 (force t87 (force t58 (t38 x)))))) (a := t0) (b := fun x => force t75 (force t42 (force t87 (force t58 (t38 x))))) (fun _ => rfl) c0 (compose (t := fun x => force t75 (force t42 (force t87 (force t58 (t38 x))))) (a := t75) (b := fun x => force t42 (force t87 (force t58 (t38 x)))) (fun _ => rfl) c75 (compose (t := fun x => force t42 (force t87 (force t58 (t38 x)))) (a := t42) (b := fun x => force t87 (force t58 (t38 x))) (fun _ => rfl) c42 (compose (t := fun x => force t87 (force t58 (t38 x))) (a := t87) (b := fun x => force t58 (t38 x)) (fun _ => rfl) c87 (compose (t := fun x => force t58 (t38 x)) (a := t58) (b := fun x => t38 x) (fun _ => rfl) c58 c38))))))) x

set_option maxHeartbeats 1600000 in
private theorem point118slice0 : Residual1Cache.slice leftMap118 rightMap118 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice1 : Residual1Cache.slice leftMap118 rightMap118 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice2 : Residual1Cache.slice leftMap118 rightMap118 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice3 : Residual1Cache.slice leftMap118 rightMap118 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice4 : Residual1Cache.slice leftMap118 rightMap118 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice5 : Residual1Cache.slice leftMap118 rightMap118 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice6 : Residual1Cache.slice leftMap118 rightMap118 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice7 : Residual1Cache.slice leftMap118 rightMap118 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice8 : Residual1Cache.slice leftMap118 rightMap118 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice9 : Residual1Cache.slice leftMap118 rightMap118 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice10 : Residual1Cache.slice leftMap118 rightMap118 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice11 : Residual1Cache.slice leftMap118 rightMap118 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice12 : Residual1Cache.slice leftMap118 rightMap118 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice13 : Residual1Cache.slice leftMap118 rightMap118 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice14 : Residual1Cache.slice leftMap118 rightMap118 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice15 : Residual1Cache.slice leftMap118 rightMap118 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice16 : Residual1Cache.slice leftMap118 rightMap118 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice17 : Residual1Cache.slice leftMap118 rightMap118 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice18 : Residual1Cache.slice leftMap118 rightMap118 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice19 : Residual1Cache.slice leftMap118 rightMap118 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice20 : Residual1Cache.slice leftMap118 rightMap118 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice21 : Residual1Cache.slice leftMap118 rightMap118 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice22 : Residual1Cache.slice leftMap118 rightMap118 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice23 : Residual1Cache.slice leftMap118 rightMap118 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice24 : Residual1Cache.slice leftMap118 rightMap118 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice25 : Residual1Cache.slice leftMap118 rightMap118 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice26 : Residual1Cache.slice leftMap118 rightMap118 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice27 : Residual1Cache.slice leftMap118 rightMap118 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice28 : Residual1Cache.slice leftMap118 rightMap118 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice29 : Residual1Cache.slice leftMap118 rightMap118 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice30 : Residual1Cache.slice leftMap118 rightMap118 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice31 : Residual1Cache.slice leftMap118 rightMap118 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice32 : Residual1Cache.slice leftMap118 rightMap118 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice33 : Residual1Cache.slice leftMap118 rightMap118 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice34 : Residual1Cache.slice leftMap118 rightMap118 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice35 : Residual1Cache.slice leftMap118 rightMap118 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice36 : Residual1Cache.slice leftMap118 rightMap118 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice37 : Residual1Cache.slice leftMap118 rightMap118 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice38 : Residual1Cache.slice leftMap118 rightMap118 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice39 : Residual1Cache.slice leftMap118 rightMap118 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice40 : Residual1Cache.slice leftMap118 rightMap118 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice41 : Residual1Cache.slice leftMap118 rightMap118 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice42 : Residual1Cache.slice leftMap118 rightMap118 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice43 : Residual1Cache.slice leftMap118 rightMap118 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice44 : Residual1Cache.slice leftMap118 rightMap118 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice45 : Residual1Cache.slice leftMap118 rightMap118 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice46 : Residual1Cache.slice leftMap118 rightMap118 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice47 : Residual1Cache.slice leftMap118 rightMap118 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice48 : Residual1Cache.slice leftMap118 rightMap118 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice49 : Residual1Cache.slice leftMap118 rightMap118 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice50 : Residual1Cache.slice leftMap118 rightMap118 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice51 : Residual1Cache.slice leftMap118 rightMap118 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice52 : Residual1Cache.slice leftMap118 rightMap118 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice53 : Residual1Cache.slice leftMap118 rightMap118 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice54 : Residual1Cache.slice leftMap118 rightMap118 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice55 : Residual1Cache.slice leftMap118 rightMap118 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice56 : Residual1Cache.slice leftMap118 rightMap118 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice57 : Residual1Cache.slice leftMap118 rightMap118 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice58 : Residual1Cache.slice leftMap118 rightMap118 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice59 : Residual1Cache.slice leftMap118 rightMap118 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice60 : Residual1Cache.slice leftMap118 rightMap118 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice61 : Residual1Cache.slice leftMap118 rightMap118 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice62 : Residual1Cache.slice leftMap118 rightMap118 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice63 : Residual1Cache.slice leftMap118 rightMap118 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice64 : Residual1Cache.slice leftMap118 rightMap118 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice65 : Residual1Cache.slice leftMap118 rightMap118 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice66 : Residual1Cache.slice leftMap118 rightMap118 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice67 : Residual1Cache.slice leftMap118 rightMap118 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice68 : Residual1Cache.slice leftMap118 rightMap118 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice69 : Residual1Cache.slice leftMap118 rightMap118 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice70 : Residual1Cache.slice leftMap118 rightMap118 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice71 : Residual1Cache.slice leftMap118 rightMap118 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice72 : Residual1Cache.slice leftMap118 rightMap118 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice73 : Residual1Cache.slice leftMap118 rightMap118 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice74 : Residual1Cache.slice leftMap118 rightMap118 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice75 : Residual1Cache.slice leftMap118 rightMap118 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice76 : Residual1Cache.slice leftMap118 rightMap118 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice77 : Residual1Cache.slice leftMap118 rightMap118 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice78 : Residual1Cache.slice leftMap118 rightMap118 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice79 : Residual1Cache.slice leftMap118 rightMap118 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice80 : Residual1Cache.slice leftMap118 rightMap118 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice81 : Residual1Cache.slice leftMap118 rightMap118 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice82 : Residual1Cache.slice leftMap118 rightMap118 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice83 : Residual1Cache.slice leftMap118 rightMap118 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice84 : Residual1Cache.slice leftMap118 rightMap118 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice85 : Residual1Cache.slice leftMap118 rightMap118 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice86 : Residual1Cache.slice leftMap118 rightMap118 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice87 : Residual1Cache.slice leftMap118 rightMap118 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice88 : Residual1Cache.slice leftMap118 rightMap118 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice89 : Residual1Cache.slice leftMap118 rightMap118 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice90 : Residual1Cache.slice leftMap118 rightMap118 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice91 : Residual1Cache.slice leftMap118 rightMap118 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice92 : Residual1Cache.slice leftMap118 rightMap118 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice93 : Residual1Cache.slice leftMap118 rightMap118 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice94 : Residual1Cache.slice leftMap118 rightMap118 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice95 : Residual1Cache.slice leftMap118 rightMap118 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice96 : Residual1Cache.slice leftMap118 rightMap118 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice97 : Residual1Cache.slice leftMap118 rightMap118 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice98 : Residual1Cache.slice leftMap118 rightMap118 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice99 : Residual1Cache.slice leftMap118 rightMap118 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice100 : Residual1Cache.slice leftMap118 rightMap118 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice101 : Residual1Cache.slice leftMap118 rightMap118 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice102 : Residual1Cache.slice leftMap118 rightMap118 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice103 : Residual1Cache.slice leftMap118 rightMap118 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice104 : Residual1Cache.slice leftMap118 rightMap118 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice105 : Residual1Cache.slice leftMap118 rightMap118 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice106 : Residual1Cache.slice leftMap118 rightMap118 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice107 : Residual1Cache.slice leftMap118 rightMap118 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice108 : Residual1Cache.slice leftMap118 rightMap118 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice109 : Residual1Cache.slice leftMap118 rightMap118 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice110 : Residual1Cache.slice leftMap118 rightMap118 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice111 : Residual1Cache.slice leftMap118 rightMap118 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice112 : Residual1Cache.slice leftMap118 rightMap118 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice113 : Residual1Cache.slice leftMap118 rightMap118 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice114 : Residual1Cache.slice leftMap118 rightMap118 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice115 : Residual1Cache.slice leftMap118 rightMap118 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice116 : Residual1Cache.slice leftMap118 rightMap118 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice117 : Residual1Cache.slice leftMap118 rightMap118 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice118 : Residual1Cache.slice leftMap118 rightMap118 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice119 : Residual1Cache.slice leftMap118 rightMap118 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice120 : Residual1Cache.slice leftMap118 rightMap118 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice121 : Residual1Cache.slice leftMap118 rightMap118 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice122 : Residual1Cache.slice leftMap118 rightMap118 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice123 : Residual1Cache.slice leftMap118 rightMap118 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice124 : Residual1Cache.slice leftMap118 rightMap118 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice125 : Residual1Cache.slice leftMap118 rightMap118 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice126 : Residual1Cache.slice leftMap118 rightMap118 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice127 : Residual1Cache.slice leftMap118 rightMap118 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice128 : Residual1Cache.slice leftMap118 rightMap118 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice129 : Residual1Cache.slice leftMap118 rightMap118 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice130 : Residual1Cache.slice leftMap118 rightMap118 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice131 : Residual1Cache.slice leftMap118 rightMap118 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice132 : Residual1Cache.slice leftMap118 rightMap118 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice133 : Residual1Cache.slice leftMap118 rightMap118 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice134 : Residual1Cache.slice leftMap118 rightMap118 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice135 : Residual1Cache.slice leftMap118 rightMap118 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice136 : Residual1Cache.slice leftMap118 rightMap118 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice137 : Residual1Cache.slice leftMap118 rightMap118 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice138 : Residual1Cache.slice leftMap118 rightMap118 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice139 : Residual1Cache.slice leftMap118 rightMap118 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice140 : Residual1Cache.slice leftMap118 rightMap118 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice141 : Residual1Cache.slice leftMap118 rightMap118 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice142 : Residual1Cache.slice leftMap118 rightMap118 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice143 : Residual1Cache.slice leftMap118 rightMap118 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice144 : Residual1Cache.slice leftMap118 rightMap118 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice145 : Residual1Cache.slice leftMap118 rightMap118 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice146 : Residual1Cache.slice leftMap118 rightMap118 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice147 : Residual1Cache.slice leftMap118 rightMap118 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice148 : Residual1Cache.slice leftMap118 rightMap118 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice149 : Residual1Cache.slice leftMap118 rightMap118 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice150 : Residual1Cache.slice leftMap118 rightMap118 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice151 : Residual1Cache.slice leftMap118 rightMap118 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice152 : Residual1Cache.slice leftMap118 rightMap118 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice153 : Residual1Cache.slice leftMap118 rightMap118 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice154 : Residual1Cache.slice leftMap118 rightMap118 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice155 : Residual1Cache.slice leftMap118 rightMap118 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice156 : Residual1Cache.slice leftMap118 rightMap118 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice157 : Residual1Cache.slice leftMap118 rightMap118 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice158 : Residual1Cache.slice leftMap118 rightMap118 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice159 : Residual1Cache.slice leftMap118 rightMap118 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice160 : Residual1Cache.slice leftMap118 rightMap118 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice161 : Residual1Cache.slice leftMap118 rightMap118 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice162 : Residual1Cache.slice leftMap118 rightMap118 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice163 : Residual1Cache.slice leftMap118 rightMap118 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice164 : Residual1Cache.slice leftMap118 rightMap118 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice165 : Residual1Cache.slice leftMap118 rightMap118 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice166 : Residual1Cache.slice leftMap118 rightMap118 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice167 : Residual1Cache.slice leftMap118 rightMap118 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice168 : Residual1Cache.slice leftMap118 rightMap118 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice169 : Residual1Cache.slice leftMap118 rightMap118 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice170 : Residual1Cache.slice leftMap118 rightMap118 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice171 : Residual1Cache.slice leftMap118 rightMap118 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice172 : Residual1Cache.slice leftMap118 rightMap118 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice173 : Residual1Cache.slice leftMap118 rightMap118 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice174 : Residual1Cache.slice leftMap118 rightMap118 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice175 : Residual1Cache.slice leftMap118 rightMap118 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice176 : Residual1Cache.slice leftMap118 rightMap118 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice177 : Residual1Cache.slice leftMap118 rightMap118 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice178 : Residual1Cache.slice leftMap118 rightMap118 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice179 : Residual1Cache.slice leftMap118 rightMap118 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice180 : Residual1Cache.slice leftMap118 rightMap118 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice181 : Residual1Cache.slice leftMap118 rightMap118 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice182 : Residual1Cache.slice leftMap118 rightMap118 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice183 : Residual1Cache.slice leftMap118 rightMap118 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice184 : Residual1Cache.slice leftMap118 rightMap118 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice185 : Residual1Cache.slice leftMap118 rightMap118 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice186 : Residual1Cache.slice leftMap118 rightMap118 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice187 : Residual1Cache.slice leftMap118 rightMap118 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice188 : Residual1Cache.slice leftMap118 rightMap118 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice189 : Residual1Cache.slice leftMap118 rightMap118 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice190 : Residual1Cache.slice leftMap118 rightMap118 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice191 : Residual1Cache.slice leftMap118 rightMap118 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice192 : Residual1Cache.slice leftMap118 rightMap118 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice193 : Residual1Cache.slice leftMap118 rightMap118 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice194 : Residual1Cache.slice leftMap118 rightMap118 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice195 : Residual1Cache.slice leftMap118 rightMap118 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice196 : Residual1Cache.slice leftMap118 rightMap118 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice197 : Residual1Cache.slice leftMap118 rightMap118 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice198 : Residual1Cache.slice leftMap118 rightMap118 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice199 : Residual1Cache.slice leftMap118 rightMap118 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice200 : Residual1Cache.slice leftMap118 rightMap118 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice201 : Residual1Cache.slice leftMap118 rightMap118 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point118slice202 : Residual1Cache.slice leftMap118 rightMap118 202 = true := by
  decide +kernel

private theorem point118_slices : ∀ c, Residual1Cache.slice leftMap118 rightMap118 c = true := by
  intro c
  fin_cases c
  · exact point118slice0
  · exact point118slice1
  · exact point118slice2
  · exact point118slice3
  · exact point118slice4
  · exact point118slice5
  · exact point118slice6
  · exact point118slice7
  · exact point118slice8
  · exact point118slice9
  · exact point118slice10
  · exact point118slice11
  · exact point118slice12
  · exact point118slice13
  · exact point118slice14
  · exact point118slice15
  · exact point118slice16
  · exact point118slice17
  · exact point118slice18
  · exact point118slice19
  · exact point118slice20
  · exact point118slice21
  · exact point118slice22
  · exact point118slice23
  · exact point118slice24
  · exact point118slice25
  · exact point118slice26
  · exact point118slice27
  · exact point118slice28
  · exact point118slice29
  · exact point118slice30
  · exact point118slice31
  · exact point118slice32
  · exact point118slice33
  · exact point118slice34
  · exact point118slice35
  · exact point118slice36
  · exact point118slice37
  · exact point118slice38
  · exact point118slice39
  · exact point118slice40
  · exact point118slice41
  · exact point118slice42
  · exact point118slice43
  · exact point118slice44
  · exact point118slice45
  · exact point118slice46
  · exact point118slice47
  · exact point118slice48
  · exact point118slice49
  · exact point118slice50
  · exact point118slice51
  · exact point118slice52
  · exact point118slice53
  · exact point118slice54
  · exact point118slice55
  · exact point118slice56
  · exact point118slice57
  · exact point118slice58
  · exact point118slice59
  · exact point118slice60
  · exact point118slice61
  · exact point118slice62
  · exact point118slice63
  · exact point118slice64
  · exact point118slice65
  · exact point118slice66
  · exact point118slice67
  · exact point118slice68
  · exact point118slice69
  · exact point118slice70
  · exact point118slice71
  · exact point118slice72
  · exact point118slice73
  · exact point118slice74
  · exact point118slice75
  · exact point118slice76
  · exact point118slice77
  · exact point118slice78
  · exact point118slice79
  · exact point118slice80
  · exact point118slice81
  · exact point118slice82
  · exact point118slice83
  · exact point118slice84
  · exact point118slice85
  · exact point118slice86
  · exact point118slice87
  · exact point118slice88
  · exact point118slice89
  · exact point118slice90
  · exact point118slice91
  · exact point118slice92
  · exact point118slice93
  · exact point118slice94
  · exact point118slice95
  · exact point118slice96
  · exact point118slice97
  · exact point118slice98
  · exact point118slice99
  · exact point118slice100
  · exact point118slice101
  · exact point118slice102
  · exact point118slice103
  · exact point118slice104
  · exact point118slice105
  · exact point118slice106
  · exact point118slice107
  · exact point118slice108
  · exact point118slice109
  · exact point118slice110
  · exact point118slice111
  · exact point118slice112
  · exact point118slice113
  · exact point118slice114
  · exact point118slice115
  · exact point118slice116
  · exact point118slice117
  · exact point118slice118
  · exact point118slice119
  · exact point118slice120
  · exact point118slice121
  · exact point118slice122
  · exact point118slice123
  · exact point118slice124
  · exact point118slice125
  · exact point118slice126
  · exact point118slice127
  · exact point118slice128
  · exact point118slice129
  · exact point118slice130
  · exact point118slice131
  · exact point118slice132
  · exact point118slice133
  · exact point118slice134
  · exact point118slice135
  · exact point118slice136
  · exact point118slice137
  · exact point118slice138
  · exact point118slice139
  · exact point118slice140
  · exact point118slice141
  · exact point118slice142
  · exact point118slice143
  · exact point118slice144
  · exact point118slice145
  · exact point118slice146
  · exact point118slice147
  · exact point118slice148
  · exact point118slice149
  · exact point118slice150
  · exact point118slice151
  · exact point118slice152
  · exact point118slice153
  · exact point118slice154
  · exact point118slice155
  · exact point118slice156
  · exact point118slice157
  · exact point118slice158
  · exact point118slice159
  · exact point118slice160
  · exact point118slice161
  · exact point118slice162
  · exact point118slice163
  · exact point118slice164
  · exact point118slice165
  · exact point118slice166
  · exact point118slice167
  · exact point118slice168
  · exact point118slice169
  · exact point118slice170
  · exact point118slice171
  · exact point118slice172
  · exact point118slice173
  · exact point118slice174
  · exact point118slice175
  · exact point118slice176
  · exact point118slice177
  · exact point118slice178
  · exact point118slice179
  · exact point118slice180
  · exact point118slice181
  · exact point118slice182
  · exact point118slice183
  · exact point118slice184
  · exact point118slice185
  · exact point118slice186
  · exact point118slice187
  · exact point118slice188
  · exact point118slice189
  · exact point118slice190
  · exact point118slice191
  · exact point118slice192
  · exact point118slice193
  · exact point118slice194
  · exact point118slice195
  · exact point118slice196
  · exact point118slice197
  · exact point118slice198
  · exact point118slice199
  · exact point118slice200
  · exact point118slice201
  · exact point118slice202

set_option maxHeartbeats 1600000 in
public theorem point118 : stepCheck 0 2579 := by
  have hleft : L0Gen 0 * L0Rep 2579 = leftPerm118 := by
    change L0Gen 0 * evalWord L0Gen [1, 0, 3, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] = leftPerm118
    simp only [leftPerm118, p102, p80, p67, p50, p48, p20, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2579) * evalWord L1Gen (L0Factor 0 2579) = rightPerm118 := by
    change evalWord L0Gen [1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 1, 0, 3] * evalWord L1Gen [0, 1, 1, 0, 1, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3] = rightPerm118
    simp only [rightPerm118, p121, p87, p75, p60, p58, p48, p42, p39, p38, p37, p33, p30, p29, p28, p27, p26, p25, p24, p23, p18, p17, p16, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2579) x =
    (L0Rep (L0Act 0 2579) * evalWord L1Gen (L0Factor 0 2579)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap118_eq, ← rightMap118_eq]
  exact Residual1Cache.ofSlices point118_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
