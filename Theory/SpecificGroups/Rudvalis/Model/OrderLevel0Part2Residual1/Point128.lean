module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level15Part1
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 128

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap128 (x : Nat) : Nat := force t247 (t153 x)
private def leftPerm128 : Equiv.Perm (Fin 4060) := p247 * (p153)
private theorem leftMap128_eq (x : Fin 4060) :
    leftMap128 x.val = (leftPerm128 x).val := (compose (t := fun x => force t247 (t153 x)) (a := t247) (b := fun x => t153 x) (fun _ => rfl) c247 c153) x

private def rightMap128 (x : Nat) : Nat := force t206 (force t76 (force t160 (force t135 (force t95 (force t198 (force t33 (t511 x)))))))
private def rightPerm128 : Equiv.Perm (Fin 4060) := p206 * (p76 * (p160 * (p135 * (p95 * (p198 * (p33 * (p511)))))))
private theorem rightMap128_eq (x : Fin 4060) :
    rightMap128 x.val = (rightPerm128 x).val := (compose (t := fun x => force t206 (force t76 (force t160 (force t135 (force t95 (force t198 (force t33 (t511 x)))))))) (a := t206) (b := fun x => force t76 (force t160 (force t135 (force t95 (force t198 (force t33 (t511 x))))))) (fun _ => rfl) c206 (compose (t := fun x => force t76 (force t160 (force t135 (force t95 (force t198 (force t33 (t511 x))))))) (a := t76) (b := fun x => force t160 (force t135 (force t95 (force t198 (force t33 (t511 x)))))) (fun _ => rfl) c76 (compose (t := fun x => force t160 (force t135 (force t95 (force t198 (force t33 (t511 x)))))) (a := t160) (b := fun x => force t135 (force t95 (force t198 (force t33 (t511 x))))) (fun _ => rfl) c160 (compose (t := fun x => force t135 (force t95 (force t198 (force t33 (t511 x))))) (a := t135) (b := fun x => force t95 (force t198 (force t33 (t511 x)))) (fun _ => rfl) c135 (compose (t := fun x => force t95 (force t198 (force t33 (t511 x)))) (a := t95) (b := fun x => force t198 (force t33 (t511 x))) (fun _ => rfl) c95 (compose (t := fun x => force t198 (force t33 (t511 x))) (a := t198) (b := fun x => force t33 (t511 x)) (fun _ => rfl) c198 (compose (t := fun x => force t33 (t511 x)) (a := t33) (b := fun x => t511 x) (fun _ => rfl) c33 c511))))))) x

set_option maxHeartbeats 1600000 in
private theorem point128slice0 : Residual1Cache.slice leftMap128 rightMap128 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice1 : Residual1Cache.slice leftMap128 rightMap128 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice2 : Residual1Cache.slice leftMap128 rightMap128 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice3 : Residual1Cache.slice leftMap128 rightMap128 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice4 : Residual1Cache.slice leftMap128 rightMap128 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice5 : Residual1Cache.slice leftMap128 rightMap128 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice6 : Residual1Cache.slice leftMap128 rightMap128 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice7 : Residual1Cache.slice leftMap128 rightMap128 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice8 : Residual1Cache.slice leftMap128 rightMap128 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice9 : Residual1Cache.slice leftMap128 rightMap128 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice10 : Residual1Cache.slice leftMap128 rightMap128 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice11 : Residual1Cache.slice leftMap128 rightMap128 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice12 : Residual1Cache.slice leftMap128 rightMap128 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice13 : Residual1Cache.slice leftMap128 rightMap128 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice14 : Residual1Cache.slice leftMap128 rightMap128 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice15 : Residual1Cache.slice leftMap128 rightMap128 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice16 : Residual1Cache.slice leftMap128 rightMap128 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice17 : Residual1Cache.slice leftMap128 rightMap128 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice18 : Residual1Cache.slice leftMap128 rightMap128 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice19 : Residual1Cache.slice leftMap128 rightMap128 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice20 : Residual1Cache.slice leftMap128 rightMap128 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice21 : Residual1Cache.slice leftMap128 rightMap128 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice22 : Residual1Cache.slice leftMap128 rightMap128 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice23 : Residual1Cache.slice leftMap128 rightMap128 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice24 : Residual1Cache.slice leftMap128 rightMap128 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice25 : Residual1Cache.slice leftMap128 rightMap128 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice26 : Residual1Cache.slice leftMap128 rightMap128 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice27 : Residual1Cache.slice leftMap128 rightMap128 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice28 : Residual1Cache.slice leftMap128 rightMap128 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice29 : Residual1Cache.slice leftMap128 rightMap128 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice30 : Residual1Cache.slice leftMap128 rightMap128 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice31 : Residual1Cache.slice leftMap128 rightMap128 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice32 : Residual1Cache.slice leftMap128 rightMap128 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice33 : Residual1Cache.slice leftMap128 rightMap128 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice34 : Residual1Cache.slice leftMap128 rightMap128 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice35 : Residual1Cache.slice leftMap128 rightMap128 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice36 : Residual1Cache.slice leftMap128 rightMap128 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice37 : Residual1Cache.slice leftMap128 rightMap128 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice38 : Residual1Cache.slice leftMap128 rightMap128 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice39 : Residual1Cache.slice leftMap128 rightMap128 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice40 : Residual1Cache.slice leftMap128 rightMap128 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice41 : Residual1Cache.slice leftMap128 rightMap128 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice42 : Residual1Cache.slice leftMap128 rightMap128 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice43 : Residual1Cache.slice leftMap128 rightMap128 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice44 : Residual1Cache.slice leftMap128 rightMap128 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice45 : Residual1Cache.slice leftMap128 rightMap128 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice46 : Residual1Cache.slice leftMap128 rightMap128 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice47 : Residual1Cache.slice leftMap128 rightMap128 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice48 : Residual1Cache.slice leftMap128 rightMap128 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice49 : Residual1Cache.slice leftMap128 rightMap128 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice50 : Residual1Cache.slice leftMap128 rightMap128 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice51 : Residual1Cache.slice leftMap128 rightMap128 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice52 : Residual1Cache.slice leftMap128 rightMap128 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice53 : Residual1Cache.slice leftMap128 rightMap128 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice54 : Residual1Cache.slice leftMap128 rightMap128 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice55 : Residual1Cache.slice leftMap128 rightMap128 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice56 : Residual1Cache.slice leftMap128 rightMap128 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice57 : Residual1Cache.slice leftMap128 rightMap128 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice58 : Residual1Cache.slice leftMap128 rightMap128 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice59 : Residual1Cache.slice leftMap128 rightMap128 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice60 : Residual1Cache.slice leftMap128 rightMap128 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice61 : Residual1Cache.slice leftMap128 rightMap128 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice62 : Residual1Cache.slice leftMap128 rightMap128 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice63 : Residual1Cache.slice leftMap128 rightMap128 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice64 : Residual1Cache.slice leftMap128 rightMap128 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice65 : Residual1Cache.slice leftMap128 rightMap128 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice66 : Residual1Cache.slice leftMap128 rightMap128 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice67 : Residual1Cache.slice leftMap128 rightMap128 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice68 : Residual1Cache.slice leftMap128 rightMap128 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice69 : Residual1Cache.slice leftMap128 rightMap128 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice70 : Residual1Cache.slice leftMap128 rightMap128 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice71 : Residual1Cache.slice leftMap128 rightMap128 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice72 : Residual1Cache.slice leftMap128 rightMap128 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice73 : Residual1Cache.slice leftMap128 rightMap128 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice74 : Residual1Cache.slice leftMap128 rightMap128 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice75 : Residual1Cache.slice leftMap128 rightMap128 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice76 : Residual1Cache.slice leftMap128 rightMap128 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice77 : Residual1Cache.slice leftMap128 rightMap128 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice78 : Residual1Cache.slice leftMap128 rightMap128 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice79 : Residual1Cache.slice leftMap128 rightMap128 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice80 : Residual1Cache.slice leftMap128 rightMap128 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice81 : Residual1Cache.slice leftMap128 rightMap128 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice82 : Residual1Cache.slice leftMap128 rightMap128 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice83 : Residual1Cache.slice leftMap128 rightMap128 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice84 : Residual1Cache.slice leftMap128 rightMap128 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice85 : Residual1Cache.slice leftMap128 rightMap128 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice86 : Residual1Cache.slice leftMap128 rightMap128 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice87 : Residual1Cache.slice leftMap128 rightMap128 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice88 : Residual1Cache.slice leftMap128 rightMap128 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice89 : Residual1Cache.slice leftMap128 rightMap128 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice90 : Residual1Cache.slice leftMap128 rightMap128 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice91 : Residual1Cache.slice leftMap128 rightMap128 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice92 : Residual1Cache.slice leftMap128 rightMap128 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice93 : Residual1Cache.slice leftMap128 rightMap128 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice94 : Residual1Cache.slice leftMap128 rightMap128 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice95 : Residual1Cache.slice leftMap128 rightMap128 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice96 : Residual1Cache.slice leftMap128 rightMap128 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice97 : Residual1Cache.slice leftMap128 rightMap128 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice98 : Residual1Cache.slice leftMap128 rightMap128 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice99 : Residual1Cache.slice leftMap128 rightMap128 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice100 : Residual1Cache.slice leftMap128 rightMap128 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice101 : Residual1Cache.slice leftMap128 rightMap128 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice102 : Residual1Cache.slice leftMap128 rightMap128 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice103 : Residual1Cache.slice leftMap128 rightMap128 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice104 : Residual1Cache.slice leftMap128 rightMap128 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice105 : Residual1Cache.slice leftMap128 rightMap128 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice106 : Residual1Cache.slice leftMap128 rightMap128 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice107 : Residual1Cache.slice leftMap128 rightMap128 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice108 : Residual1Cache.slice leftMap128 rightMap128 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice109 : Residual1Cache.slice leftMap128 rightMap128 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice110 : Residual1Cache.slice leftMap128 rightMap128 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice111 : Residual1Cache.slice leftMap128 rightMap128 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice112 : Residual1Cache.slice leftMap128 rightMap128 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice113 : Residual1Cache.slice leftMap128 rightMap128 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice114 : Residual1Cache.slice leftMap128 rightMap128 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice115 : Residual1Cache.slice leftMap128 rightMap128 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice116 : Residual1Cache.slice leftMap128 rightMap128 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice117 : Residual1Cache.slice leftMap128 rightMap128 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice118 : Residual1Cache.slice leftMap128 rightMap128 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice119 : Residual1Cache.slice leftMap128 rightMap128 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice120 : Residual1Cache.slice leftMap128 rightMap128 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice121 : Residual1Cache.slice leftMap128 rightMap128 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice122 : Residual1Cache.slice leftMap128 rightMap128 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice123 : Residual1Cache.slice leftMap128 rightMap128 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice124 : Residual1Cache.slice leftMap128 rightMap128 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice125 : Residual1Cache.slice leftMap128 rightMap128 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice126 : Residual1Cache.slice leftMap128 rightMap128 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice127 : Residual1Cache.slice leftMap128 rightMap128 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice128 : Residual1Cache.slice leftMap128 rightMap128 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice129 : Residual1Cache.slice leftMap128 rightMap128 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice130 : Residual1Cache.slice leftMap128 rightMap128 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice131 : Residual1Cache.slice leftMap128 rightMap128 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice132 : Residual1Cache.slice leftMap128 rightMap128 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice133 : Residual1Cache.slice leftMap128 rightMap128 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice134 : Residual1Cache.slice leftMap128 rightMap128 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice135 : Residual1Cache.slice leftMap128 rightMap128 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice136 : Residual1Cache.slice leftMap128 rightMap128 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice137 : Residual1Cache.slice leftMap128 rightMap128 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice138 : Residual1Cache.slice leftMap128 rightMap128 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice139 : Residual1Cache.slice leftMap128 rightMap128 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice140 : Residual1Cache.slice leftMap128 rightMap128 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice141 : Residual1Cache.slice leftMap128 rightMap128 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice142 : Residual1Cache.slice leftMap128 rightMap128 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice143 : Residual1Cache.slice leftMap128 rightMap128 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice144 : Residual1Cache.slice leftMap128 rightMap128 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice145 : Residual1Cache.slice leftMap128 rightMap128 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice146 : Residual1Cache.slice leftMap128 rightMap128 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice147 : Residual1Cache.slice leftMap128 rightMap128 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice148 : Residual1Cache.slice leftMap128 rightMap128 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice149 : Residual1Cache.slice leftMap128 rightMap128 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice150 : Residual1Cache.slice leftMap128 rightMap128 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice151 : Residual1Cache.slice leftMap128 rightMap128 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice152 : Residual1Cache.slice leftMap128 rightMap128 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice153 : Residual1Cache.slice leftMap128 rightMap128 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice154 : Residual1Cache.slice leftMap128 rightMap128 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice155 : Residual1Cache.slice leftMap128 rightMap128 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice156 : Residual1Cache.slice leftMap128 rightMap128 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice157 : Residual1Cache.slice leftMap128 rightMap128 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice158 : Residual1Cache.slice leftMap128 rightMap128 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice159 : Residual1Cache.slice leftMap128 rightMap128 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice160 : Residual1Cache.slice leftMap128 rightMap128 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice161 : Residual1Cache.slice leftMap128 rightMap128 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice162 : Residual1Cache.slice leftMap128 rightMap128 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice163 : Residual1Cache.slice leftMap128 rightMap128 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice164 : Residual1Cache.slice leftMap128 rightMap128 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice165 : Residual1Cache.slice leftMap128 rightMap128 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice166 : Residual1Cache.slice leftMap128 rightMap128 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice167 : Residual1Cache.slice leftMap128 rightMap128 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice168 : Residual1Cache.slice leftMap128 rightMap128 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice169 : Residual1Cache.slice leftMap128 rightMap128 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice170 : Residual1Cache.slice leftMap128 rightMap128 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice171 : Residual1Cache.slice leftMap128 rightMap128 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice172 : Residual1Cache.slice leftMap128 rightMap128 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice173 : Residual1Cache.slice leftMap128 rightMap128 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice174 : Residual1Cache.slice leftMap128 rightMap128 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice175 : Residual1Cache.slice leftMap128 rightMap128 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice176 : Residual1Cache.slice leftMap128 rightMap128 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice177 : Residual1Cache.slice leftMap128 rightMap128 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice178 : Residual1Cache.slice leftMap128 rightMap128 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice179 : Residual1Cache.slice leftMap128 rightMap128 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice180 : Residual1Cache.slice leftMap128 rightMap128 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice181 : Residual1Cache.slice leftMap128 rightMap128 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice182 : Residual1Cache.slice leftMap128 rightMap128 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice183 : Residual1Cache.slice leftMap128 rightMap128 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice184 : Residual1Cache.slice leftMap128 rightMap128 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice185 : Residual1Cache.slice leftMap128 rightMap128 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice186 : Residual1Cache.slice leftMap128 rightMap128 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice187 : Residual1Cache.slice leftMap128 rightMap128 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice188 : Residual1Cache.slice leftMap128 rightMap128 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice189 : Residual1Cache.slice leftMap128 rightMap128 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice190 : Residual1Cache.slice leftMap128 rightMap128 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice191 : Residual1Cache.slice leftMap128 rightMap128 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice192 : Residual1Cache.slice leftMap128 rightMap128 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice193 : Residual1Cache.slice leftMap128 rightMap128 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice194 : Residual1Cache.slice leftMap128 rightMap128 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice195 : Residual1Cache.slice leftMap128 rightMap128 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice196 : Residual1Cache.slice leftMap128 rightMap128 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice197 : Residual1Cache.slice leftMap128 rightMap128 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice198 : Residual1Cache.slice leftMap128 rightMap128 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice199 : Residual1Cache.slice leftMap128 rightMap128 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice200 : Residual1Cache.slice leftMap128 rightMap128 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice201 : Residual1Cache.slice leftMap128 rightMap128 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point128slice202 : Residual1Cache.slice leftMap128 rightMap128 202 = true := by
  decide +kernel

private theorem point128_slices : ∀ c, Residual1Cache.slice leftMap128 rightMap128 c = true := by
  intro c
  fin_cases c
  · exact point128slice0
  · exact point128slice1
  · exact point128slice2
  · exact point128slice3
  · exact point128slice4
  · exact point128slice5
  · exact point128slice6
  · exact point128slice7
  · exact point128slice8
  · exact point128slice9
  · exact point128slice10
  · exact point128slice11
  · exact point128slice12
  · exact point128slice13
  · exact point128slice14
  · exact point128slice15
  · exact point128slice16
  · exact point128slice17
  · exact point128slice18
  · exact point128slice19
  · exact point128slice20
  · exact point128slice21
  · exact point128slice22
  · exact point128slice23
  · exact point128slice24
  · exact point128slice25
  · exact point128slice26
  · exact point128slice27
  · exact point128slice28
  · exact point128slice29
  · exact point128slice30
  · exact point128slice31
  · exact point128slice32
  · exact point128slice33
  · exact point128slice34
  · exact point128slice35
  · exact point128slice36
  · exact point128slice37
  · exact point128slice38
  · exact point128slice39
  · exact point128slice40
  · exact point128slice41
  · exact point128slice42
  · exact point128slice43
  · exact point128slice44
  · exact point128slice45
  · exact point128slice46
  · exact point128slice47
  · exact point128slice48
  · exact point128slice49
  · exact point128slice50
  · exact point128slice51
  · exact point128slice52
  · exact point128slice53
  · exact point128slice54
  · exact point128slice55
  · exact point128slice56
  · exact point128slice57
  · exact point128slice58
  · exact point128slice59
  · exact point128slice60
  · exact point128slice61
  · exact point128slice62
  · exact point128slice63
  · exact point128slice64
  · exact point128slice65
  · exact point128slice66
  · exact point128slice67
  · exact point128slice68
  · exact point128slice69
  · exact point128slice70
  · exact point128slice71
  · exact point128slice72
  · exact point128slice73
  · exact point128slice74
  · exact point128slice75
  · exact point128slice76
  · exact point128slice77
  · exact point128slice78
  · exact point128slice79
  · exact point128slice80
  · exact point128slice81
  · exact point128slice82
  · exact point128slice83
  · exact point128slice84
  · exact point128slice85
  · exact point128slice86
  · exact point128slice87
  · exact point128slice88
  · exact point128slice89
  · exact point128slice90
  · exact point128slice91
  · exact point128slice92
  · exact point128slice93
  · exact point128slice94
  · exact point128slice95
  · exact point128slice96
  · exact point128slice97
  · exact point128slice98
  · exact point128slice99
  · exact point128slice100
  · exact point128slice101
  · exact point128slice102
  · exact point128slice103
  · exact point128slice104
  · exact point128slice105
  · exact point128slice106
  · exact point128slice107
  · exact point128slice108
  · exact point128slice109
  · exact point128slice110
  · exact point128slice111
  · exact point128slice112
  · exact point128slice113
  · exact point128slice114
  · exact point128slice115
  · exact point128slice116
  · exact point128slice117
  · exact point128slice118
  · exact point128slice119
  · exact point128slice120
  · exact point128slice121
  · exact point128slice122
  · exact point128slice123
  · exact point128slice124
  · exact point128slice125
  · exact point128slice126
  · exact point128slice127
  · exact point128slice128
  · exact point128slice129
  · exact point128slice130
  · exact point128slice131
  · exact point128slice132
  · exact point128slice133
  · exact point128slice134
  · exact point128slice135
  · exact point128slice136
  · exact point128slice137
  · exact point128slice138
  · exact point128slice139
  · exact point128slice140
  · exact point128slice141
  · exact point128slice142
  · exact point128slice143
  · exact point128slice144
  · exact point128slice145
  · exact point128slice146
  · exact point128slice147
  · exact point128slice148
  · exact point128slice149
  · exact point128slice150
  · exact point128slice151
  · exact point128slice152
  · exact point128slice153
  · exact point128slice154
  · exact point128slice155
  · exact point128slice156
  · exact point128slice157
  · exact point128slice158
  · exact point128slice159
  · exact point128slice160
  · exact point128slice161
  · exact point128slice162
  · exact point128slice163
  · exact point128slice164
  · exact point128slice165
  · exact point128slice166
  · exact point128slice167
  · exact point128slice168
  · exact point128slice169
  · exact point128slice170
  · exact point128slice171
  · exact point128slice172
  · exact point128slice173
  · exact point128slice174
  · exact point128slice175
  · exact point128slice176
  · exact point128slice177
  · exact point128slice178
  · exact point128slice179
  · exact point128slice180
  · exact point128slice181
  · exact point128slice182
  · exact point128slice183
  · exact point128slice184
  · exact point128slice185
  · exact point128slice186
  · exact point128slice187
  · exact point128slice188
  · exact point128slice189
  · exact point128slice190
  · exact point128slice191
  · exact point128slice192
  · exact point128slice193
  · exact point128slice194
  · exact point128slice195
  · exact point128slice196
  · exact point128slice197
  · exact point128slice198
  · exact point128slice199
  · exact point128slice200
  · exact point128slice201
  · exact point128slice202

set_option maxHeartbeats 1600000 in
public theorem point128 : stepCheck 0 2700 := by
  have hleft : L0Gen 0 * L0Rep 2700 = leftPerm128 := by
    change L0Gen 0 * evalWord L0Gen [1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3] = leftPerm128
    simp only [leftPerm128, p247, p153, p92, p67, p54, p30, p20, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2700) * evalWord L1Gen (L0Factor 0 2700) = rightPerm128 := by
    change evalWord L0Gen [1, 0, 3, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3] * evalWord L1Gen [2, 3, 2, 1, 0, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm128
    simp only [rightPerm128, p511, p206, p198, p160, p139, p135, p110, p99, p95, p76, p63, p60, p55, p51, p49, p47, p46, p45, p44, p43, p42, p41, p40, p39, p38, p37, p36, p35, p34, p33, p32, p31, p29, p28, p27, p26, p25, p24, p23, p22, p21, p20, p19, p18, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2700) x =
    (L0Rep (L0Act 0 2700) * evalWord L1Gen (L0Factor 0 2700)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap128_eq, ← rightMap128_eq]
  exact Residual1Cache.ofSlices point128_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
