module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level12Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level15Part1
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 123

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap123 (x : Nat) : Nat := force t645 (t80 x)
private def leftPerm123 : Equiv.Perm (Fin 4060) := p645 * (p80)
private theorem leftMap123_eq (x : Fin 4060) :
    leftMap123 x.val = (leftPerm123 x).val := (compose (t := fun x => force t645 (t80 x)) (a := t645) (b := fun x => t80 x) (fun _ => rfl) c645 c80) x

private def rightMap123 (x : Nat) : Nat := force t100 (force t140 (force t0 (force t493 (force t653 (force t12 (force t147 (force t55 (force t511 (t56 x)))))))))
private def rightPerm123 : Equiv.Perm (Fin 4060) := p100 * (p140 * (p0 * (p493 * (p653 * (p12 * (p147 * (p55 * (p511 * (p56)))))))))
private theorem rightMap123_eq (x : Fin 4060) :
    rightMap123 x.val = (rightPerm123 x).val := (compose (t := fun x => force t100 (force t140 (force t0 (force t493 (force t653 (force t12 (force t147 (force t55 (force t511 (t56 x)))))))))) (a := t100) (b := fun x => force t140 (force t0 (force t493 (force t653 (force t12 (force t147 (force t55 (force t511 (t56 x))))))))) (fun _ => rfl) c100 (compose (t := fun x => force t140 (force t0 (force t493 (force t653 (force t12 (force t147 (force t55 (force t511 (t56 x))))))))) (a := t140) (b := fun x => force t0 (force t493 (force t653 (force t12 (force t147 (force t55 (force t511 (t56 x)))))))) (fun _ => rfl) c140 (compose (t := fun x => force t0 (force t493 (force t653 (force t12 (force t147 (force t55 (force t511 (t56 x)))))))) (a := t0) (b := fun x => force t493 (force t653 (force t12 (force t147 (force t55 (force t511 (t56 x))))))) (fun _ => rfl) c0 (compose (t := fun x => force t493 (force t653 (force t12 (force t147 (force t55 (force t511 (t56 x))))))) (a := t493) (b := fun x => force t653 (force t12 (force t147 (force t55 (force t511 (t56 x)))))) (fun _ => rfl) c493 (compose (t := fun x => force t653 (force t12 (force t147 (force t55 (force t511 (t56 x)))))) (a := t653) (b := fun x => force t12 (force t147 (force t55 (force t511 (t56 x))))) (fun _ => rfl) c653 (compose (t := fun x => force t12 (force t147 (force t55 (force t511 (t56 x))))) (a := t12) (b := fun x => force t147 (force t55 (force t511 (t56 x)))) (fun _ => rfl) c12 (compose (t := fun x => force t147 (force t55 (force t511 (t56 x)))) (a := t147) (b := fun x => force t55 (force t511 (t56 x))) (fun _ => rfl) c147 (compose (t := fun x => force t55 (force t511 (t56 x))) (a := t55) (b := fun x => force t511 (t56 x)) (fun _ => rfl) c55 (compose (t := fun x => force t511 (t56 x)) (a := t511) (b := fun x => t56 x) (fun _ => rfl) c511 c56))))))))) x

set_option maxHeartbeats 1600000 in
private theorem point123slice0 : Residual1Cache.slice leftMap123 rightMap123 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice1 : Residual1Cache.slice leftMap123 rightMap123 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice2 : Residual1Cache.slice leftMap123 rightMap123 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice3 : Residual1Cache.slice leftMap123 rightMap123 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice4 : Residual1Cache.slice leftMap123 rightMap123 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice5 : Residual1Cache.slice leftMap123 rightMap123 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice6 : Residual1Cache.slice leftMap123 rightMap123 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice7 : Residual1Cache.slice leftMap123 rightMap123 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice8 : Residual1Cache.slice leftMap123 rightMap123 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice9 : Residual1Cache.slice leftMap123 rightMap123 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice10 : Residual1Cache.slice leftMap123 rightMap123 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice11 : Residual1Cache.slice leftMap123 rightMap123 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice12 : Residual1Cache.slice leftMap123 rightMap123 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice13 : Residual1Cache.slice leftMap123 rightMap123 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice14 : Residual1Cache.slice leftMap123 rightMap123 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice15 : Residual1Cache.slice leftMap123 rightMap123 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice16 : Residual1Cache.slice leftMap123 rightMap123 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice17 : Residual1Cache.slice leftMap123 rightMap123 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice18 : Residual1Cache.slice leftMap123 rightMap123 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice19 : Residual1Cache.slice leftMap123 rightMap123 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice20 : Residual1Cache.slice leftMap123 rightMap123 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice21 : Residual1Cache.slice leftMap123 rightMap123 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice22 : Residual1Cache.slice leftMap123 rightMap123 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice23 : Residual1Cache.slice leftMap123 rightMap123 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice24 : Residual1Cache.slice leftMap123 rightMap123 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice25 : Residual1Cache.slice leftMap123 rightMap123 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice26 : Residual1Cache.slice leftMap123 rightMap123 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice27 : Residual1Cache.slice leftMap123 rightMap123 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice28 : Residual1Cache.slice leftMap123 rightMap123 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice29 : Residual1Cache.slice leftMap123 rightMap123 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice30 : Residual1Cache.slice leftMap123 rightMap123 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice31 : Residual1Cache.slice leftMap123 rightMap123 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice32 : Residual1Cache.slice leftMap123 rightMap123 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice33 : Residual1Cache.slice leftMap123 rightMap123 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice34 : Residual1Cache.slice leftMap123 rightMap123 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice35 : Residual1Cache.slice leftMap123 rightMap123 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice36 : Residual1Cache.slice leftMap123 rightMap123 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice37 : Residual1Cache.slice leftMap123 rightMap123 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice38 : Residual1Cache.slice leftMap123 rightMap123 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice39 : Residual1Cache.slice leftMap123 rightMap123 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice40 : Residual1Cache.slice leftMap123 rightMap123 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice41 : Residual1Cache.slice leftMap123 rightMap123 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice42 : Residual1Cache.slice leftMap123 rightMap123 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice43 : Residual1Cache.slice leftMap123 rightMap123 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice44 : Residual1Cache.slice leftMap123 rightMap123 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice45 : Residual1Cache.slice leftMap123 rightMap123 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice46 : Residual1Cache.slice leftMap123 rightMap123 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice47 : Residual1Cache.slice leftMap123 rightMap123 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice48 : Residual1Cache.slice leftMap123 rightMap123 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice49 : Residual1Cache.slice leftMap123 rightMap123 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice50 : Residual1Cache.slice leftMap123 rightMap123 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice51 : Residual1Cache.slice leftMap123 rightMap123 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice52 : Residual1Cache.slice leftMap123 rightMap123 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice53 : Residual1Cache.slice leftMap123 rightMap123 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice54 : Residual1Cache.slice leftMap123 rightMap123 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice55 : Residual1Cache.slice leftMap123 rightMap123 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice56 : Residual1Cache.slice leftMap123 rightMap123 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice57 : Residual1Cache.slice leftMap123 rightMap123 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice58 : Residual1Cache.slice leftMap123 rightMap123 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice59 : Residual1Cache.slice leftMap123 rightMap123 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice60 : Residual1Cache.slice leftMap123 rightMap123 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice61 : Residual1Cache.slice leftMap123 rightMap123 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice62 : Residual1Cache.slice leftMap123 rightMap123 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice63 : Residual1Cache.slice leftMap123 rightMap123 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice64 : Residual1Cache.slice leftMap123 rightMap123 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice65 : Residual1Cache.slice leftMap123 rightMap123 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice66 : Residual1Cache.slice leftMap123 rightMap123 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice67 : Residual1Cache.slice leftMap123 rightMap123 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice68 : Residual1Cache.slice leftMap123 rightMap123 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice69 : Residual1Cache.slice leftMap123 rightMap123 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice70 : Residual1Cache.slice leftMap123 rightMap123 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice71 : Residual1Cache.slice leftMap123 rightMap123 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice72 : Residual1Cache.slice leftMap123 rightMap123 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice73 : Residual1Cache.slice leftMap123 rightMap123 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice74 : Residual1Cache.slice leftMap123 rightMap123 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice75 : Residual1Cache.slice leftMap123 rightMap123 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice76 : Residual1Cache.slice leftMap123 rightMap123 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice77 : Residual1Cache.slice leftMap123 rightMap123 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice78 : Residual1Cache.slice leftMap123 rightMap123 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice79 : Residual1Cache.slice leftMap123 rightMap123 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice80 : Residual1Cache.slice leftMap123 rightMap123 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice81 : Residual1Cache.slice leftMap123 rightMap123 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice82 : Residual1Cache.slice leftMap123 rightMap123 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice83 : Residual1Cache.slice leftMap123 rightMap123 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice84 : Residual1Cache.slice leftMap123 rightMap123 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice85 : Residual1Cache.slice leftMap123 rightMap123 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice86 : Residual1Cache.slice leftMap123 rightMap123 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice87 : Residual1Cache.slice leftMap123 rightMap123 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice88 : Residual1Cache.slice leftMap123 rightMap123 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice89 : Residual1Cache.slice leftMap123 rightMap123 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice90 : Residual1Cache.slice leftMap123 rightMap123 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice91 : Residual1Cache.slice leftMap123 rightMap123 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice92 : Residual1Cache.slice leftMap123 rightMap123 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice93 : Residual1Cache.slice leftMap123 rightMap123 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice94 : Residual1Cache.slice leftMap123 rightMap123 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice95 : Residual1Cache.slice leftMap123 rightMap123 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice96 : Residual1Cache.slice leftMap123 rightMap123 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice97 : Residual1Cache.slice leftMap123 rightMap123 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice98 : Residual1Cache.slice leftMap123 rightMap123 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice99 : Residual1Cache.slice leftMap123 rightMap123 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice100 : Residual1Cache.slice leftMap123 rightMap123 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice101 : Residual1Cache.slice leftMap123 rightMap123 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice102 : Residual1Cache.slice leftMap123 rightMap123 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice103 : Residual1Cache.slice leftMap123 rightMap123 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice104 : Residual1Cache.slice leftMap123 rightMap123 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice105 : Residual1Cache.slice leftMap123 rightMap123 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice106 : Residual1Cache.slice leftMap123 rightMap123 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice107 : Residual1Cache.slice leftMap123 rightMap123 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice108 : Residual1Cache.slice leftMap123 rightMap123 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice109 : Residual1Cache.slice leftMap123 rightMap123 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice110 : Residual1Cache.slice leftMap123 rightMap123 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice111 : Residual1Cache.slice leftMap123 rightMap123 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice112 : Residual1Cache.slice leftMap123 rightMap123 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice113 : Residual1Cache.slice leftMap123 rightMap123 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice114 : Residual1Cache.slice leftMap123 rightMap123 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice115 : Residual1Cache.slice leftMap123 rightMap123 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice116 : Residual1Cache.slice leftMap123 rightMap123 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice117 : Residual1Cache.slice leftMap123 rightMap123 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice118 : Residual1Cache.slice leftMap123 rightMap123 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice119 : Residual1Cache.slice leftMap123 rightMap123 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice120 : Residual1Cache.slice leftMap123 rightMap123 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice121 : Residual1Cache.slice leftMap123 rightMap123 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice122 : Residual1Cache.slice leftMap123 rightMap123 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice123 : Residual1Cache.slice leftMap123 rightMap123 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice124 : Residual1Cache.slice leftMap123 rightMap123 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice125 : Residual1Cache.slice leftMap123 rightMap123 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice126 : Residual1Cache.slice leftMap123 rightMap123 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice127 : Residual1Cache.slice leftMap123 rightMap123 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice128 : Residual1Cache.slice leftMap123 rightMap123 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice129 : Residual1Cache.slice leftMap123 rightMap123 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice130 : Residual1Cache.slice leftMap123 rightMap123 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice131 : Residual1Cache.slice leftMap123 rightMap123 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice132 : Residual1Cache.slice leftMap123 rightMap123 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice133 : Residual1Cache.slice leftMap123 rightMap123 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice134 : Residual1Cache.slice leftMap123 rightMap123 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice135 : Residual1Cache.slice leftMap123 rightMap123 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice136 : Residual1Cache.slice leftMap123 rightMap123 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice137 : Residual1Cache.slice leftMap123 rightMap123 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice138 : Residual1Cache.slice leftMap123 rightMap123 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice139 : Residual1Cache.slice leftMap123 rightMap123 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice140 : Residual1Cache.slice leftMap123 rightMap123 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice141 : Residual1Cache.slice leftMap123 rightMap123 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice142 : Residual1Cache.slice leftMap123 rightMap123 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice143 : Residual1Cache.slice leftMap123 rightMap123 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice144 : Residual1Cache.slice leftMap123 rightMap123 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice145 : Residual1Cache.slice leftMap123 rightMap123 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice146 : Residual1Cache.slice leftMap123 rightMap123 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice147 : Residual1Cache.slice leftMap123 rightMap123 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice148 : Residual1Cache.slice leftMap123 rightMap123 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice149 : Residual1Cache.slice leftMap123 rightMap123 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice150 : Residual1Cache.slice leftMap123 rightMap123 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice151 : Residual1Cache.slice leftMap123 rightMap123 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice152 : Residual1Cache.slice leftMap123 rightMap123 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice153 : Residual1Cache.slice leftMap123 rightMap123 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice154 : Residual1Cache.slice leftMap123 rightMap123 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice155 : Residual1Cache.slice leftMap123 rightMap123 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice156 : Residual1Cache.slice leftMap123 rightMap123 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice157 : Residual1Cache.slice leftMap123 rightMap123 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice158 : Residual1Cache.slice leftMap123 rightMap123 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice159 : Residual1Cache.slice leftMap123 rightMap123 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice160 : Residual1Cache.slice leftMap123 rightMap123 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice161 : Residual1Cache.slice leftMap123 rightMap123 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice162 : Residual1Cache.slice leftMap123 rightMap123 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice163 : Residual1Cache.slice leftMap123 rightMap123 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice164 : Residual1Cache.slice leftMap123 rightMap123 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice165 : Residual1Cache.slice leftMap123 rightMap123 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice166 : Residual1Cache.slice leftMap123 rightMap123 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice167 : Residual1Cache.slice leftMap123 rightMap123 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice168 : Residual1Cache.slice leftMap123 rightMap123 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice169 : Residual1Cache.slice leftMap123 rightMap123 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice170 : Residual1Cache.slice leftMap123 rightMap123 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice171 : Residual1Cache.slice leftMap123 rightMap123 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice172 : Residual1Cache.slice leftMap123 rightMap123 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice173 : Residual1Cache.slice leftMap123 rightMap123 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice174 : Residual1Cache.slice leftMap123 rightMap123 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice175 : Residual1Cache.slice leftMap123 rightMap123 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice176 : Residual1Cache.slice leftMap123 rightMap123 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice177 : Residual1Cache.slice leftMap123 rightMap123 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice178 : Residual1Cache.slice leftMap123 rightMap123 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice179 : Residual1Cache.slice leftMap123 rightMap123 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice180 : Residual1Cache.slice leftMap123 rightMap123 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice181 : Residual1Cache.slice leftMap123 rightMap123 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice182 : Residual1Cache.slice leftMap123 rightMap123 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice183 : Residual1Cache.slice leftMap123 rightMap123 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice184 : Residual1Cache.slice leftMap123 rightMap123 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice185 : Residual1Cache.slice leftMap123 rightMap123 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice186 : Residual1Cache.slice leftMap123 rightMap123 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice187 : Residual1Cache.slice leftMap123 rightMap123 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice188 : Residual1Cache.slice leftMap123 rightMap123 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice189 : Residual1Cache.slice leftMap123 rightMap123 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice190 : Residual1Cache.slice leftMap123 rightMap123 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice191 : Residual1Cache.slice leftMap123 rightMap123 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice192 : Residual1Cache.slice leftMap123 rightMap123 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice193 : Residual1Cache.slice leftMap123 rightMap123 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice194 : Residual1Cache.slice leftMap123 rightMap123 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice195 : Residual1Cache.slice leftMap123 rightMap123 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice196 : Residual1Cache.slice leftMap123 rightMap123 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice197 : Residual1Cache.slice leftMap123 rightMap123 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice198 : Residual1Cache.slice leftMap123 rightMap123 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice199 : Residual1Cache.slice leftMap123 rightMap123 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice200 : Residual1Cache.slice leftMap123 rightMap123 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice201 : Residual1Cache.slice leftMap123 rightMap123 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point123slice202 : Residual1Cache.slice leftMap123 rightMap123 202 = true := by
  decide +kernel

private theorem point123_slices : ∀ c, Residual1Cache.slice leftMap123 rightMap123 c = true := by
  intro c
  fin_cases c
  · exact point123slice0
  · exact point123slice1
  · exact point123slice2
  · exact point123slice3
  · exact point123slice4
  · exact point123slice5
  · exact point123slice6
  · exact point123slice7
  · exact point123slice8
  · exact point123slice9
  · exact point123slice10
  · exact point123slice11
  · exact point123slice12
  · exact point123slice13
  · exact point123slice14
  · exact point123slice15
  · exact point123slice16
  · exact point123slice17
  · exact point123slice18
  · exact point123slice19
  · exact point123slice20
  · exact point123slice21
  · exact point123slice22
  · exact point123slice23
  · exact point123slice24
  · exact point123slice25
  · exact point123slice26
  · exact point123slice27
  · exact point123slice28
  · exact point123slice29
  · exact point123slice30
  · exact point123slice31
  · exact point123slice32
  · exact point123slice33
  · exact point123slice34
  · exact point123slice35
  · exact point123slice36
  · exact point123slice37
  · exact point123slice38
  · exact point123slice39
  · exact point123slice40
  · exact point123slice41
  · exact point123slice42
  · exact point123slice43
  · exact point123slice44
  · exact point123slice45
  · exact point123slice46
  · exact point123slice47
  · exact point123slice48
  · exact point123slice49
  · exact point123slice50
  · exact point123slice51
  · exact point123slice52
  · exact point123slice53
  · exact point123slice54
  · exact point123slice55
  · exact point123slice56
  · exact point123slice57
  · exact point123slice58
  · exact point123slice59
  · exact point123slice60
  · exact point123slice61
  · exact point123slice62
  · exact point123slice63
  · exact point123slice64
  · exact point123slice65
  · exact point123slice66
  · exact point123slice67
  · exact point123slice68
  · exact point123slice69
  · exact point123slice70
  · exact point123slice71
  · exact point123slice72
  · exact point123slice73
  · exact point123slice74
  · exact point123slice75
  · exact point123slice76
  · exact point123slice77
  · exact point123slice78
  · exact point123slice79
  · exact point123slice80
  · exact point123slice81
  · exact point123slice82
  · exact point123slice83
  · exact point123slice84
  · exact point123slice85
  · exact point123slice86
  · exact point123slice87
  · exact point123slice88
  · exact point123slice89
  · exact point123slice90
  · exact point123slice91
  · exact point123slice92
  · exact point123slice93
  · exact point123slice94
  · exact point123slice95
  · exact point123slice96
  · exact point123slice97
  · exact point123slice98
  · exact point123slice99
  · exact point123slice100
  · exact point123slice101
  · exact point123slice102
  · exact point123slice103
  · exact point123slice104
  · exact point123slice105
  · exact point123slice106
  · exact point123slice107
  · exact point123slice108
  · exact point123slice109
  · exact point123slice110
  · exact point123slice111
  · exact point123slice112
  · exact point123slice113
  · exact point123slice114
  · exact point123slice115
  · exact point123slice116
  · exact point123slice117
  · exact point123slice118
  · exact point123slice119
  · exact point123slice120
  · exact point123slice121
  · exact point123slice122
  · exact point123slice123
  · exact point123slice124
  · exact point123slice125
  · exact point123slice126
  · exact point123slice127
  · exact point123slice128
  · exact point123slice129
  · exact point123slice130
  · exact point123slice131
  · exact point123slice132
  · exact point123slice133
  · exact point123slice134
  · exact point123slice135
  · exact point123slice136
  · exact point123slice137
  · exact point123slice138
  · exact point123slice139
  · exact point123slice140
  · exact point123slice141
  · exact point123slice142
  · exact point123slice143
  · exact point123slice144
  · exact point123slice145
  · exact point123slice146
  · exact point123slice147
  · exact point123slice148
  · exact point123slice149
  · exact point123slice150
  · exact point123slice151
  · exact point123slice152
  · exact point123slice153
  · exact point123slice154
  · exact point123slice155
  · exact point123slice156
  · exact point123slice157
  · exact point123slice158
  · exact point123slice159
  · exact point123slice160
  · exact point123slice161
  · exact point123slice162
  · exact point123slice163
  · exact point123slice164
  · exact point123slice165
  · exact point123slice166
  · exact point123slice167
  · exact point123slice168
  · exact point123slice169
  · exact point123slice170
  · exact point123slice171
  · exact point123slice172
  · exact point123slice173
  · exact point123slice174
  · exact point123slice175
  · exact point123slice176
  · exact point123slice177
  · exact point123slice178
  · exact point123slice179
  · exact point123slice180
  · exact point123slice181
  · exact point123slice182
  · exact point123slice183
  · exact point123slice184
  · exact point123slice185
  · exact point123slice186
  · exact point123slice187
  · exact point123slice188
  · exact point123slice189
  · exact point123slice190
  · exact point123slice191
  · exact point123slice192
  · exact point123slice193
  · exact point123slice194
  · exact point123slice195
  · exact point123slice196
  · exact point123slice197
  · exact point123slice198
  · exact point123slice199
  · exact point123slice200
  · exact point123slice201
  · exact point123slice202

set_option maxHeartbeats 1600000 in
public theorem point123 : stepCheck 1 2574 := by
  have hleft : L0Gen 1 * L0Rep 2574 = leftPerm123 := by
    change L0Gen 1 * evalWord L0Gen [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] = leftPerm123
    simp only [leftPerm123, p645, p80, p73, p48, p20, p17, p11, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2574) * evalWord L1Gen (L0Factor 1 2574) = rightPerm123 := by
    change evalWord L0Gen [3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 1, 0] * evalWord L1Gen [2, 1, 1, 2, 1, 1, 0, 1, 0, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm123
    simp only [rightPerm123, p653, p511, p493, p147, p140, p139, p132, p110, p100, p99, p56, p55, p51, p49, p48, p47, p46, p45, p44, p43, p42, p41, p40, p39, p38, p37, p36, p35, p34, p33, p32, p31, p30, p29, p28, p27, p26, p25, p24, p23, p22, p21, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2574) x =
    (L0Rep (L0Act 1 2574) * evalWord L1Gen (L0Factor 1 2574)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap123_eq, ← rightMap123_eq]
  exact Residual1Cache.ofSlices point123_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
