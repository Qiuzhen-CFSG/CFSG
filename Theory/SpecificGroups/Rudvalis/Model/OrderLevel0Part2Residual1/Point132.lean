module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level14Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 132

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap132 (x : Nat) : Nat := force t166 (force t121 (force t0 (t3 x)))
private def leftPerm132 : Equiv.Perm (Fin 4060) := p166 * (p121 * (p0 * (p3)))
private theorem leftMap132_eq (x : Fin 4060) :
    leftMap132 x.val = (leftPerm132 x).val := (compose (t := fun x => force t166 (force t121 (force t0 (t3 x)))) (a := t166) (b := fun x => force t121 (force t0 (t3 x))) (fun _ => rfl) c166 (compose (t := fun x => force t121 (force t0 (t3 x))) (a := t121) (b := fun x => force t0 (t3 x)) (fun _ => rfl) c121 (compose (t := fun x => force t0 (t3 x)) (a := t0) (b := fun x => t3 x) (fun _ => rfl) c0 c3))) x

private def rightMap132 (x : Nat) : Nat := force t712 (force t80 (force t731 (force t8 (force t259 (force t128 (force t26 (t288 x)))))))
private def rightPerm132 : Equiv.Perm (Fin 4060) := p712 * (p80 * (p731 * (p8 * (p259 * (p128 * (p26 * (p288)))))))
private theorem rightMap132_eq (x : Fin 4060) :
    rightMap132 x.val = (rightPerm132 x).val := (compose (t := fun x => force t712 (force t80 (force t731 (force t8 (force t259 (force t128 (force t26 (t288 x)))))))) (a := t712) (b := fun x => force t80 (force t731 (force t8 (force t259 (force t128 (force t26 (t288 x))))))) (fun _ => rfl) c712 (compose (t := fun x => force t80 (force t731 (force t8 (force t259 (force t128 (force t26 (t288 x))))))) (a := t80) (b := fun x => force t731 (force t8 (force t259 (force t128 (force t26 (t288 x)))))) (fun _ => rfl) c80 (compose (t := fun x => force t731 (force t8 (force t259 (force t128 (force t26 (t288 x)))))) (a := t731) (b := fun x => force t8 (force t259 (force t128 (force t26 (t288 x))))) (fun _ => rfl) c731 (compose (t := fun x => force t8 (force t259 (force t128 (force t26 (t288 x))))) (a := t8) (b := fun x => force t259 (force t128 (force t26 (t288 x)))) (fun _ => rfl) c8 (compose (t := fun x => force t259 (force t128 (force t26 (t288 x)))) (a := t259) (b := fun x => force t128 (force t26 (t288 x))) (fun _ => rfl) c259 (compose (t := fun x => force t128 (force t26 (t288 x))) (a := t128) (b := fun x => force t26 (t288 x)) (fun _ => rfl) c128 (compose (t := fun x => force t26 (t288 x)) (a := t26) (b := fun x => t288 x) (fun _ => rfl) c26 c288))))))) x

set_option maxHeartbeats 1600000 in
private theorem point132slice0 : Residual1Cache.slice leftMap132 rightMap132 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice1 : Residual1Cache.slice leftMap132 rightMap132 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice2 : Residual1Cache.slice leftMap132 rightMap132 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice3 : Residual1Cache.slice leftMap132 rightMap132 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice4 : Residual1Cache.slice leftMap132 rightMap132 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice5 : Residual1Cache.slice leftMap132 rightMap132 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice6 : Residual1Cache.slice leftMap132 rightMap132 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice7 : Residual1Cache.slice leftMap132 rightMap132 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice8 : Residual1Cache.slice leftMap132 rightMap132 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice9 : Residual1Cache.slice leftMap132 rightMap132 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice10 : Residual1Cache.slice leftMap132 rightMap132 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice11 : Residual1Cache.slice leftMap132 rightMap132 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice12 : Residual1Cache.slice leftMap132 rightMap132 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice13 : Residual1Cache.slice leftMap132 rightMap132 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice14 : Residual1Cache.slice leftMap132 rightMap132 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice15 : Residual1Cache.slice leftMap132 rightMap132 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice16 : Residual1Cache.slice leftMap132 rightMap132 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice17 : Residual1Cache.slice leftMap132 rightMap132 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice18 : Residual1Cache.slice leftMap132 rightMap132 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice19 : Residual1Cache.slice leftMap132 rightMap132 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice20 : Residual1Cache.slice leftMap132 rightMap132 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice21 : Residual1Cache.slice leftMap132 rightMap132 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice22 : Residual1Cache.slice leftMap132 rightMap132 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice23 : Residual1Cache.slice leftMap132 rightMap132 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice24 : Residual1Cache.slice leftMap132 rightMap132 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice25 : Residual1Cache.slice leftMap132 rightMap132 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice26 : Residual1Cache.slice leftMap132 rightMap132 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice27 : Residual1Cache.slice leftMap132 rightMap132 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice28 : Residual1Cache.slice leftMap132 rightMap132 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice29 : Residual1Cache.slice leftMap132 rightMap132 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice30 : Residual1Cache.slice leftMap132 rightMap132 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice31 : Residual1Cache.slice leftMap132 rightMap132 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice32 : Residual1Cache.slice leftMap132 rightMap132 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice33 : Residual1Cache.slice leftMap132 rightMap132 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice34 : Residual1Cache.slice leftMap132 rightMap132 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice35 : Residual1Cache.slice leftMap132 rightMap132 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice36 : Residual1Cache.slice leftMap132 rightMap132 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice37 : Residual1Cache.slice leftMap132 rightMap132 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice38 : Residual1Cache.slice leftMap132 rightMap132 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice39 : Residual1Cache.slice leftMap132 rightMap132 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice40 : Residual1Cache.slice leftMap132 rightMap132 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice41 : Residual1Cache.slice leftMap132 rightMap132 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice42 : Residual1Cache.slice leftMap132 rightMap132 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice43 : Residual1Cache.slice leftMap132 rightMap132 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice44 : Residual1Cache.slice leftMap132 rightMap132 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice45 : Residual1Cache.slice leftMap132 rightMap132 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice46 : Residual1Cache.slice leftMap132 rightMap132 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice47 : Residual1Cache.slice leftMap132 rightMap132 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice48 : Residual1Cache.slice leftMap132 rightMap132 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice49 : Residual1Cache.slice leftMap132 rightMap132 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice50 : Residual1Cache.slice leftMap132 rightMap132 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice51 : Residual1Cache.slice leftMap132 rightMap132 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice52 : Residual1Cache.slice leftMap132 rightMap132 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice53 : Residual1Cache.slice leftMap132 rightMap132 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice54 : Residual1Cache.slice leftMap132 rightMap132 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice55 : Residual1Cache.slice leftMap132 rightMap132 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice56 : Residual1Cache.slice leftMap132 rightMap132 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice57 : Residual1Cache.slice leftMap132 rightMap132 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice58 : Residual1Cache.slice leftMap132 rightMap132 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice59 : Residual1Cache.slice leftMap132 rightMap132 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice60 : Residual1Cache.slice leftMap132 rightMap132 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice61 : Residual1Cache.slice leftMap132 rightMap132 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice62 : Residual1Cache.slice leftMap132 rightMap132 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice63 : Residual1Cache.slice leftMap132 rightMap132 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice64 : Residual1Cache.slice leftMap132 rightMap132 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice65 : Residual1Cache.slice leftMap132 rightMap132 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice66 : Residual1Cache.slice leftMap132 rightMap132 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice67 : Residual1Cache.slice leftMap132 rightMap132 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice68 : Residual1Cache.slice leftMap132 rightMap132 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice69 : Residual1Cache.slice leftMap132 rightMap132 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice70 : Residual1Cache.slice leftMap132 rightMap132 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice71 : Residual1Cache.slice leftMap132 rightMap132 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice72 : Residual1Cache.slice leftMap132 rightMap132 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice73 : Residual1Cache.slice leftMap132 rightMap132 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice74 : Residual1Cache.slice leftMap132 rightMap132 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice75 : Residual1Cache.slice leftMap132 rightMap132 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice76 : Residual1Cache.slice leftMap132 rightMap132 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice77 : Residual1Cache.slice leftMap132 rightMap132 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice78 : Residual1Cache.slice leftMap132 rightMap132 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice79 : Residual1Cache.slice leftMap132 rightMap132 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice80 : Residual1Cache.slice leftMap132 rightMap132 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice81 : Residual1Cache.slice leftMap132 rightMap132 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice82 : Residual1Cache.slice leftMap132 rightMap132 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice83 : Residual1Cache.slice leftMap132 rightMap132 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice84 : Residual1Cache.slice leftMap132 rightMap132 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice85 : Residual1Cache.slice leftMap132 rightMap132 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice86 : Residual1Cache.slice leftMap132 rightMap132 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice87 : Residual1Cache.slice leftMap132 rightMap132 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice88 : Residual1Cache.slice leftMap132 rightMap132 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice89 : Residual1Cache.slice leftMap132 rightMap132 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice90 : Residual1Cache.slice leftMap132 rightMap132 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice91 : Residual1Cache.slice leftMap132 rightMap132 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice92 : Residual1Cache.slice leftMap132 rightMap132 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice93 : Residual1Cache.slice leftMap132 rightMap132 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice94 : Residual1Cache.slice leftMap132 rightMap132 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice95 : Residual1Cache.slice leftMap132 rightMap132 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice96 : Residual1Cache.slice leftMap132 rightMap132 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice97 : Residual1Cache.slice leftMap132 rightMap132 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice98 : Residual1Cache.slice leftMap132 rightMap132 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice99 : Residual1Cache.slice leftMap132 rightMap132 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice100 : Residual1Cache.slice leftMap132 rightMap132 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice101 : Residual1Cache.slice leftMap132 rightMap132 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice102 : Residual1Cache.slice leftMap132 rightMap132 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice103 : Residual1Cache.slice leftMap132 rightMap132 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice104 : Residual1Cache.slice leftMap132 rightMap132 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice105 : Residual1Cache.slice leftMap132 rightMap132 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice106 : Residual1Cache.slice leftMap132 rightMap132 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice107 : Residual1Cache.slice leftMap132 rightMap132 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice108 : Residual1Cache.slice leftMap132 rightMap132 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice109 : Residual1Cache.slice leftMap132 rightMap132 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice110 : Residual1Cache.slice leftMap132 rightMap132 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice111 : Residual1Cache.slice leftMap132 rightMap132 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice112 : Residual1Cache.slice leftMap132 rightMap132 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice113 : Residual1Cache.slice leftMap132 rightMap132 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice114 : Residual1Cache.slice leftMap132 rightMap132 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice115 : Residual1Cache.slice leftMap132 rightMap132 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice116 : Residual1Cache.slice leftMap132 rightMap132 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice117 : Residual1Cache.slice leftMap132 rightMap132 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice118 : Residual1Cache.slice leftMap132 rightMap132 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice119 : Residual1Cache.slice leftMap132 rightMap132 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice120 : Residual1Cache.slice leftMap132 rightMap132 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice121 : Residual1Cache.slice leftMap132 rightMap132 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice122 : Residual1Cache.slice leftMap132 rightMap132 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice123 : Residual1Cache.slice leftMap132 rightMap132 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice124 : Residual1Cache.slice leftMap132 rightMap132 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice125 : Residual1Cache.slice leftMap132 rightMap132 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice126 : Residual1Cache.slice leftMap132 rightMap132 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice127 : Residual1Cache.slice leftMap132 rightMap132 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice128 : Residual1Cache.slice leftMap132 rightMap132 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice129 : Residual1Cache.slice leftMap132 rightMap132 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice130 : Residual1Cache.slice leftMap132 rightMap132 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice131 : Residual1Cache.slice leftMap132 rightMap132 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice132 : Residual1Cache.slice leftMap132 rightMap132 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice133 : Residual1Cache.slice leftMap132 rightMap132 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice134 : Residual1Cache.slice leftMap132 rightMap132 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice135 : Residual1Cache.slice leftMap132 rightMap132 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice136 : Residual1Cache.slice leftMap132 rightMap132 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice137 : Residual1Cache.slice leftMap132 rightMap132 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice138 : Residual1Cache.slice leftMap132 rightMap132 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice139 : Residual1Cache.slice leftMap132 rightMap132 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice140 : Residual1Cache.slice leftMap132 rightMap132 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice141 : Residual1Cache.slice leftMap132 rightMap132 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice142 : Residual1Cache.slice leftMap132 rightMap132 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice143 : Residual1Cache.slice leftMap132 rightMap132 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice144 : Residual1Cache.slice leftMap132 rightMap132 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice145 : Residual1Cache.slice leftMap132 rightMap132 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice146 : Residual1Cache.slice leftMap132 rightMap132 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice147 : Residual1Cache.slice leftMap132 rightMap132 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice148 : Residual1Cache.slice leftMap132 rightMap132 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice149 : Residual1Cache.slice leftMap132 rightMap132 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice150 : Residual1Cache.slice leftMap132 rightMap132 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice151 : Residual1Cache.slice leftMap132 rightMap132 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice152 : Residual1Cache.slice leftMap132 rightMap132 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice153 : Residual1Cache.slice leftMap132 rightMap132 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice154 : Residual1Cache.slice leftMap132 rightMap132 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice155 : Residual1Cache.slice leftMap132 rightMap132 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice156 : Residual1Cache.slice leftMap132 rightMap132 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice157 : Residual1Cache.slice leftMap132 rightMap132 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice158 : Residual1Cache.slice leftMap132 rightMap132 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice159 : Residual1Cache.slice leftMap132 rightMap132 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice160 : Residual1Cache.slice leftMap132 rightMap132 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice161 : Residual1Cache.slice leftMap132 rightMap132 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice162 : Residual1Cache.slice leftMap132 rightMap132 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice163 : Residual1Cache.slice leftMap132 rightMap132 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice164 : Residual1Cache.slice leftMap132 rightMap132 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice165 : Residual1Cache.slice leftMap132 rightMap132 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice166 : Residual1Cache.slice leftMap132 rightMap132 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice167 : Residual1Cache.slice leftMap132 rightMap132 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice168 : Residual1Cache.slice leftMap132 rightMap132 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice169 : Residual1Cache.slice leftMap132 rightMap132 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice170 : Residual1Cache.slice leftMap132 rightMap132 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice171 : Residual1Cache.slice leftMap132 rightMap132 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice172 : Residual1Cache.slice leftMap132 rightMap132 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice173 : Residual1Cache.slice leftMap132 rightMap132 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice174 : Residual1Cache.slice leftMap132 rightMap132 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice175 : Residual1Cache.slice leftMap132 rightMap132 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice176 : Residual1Cache.slice leftMap132 rightMap132 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice177 : Residual1Cache.slice leftMap132 rightMap132 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice178 : Residual1Cache.slice leftMap132 rightMap132 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice179 : Residual1Cache.slice leftMap132 rightMap132 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice180 : Residual1Cache.slice leftMap132 rightMap132 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice181 : Residual1Cache.slice leftMap132 rightMap132 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice182 : Residual1Cache.slice leftMap132 rightMap132 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice183 : Residual1Cache.slice leftMap132 rightMap132 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice184 : Residual1Cache.slice leftMap132 rightMap132 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice185 : Residual1Cache.slice leftMap132 rightMap132 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice186 : Residual1Cache.slice leftMap132 rightMap132 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice187 : Residual1Cache.slice leftMap132 rightMap132 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice188 : Residual1Cache.slice leftMap132 rightMap132 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice189 : Residual1Cache.slice leftMap132 rightMap132 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice190 : Residual1Cache.slice leftMap132 rightMap132 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice191 : Residual1Cache.slice leftMap132 rightMap132 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice192 : Residual1Cache.slice leftMap132 rightMap132 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice193 : Residual1Cache.slice leftMap132 rightMap132 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice194 : Residual1Cache.slice leftMap132 rightMap132 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice195 : Residual1Cache.slice leftMap132 rightMap132 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice196 : Residual1Cache.slice leftMap132 rightMap132 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice197 : Residual1Cache.slice leftMap132 rightMap132 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice198 : Residual1Cache.slice leftMap132 rightMap132 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice199 : Residual1Cache.slice leftMap132 rightMap132 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice200 : Residual1Cache.slice leftMap132 rightMap132 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice201 : Residual1Cache.slice leftMap132 rightMap132 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point132slice202 : Residual1Cache.slice leftMap132 rightMap132 202 = true := by
  decide +kernel

private theorem point132_slices : ∀ c, Residual1Cache.slice leftMap132 rightMap132 c = true := by
  intro c
  fin_cases c
  · exact point132slice0
  · exact point132slice1
  · exact point132slice2
  · exact point132slice3
  · exact point132slice4
  · exact point132slice5
  · exact point132slice6
  · exact point132slice7
  · exact point132slice8
  · exact point132slice9
  · exact point132slice10
  · exact point132slice11
  · exact point132slice12
  · exact point132slice13
  · exact point132slice14
  · exact point132slice15
  · exact point132slice16
  · exact point132slice17
  · exact point132slice18
  · exact point132slice19
  · exact point132slice20
  · exact point132slice21
  · exact point132slice22
  · exact point132slice23
  · exact point132slice24
  · exact point132slice25
  · exact point132slice26
  · exact point132slice27
  · exact point132slice28
  · exact point132slice29
  · exact point132slice30
  · exact point132slice31
  · exact point132slice32
  · exact point132slice33
  · exact point132slice34
  · exact point132slice35
  · exact point132slice36
  · exact point132slice37
  · exact point132slice38
  · exact point132slice39
  · exact point132slice40
  · exact point132slice41
  · exact point132slice42
  · exact point132slice43
  · exact point132slice44
  · exact point132slice45
  · exact point132slice46
  · exact point132slice47
  · exact point132slice48
  · exact point132slice49
  · exact point132slice50
  · exact point132slice51
  · exact point132slice52
  · exact point132slice53
  · exact point132slice54
  · exact point132slice55
  · exact point132slice56
  · exact point132slice57
  · exact point132slice58
  · exact point132slice59
  · exact point132slice60
  · exact point132slice61
  · exact point132slice62
  · exact point132slice63
  · exact point132slice64
  · exact point132slice65
  · exact point132slice66
  · exact point132slice67
  · exact point132slice68
  · exact point132slice69
  · exact point132slice70
  · exact point132slice71
  · exact point132slice72
  · exact point132slice73
  · exact point132slice74
  · exact point132slice75
  · exact point132slice76
  · exact point132slice77
  · exact point132slice78
  · exact point132slice79
  · exact point132slice80
  · exact point132slice81
  · exact point132slice82
  · exact point132slice83
  · exact point132slice84
  · exact point132slice85
  · exact point132slice86
  · exact point132slice87
  · exact point132slice88
  · exact point132slice89
  · exact point132slice90
  · exact point132slice91
  · exact point132slice92
  · exact point132slice93
  · exact point132slice94
  · exact point132slice95
  · exact point132slice96
  · exact point132slice97
  · exact point132slice98
  · exact point132slice99
  · exact point132slice100
  · exact point132slice101
  · exact point132slice102
  · exact point132slice103
  · exact point132slice104
  · exact point132slice105
  · exact point132slice106
  · exact point132slice107
  · exact point132slice108
  · exact point132slice109
  · exact point132slice110
  · exact point132slice111
  · exact point132slice112
  · exact point132slice113
  · exact point132slice114
  · exact point132slice115
  · exact point132slice116
  · exact point132slice117
  · exact point132slice118
  · exact point132slice119
  · exact point132slice120
  · exact point132slice121
  · exact point132slice122
  · exact point132slice123
  · exact point132slice124
  · exact point132slice125
  · exact point132slice126
  · exact point132slice127
  · exact point132slice128
  · exact point132slice129
  · exact point132slice130
  · exact point132slice131
  · exact point132slice132
  · exact point132slice133
  · exact point132slice134
  · exact point132slice135
  · exact point132slice136
  · exact point132slice137
  · exact point132slice138
  · exact point132slice139
  · exact point132slice140
  · exact point132slice141
  · exact point132slice142
  · exact point132slice143
  · exact point132slice144
  · exact point132slice145
  · exact point132slice146
  · exact point132slice147
  · exact point132slice148
  · exact point132slice149
  · exact point132slice150
  · exact point132slice151
  · exact point132slice152
  · exact point132slice153
  · exact point132slice154
  · exact point132slice155
  · exact point132slice156
  · exact point132slice157
  · exact point132slice158
  · exact point132slice159
  · exact point132slice160
  · exact point132slice161
  · exact point132slice162
  · exact point132slice163
  · exact point132slice164
  · exact point132slice165
  · exact point132slice166
  · exact point132slice167
  · exact point132slice168
  · exact point132slice169
  · exact point132slice170
  · exact point132slice171
  · exact point132slice172
  · exact point132slice173
  · exact point132slice174
  · exact point132slice175
  · exact point132slice176
  · exact point132slice177
  · exact point132slice178
  · exact point132slice179
  · exact point132slice180
  · exact point132slice181
  · exact point132slice182
  · exact point132slice183
  · exact point132slice184
  · exact point132slice185
  · exact point132slice186
  · exact point132slice187
  · exact point132slice188
  · exact point132slice189
  · exact point132slice190
  · exact point132slice191
  · exact point132slice192
  · exact point132slice193
  · exact point132slice194
  · exact point132slice195
  · exact point132slice196
  · exact point132slice197
  · exact point132slice198
  · exact point132slice199
  · exact point132slice200
  · exact point132slice201
  · exact point132slice202

set_option maxHeartbeats 1600000 in
public theorem point132 : stepCheck 0 2717 := by
  have hleft : L0Gen 0 * L0Rep 2717 = leftPerm132 := by
    change L0Gen 0 * evalWord L0Gen [1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 1, 0, 3] = leftPerm132
    simp only [leftPerm132, p166, p121, p60, p48, p30, p27, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2717) * evalWord L1Gen (L0Factor 0 2717) = rightPerm132 := by
    change evalWord L0Gen [1, 0, 3, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] * evalWord L1Gen [0, 1, 0, 1, 2, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm132
    simp only [rightPerm132, p731, p712, p288, p259, p128, p102, p101, p80, p57, p56, p52, p51, p50, p49, p48, p46, p45, p44, p43, p42, p41, p40, p39, p37, p36, p35, p34, p32, p31, p29, p28, p26, p24, p23, p22, p21, p20, p19, p18, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2717) x =
    (L0Rep (L0Act 0 2717) * evalWord L1Gen (L0Factor 0 2717)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap132_eq, ← rightMap132_eq]
  exact Residual1Cache.ofSlices point132_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
