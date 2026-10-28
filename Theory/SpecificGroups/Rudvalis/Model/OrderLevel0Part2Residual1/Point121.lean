module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level15Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 121

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap121 (x : Nat) : Nat := force t86 (t483 x)
private def leftPerm121 : Equiv.Perm (Fin 4060) := p86 * (p483)
private theorem leftMap121_eq (x : Fin 4060) :
    leftMap121 x.val = (leftPerm121 x).val := (compose (t := fun x => force t86 (t483 x)) (a := t86) (b := fun x => t483 x) (fun _ => rfl) c86 c483) x

private def rightMap121 (x : Nat) : Nat := force t59 (force t140 (force t0 (force t48 (force t69 (force t9 (force t52 (force t89 (force t94 (force t630 (t182 x))))))))))
private def rightPerm121 : Equiv.Perm (Fin 4060) := p59 * (p140 * (p0 * (p48 * (p69 * (p9 * (p52 * (p89 * (p94 * (p630 * (p182))))))))))
private theorem rightMap121_eq (x : Fin 4060) :
    rightMap121 x.val = (rightPerm121 x).val := (compose (t := fun x => force t59 (force t140 (force t0 (force t48 (force t69 (force t9 (force t52 (force t89 (force t94 (force t630 (t182 x))))))))))) (a := t59) (b := fun x => force t140 (force t0 (force t48 (force t69 (force t9 (force t52 (force t89 (force t94 (force t630 (t182 x)))))))))) (fun _ => rfl) c59 (compose (t := fun x => force t140 (force t0 (force t48 (force t69 (force t9 (force t52 (force t89 (force t94 (force t630 (t182 x)))))))))) (a := t140) (b := fun x => force t0 (force t48 (force t69 (force t9 (force t52 (force t89 (force t94 (force t630 (t182 x))))))))) (fun _ => rfl) c140 (compose (t := fun x => force t0 (force t48 (force t69 (force t9 (force t52 (force t89 (force t94 (force t630 (t182 x))))))))) (a := t0) (b := fun x => force t48 (force t69 (force t9 (force t52 (force t89 (force t94 (force t630 (t182 x)))))))) (fun _ => rfl) c0 (compose (t := fun x => force t48 (force t69 (force t9 (force t52 (force t89 (force t94 (force t630 (t182 x)))))))) (a := t48) (b := fun x => force t69 (force t9 (force t52 (force t89 (force t94 (force t630 (t182 x))))))) (fun _ => rfl) c48 (compose (t := fun x => force t69 (force t9 (force t52 (force t89 (force t94 (force t630 (t182 x))))))) (a := t69) (b := fun x => force t9 (force t52 (force t89 (force t94 (force t630 (t182 x)))))) (fun _ => rfl) c69 (compose (t := fun x => force t9 (force t52 (force t89 (force t94 (force t630 (t182 x)))))) (a := t9) (b := fun x => force t52 (force t89 (force t94 (force t630 (t182 x))))) (fun _ => rfl) c9 (compose (t := fun x => force t52 (force t89 (force t94 (force t630 (t182 x))))) (a := t52) (b := fun x => force t89 (force t94 (force t630 (t182 x)))) (fun _ => rfl) c52 (compose (t := fun x => force t89 (force t94 (force t630 (t182 x)))) (a := t89) (b := fun x => force t94 (force t630 (t182 x))) (fun _ => rfl) c89 (compose (t := fun x => force t94 (force t630 (t182 x))) (a := t94) (b := fun x => force t630 (t182 x)) (fun _ => rfl) c94 (compose (t := fun x => force t630 (t182 x)) (a := t630) (b := fun x => t182 x) (fun _ => rfl) c630 c182)))))))))) x

set_option maxHeartbeats 1600000 in
private theorem point121slice0 : Residual1Cache.slice leftMap121 rightMap121 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice1 : Residual1Cache.slice leftMap121 rightMap121 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice2 : Residual1Cache.slice leftMap121 rightMap121 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice3 : Residual1Cache.slice leftMap121 rightMap121 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice4 : Residual1Cache.slice leftMap121 rightMap121 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice5 : Residual1Cache.slice leftMap121 rightMap121 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice6 : Residual1Cache.slice leftMap121 rightMap121 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice7 : Residual1Cache.slice leftMap121 rightMap121 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice8 : Residual1Cache.slice leftMap121 rightMap121 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice9 : Residual1Cache.slice leftMap121 rightMap121 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice10 : Residual1Cache.slice leftMap121 rightMap121 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice11 : Residual1Cache.slice leftMap121 rightMap121 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice12 : Residual1Cache.slice leftMap121 rightMap121 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice13 : Residual1Cache.slice leftMap121 rightMap121 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice14 : Residual1Cache.slice leftMap121 rightMap121 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice15 : Residual1Cache.slice leftMap121 rightMap121 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice16 : Residual1Cache.slice leftMap121 rightMap121 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice17 : Residual1Cache.slice leftMap121 rightMap121 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice18 : Residual1Cache.slice leftMap121 rightMap121 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice19 : Residual1Cache.slice leftMap121 rightMap121 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice20 : Residual1Cache.slice leftMap121 rightMap121 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice21 : Residual1Cache.slice leftMap121 rightMap121 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice22 : Residual1Cache.slice leftMap121 rightMap121 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice23 : Residual1Cache.slice leftMap121 rightMap121 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice24 : Residual1Cache.slice leftMap121 rightMap121 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice25 : Residual1Cache.slice leftMap121 rightMap121 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice26 : Residual1Cache.slice leftMap121 rightMap121 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice27 : Residual1Cache.slice leftMap121 rightMap121 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice28 : Residual1Cache.slice leftMap121 rightMap121 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice29 : Residual1Cache.slice leftMap121 rightMap121 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice30 : Residual1Cache.slice leftMap121 rightMap121 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice31 : Residual1Cache.slice leftMap121 rightMap121 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice32 : Residual1Cache.slice leftMap121 rightMap121 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice33 : Residual1Cache.slice leftMap121 rightMap121 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice34 : Residual1Cache.slice leftMap121 rightMap121 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice35 : Residual1Cache.slice leftMap121 rightMap121 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice36 : Residual1Cache.slice leftMap121 rightMap121 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice37 : Residual1Cache.slice leftMap121 rightMap121 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice38 : Residual1Cache.slice leftMap121 rightMap121 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice39 : Residual1Cache.slice leftMap121 rightMap121 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice40 : Residual1Cache.slice leftMap121 rightMap121 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice41 : Residual1Cache.slice leftMap121 rightMap121 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice42 : Residual1Cache.slice leftMap121 rightMap121 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice43 : Residual1Cache.slice leftMap121 rightMap121 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice44 : Residual1Cache.slice leftMap121 rightMap121 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice45 : Residual1Cache.slice leftMap121 rightMap121 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice46 : Residual1Cache.slice leftMap121 rightMap121 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice47 : Residual1Cache.slice leftMap121 rightMap121 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice48 : Residual1Cache.slice leftMap121 rightMap121 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice49 : Residual1Cache.slice leftMap121 rightMap121 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice50 : Residual1Cache.slice leftMap121 rightMap121 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice51 : Residual1Cache.slice leftMap121 rightMap121 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice52 : Residual1Cache.slice leftMap121 rightMap121 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice53 : Residual1Cache.slice leftMap121 rightMap121 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice54 : Residual1Cache.slice leftMap121 rightMap121 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice55 : Residual1Cache.slice leftMap121 rightMap121 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice56 : Residual1Cache.slice leftMap121 rightMap121 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice57 : Residual1Cache.slice leftMap121 rightMap121 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice58 : Residual1Cache.slice leftMap121 rightMap121 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice59 : Residual1Cache.slice leftMap121 rightMap121 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice60 : Residual1Cache.slice leftMap121 rightMap121 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice61 : Residual1Cache.slice leftMap121 rightMap121 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice62 : Residual1Cache.slice leftMap121 rightMap121 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice63 : Residual1Cache.slice leftMap121 rightMap121 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice64 : Residual1Cache.slice leftMap121 rightMap121 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice65 : Residual1Cache.slice leftMap121 rightMap121 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice66 : Residual1Cache.slice leftMap121 rightMap121 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice67 : Residual1Cache.slice leftMap121 rightMap121 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice68 : Residual1Cache.slice leftMap121 rightMap121 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice69 : Residual1Cache.slice leftMap121 rightMap121 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice70 : Residual1Cache.slice leftMap121 rightMap121 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice71 : Residual1Cache.slice leftMap121 rightMap121 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice72 : Residual1Cache.slice leftMap121 rightMap121 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice73 : Residual1Cache.slice leftMap121 rightMap121 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice74 : Residual1Cache.slice leftMap121 rightMap121 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice75 : Residual1Cache.slice leftMap121 rightMap121 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice76 : Residual1Cache.slice leftMap121 rightMap121 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice77 : Residual1Cache.slice leftMap121 rightMap121 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice78 : Residual1Cache.slice leftMap121 rightMap121 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice79 : Residual1Cache.slice leftMap121 rightMap121 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice80 : Residual1Cache.slice leftMap121 rightMap121 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice81 : Residual1Cache.slice leftMap121 rightMap121 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice82 : Residual1Cache.slice leftMap121 rightMap121 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice83 : Residual1Cache.slice leftMap121 rightMap121 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice84 : Residual1Cache.slice leftMap121 rightMap121 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice85 : Residual1Cache.slice leftMap121 rightMap121 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice86 : Residual1Cache.slice leftMap121 rightMap121 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice87 : Residual1Cache.slice leftMap121 rightMap121 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice88 : Residual1Cache.slice leftMap121 rightMap121 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice89 : Residual1Cache.slice leftMap121 rightMap121 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice90 : Residual1Cache.slice leftMap121 rightMap121 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice91 : Residual1Cache.slice leftMap121 rightMap121 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice92 : Residual1Cache.slice leftMap121 rightMap121 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice93 : Residual1Cache.slice leftMap121 rightMap121 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice94 : Residual1Cache.slice leftMap121 rightMap121 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice95 : Residual1Cache.slice leftMap121 rightMap121 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice96 : Residual1Cache.slice leftMap121 rightMap121 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice97 : Residual1Cache.slice leftMap121 rightMap121 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice98 : Residual1Cache.slice leftMap121 rightMap121 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice99 : Residual1Cache.slice leftMap121 rightMap121 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice100 : Residual1Cache.slice leftMap121 rightMap121 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice101 : Residual1Cache.slice leftMap121 rightMap121 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice102 : Residual1Cache.slice leftMap121 rightMap121 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice103 : Residual1Cache.slice leftMap121 rightMap121 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice104 : Residual1Cache.slice leftMap121 rightMap121 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice105 : Residual1Cache.slice leftMap121 rightMap121 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice106 : Residual1Cache.slice leftMap121 rightMap121 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice107 : Residual1Cache.slice leftMap121 rightMap121 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice108 : Residual1Cache.slice leftMap121 rightMap121 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice109 : Residual1Cache.slice leftMap121 rightMap121 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice110 : Residual1Cache.slice leftMap121 rightMap121 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice111 : Residual1Cache.slice leftMap121 rightMap121 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice112 : Residual1Cache.slice leftMap121 rightMap121 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice113 : Residual1Cache.slice leftMap121 rightMap121 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice114 : Residual1Cache.slice leftMap121 rightMap121 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice115 : Residual1Cache.slice leftMap121 rightMap121 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice116 : Residual1Cache.slice leftMap121 rightMap121 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice117 : Residual1Cache.slice leftMap121 rightMap121 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice118 : Residual1Cache.slice leftMap121 rightMap121 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice119 : Residual1Cache.slice leftMap121 rightMap121 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice120 : Residual1Cache.slice leftMap121 rightMap121 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice121 : Residual1Cache.slice leftMap121 rightMap121 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice122 : Residual1Cache.slice leftMap121 rightMap121 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice123 : Residual1Cache.slice leftMap121 rightMap121 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice124 : Residual1Cache.slice leftMap121 rightMap121 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice125 : Residual1Cache.slice leftMap121 rightMap121 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice126 : Residual1Cache.slice leftMap121 rightMap121 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice127 : Residual1Cache.slice leftMap121 rightMap121 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice128 : Residual1Cache.slice leftMap121 rightMap121 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice129 : Residual1Cache.slice leftMap121 rightMap121 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice130 : Residual1Cache.slice leftMap121 rightMap121 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice131 : Residual1Cache.slice leftMap121 rightMap121 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice132 : Residual1Cache.slice leftMap121 rightMap121 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice133 : Residual1Cache.slice leftMap121 rightMap121 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice134 : Residual1Cache.slice leftMap121 rightMap121 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice135 : Residual1Cache.slice leftMap121 rightMap121 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice136 : Residual1Cache.slice leftMap121 rightMap121 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice137 : Residual1Cache.slice leftMap121 rightMap121 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice138 : Residual1Cache.slice leftMap121 rightMap121 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice139 : Residual1Cache.slice leftMap121 rightMap121 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice140 : Residual1Cache.slice leftMap121 rightMap121 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice141 : Residual1Cache.slice leftMap121 rightMap121 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice142 : Residual1Cache.slice leftMap121 rightMap121 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice143 : Residual1Cache.slice leftMap121 rightMap121 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice144 : Residual1Cache.slice leftMap121 rightMap121 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice145 : Residual1Cache.slice leftMap121 rightMap121 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice146 : Residual1Cache.slice leftMap121 rightMap121 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice147 : Residual1Cache.slice leftMap121 rightMap121 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice148 : Residual1Cache.slice leftMap121 rightMap121 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice149 : Residual1Cache.slice leftMap121 rightMap121 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice150 : Residual1Cache.slice leftMap121 rightMap121 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice151 : Residual1Cache.slice leftMap121 rightMap121 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice152 : Residual1Cache.slice leftMap121 rightMap121 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice153 : Residual1Cache.slice leftMap121 rightMap121 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice154 : Residual1Cache.slice leftMap121 rightMap121 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice155 : Residual1Cache.slice leftMap121 rightMap121 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice156 : Residual1Cache.slice leftMap121 rightMap121 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice157 : Residual1Cache.slice leftMap121 rightMap121 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice158 : Residual1Cache.slice leftMap121 rightMap121 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice159 : Residual1Cache.slice leftMap121 rightMap121 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice160 : Residual1Cache.slice leftMap121 rightMap121 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice161 : Residual1Cache.slice leftMap121 rightMap121 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice162 : Residual1Cache.slice leftMap121 rightMap121 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice163 : Residual1Cache.slice leftMap121 rightMap121 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice164 : Residual1Cache.slice leftMap121 rightMap121 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice165 : Residual1Cache.slice leftMap121 rightMap121 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice166 : Residual1Cache.slice leftMap121 rightMap121 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice167 : Residual1Cache.slice leftMap121 rightMap121 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice168 : Residual1Cache.slice leftMap121 rightMap121 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice169 : Residual1Cache.slice leftMap121 rightMap121 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice170 : Residual1Cache.slice leftMap121 rightMap121 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice171 : Residual1Cache.slice leftMap121 rightMap121 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice172 : Residual1Cache.slice leftMap121 rightMap121 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice173 : Residual1Cache.slice leftMap121 rightMap121 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice174 : Residual1Cache.slice leftMap121 rightMap121 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice175 : Residual1Cache.slice leftMap121 rightMap121 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice176 : Residual1Cache.slice leftMap121 rightMap121 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice177 : Residual1Cache.slice leftMap121 rightMap121 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice178 : Residual1Cache.slice leftMap121 rightMap121 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice179 : Residual1Cache.slice leftMap121 rightMap121 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice180 : Residual1Cache.slice leftMap121 rightMap121 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice181 : Residual1Cache.slice leftMap121 rightMap121 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice182 : Residual1Cache.slice leftMap121 rightMap121 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice183 : Residual1Cache.slice leftMap121 rightMap121 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice184 : Residual1Cache.slice leftMap121 rightMap121 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice185 : Residual1Cache.slice leftMap121 rightMap121 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice186 : Residual1Cache.slice leftMap121 rightMap121 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice187 : Residual1Cache.slice leftMap121 rightMap121 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice188 : Residual1Cache.slice leftMap121 rightMap121 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice189 : Residual1Cache.slice leftMap121 rightMap121 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice190 : Residual1Cache.slice leftMap121 rightMap121 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice191 : Residual1Cache.slice leftMap121 rightMap121 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice192 : Residual1Cache.slice leftMap121 rightMap121 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice193 : Residual1Cache.slice leftMap121 rightMap121 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice194 : Residual1Cache.slice leftMap121 rightMap121 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice195 : Residual1Cache.slice leftMap121 rightMap121 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice196 : Residual1Cache.slice leftMap121 rightMap121 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice197 : Residual1Cache.slice leftMap121 rightMap121 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice198 : Residual1Cache.slice leftMap121 rightMap121 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice199 : Residual1Cache.slice leftMap121 rightMap121 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice200 : Residual1Cache.slice leftMap121 rightMap121 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice201 : Residual1Cache.slice leftMap121 rightMap121 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point121slice202 : Residual1Cache.slice leftMap121 rightMap121 202 = true := by
  decide +kernel

private theorem point121_slices : ∀ c, Residual1Cache.slice leftMap121 rightMap121 c = true := by
  intro c
  fin_cases c
  · exact point121slice0
  · exact point121slice1
  · exact point121slice2
  · exact point121slice3
  · exact point121slice4
  · exact point121slice5
  · exact point121slice6
  · exact point121slice7
  · exact point121slice8
  · exact point121slice9
  · exact point121slice10
  · exact point121slice11
  · exact point121slice12
  · exact point121slice13
  · exact point121slice14
  · exact point121slice15
  · exact point121slice16
  · exact point121slice17
  · exact point121slice18
  · exact point121slice19
  · exact point121slice20
  · exact point121slice21
  · exact point121slice22
  · exact point121slice23
  · exact point121slice24
  · exact point121slice25
  · exact point121slice26
  · exact point121slice27
  · exact point121slice28
  · exact point121slice29
  · exact point121slice30
  · exact point121slice31
  · exact point121slice32
  · exact point121slice33
  · exact point121slice34
  · exact point121slice35
  · exact point121slice36
  · exact point121slice37
  · exact point121slice38
  · exact point121slice39
  · exact point121slice40
  · exact point121slice41
  · exact point121slice42
  · exact point121slice43
  · exact point121slice44
  · exact point121slice45
  · exact point121slice46
  · exact point121slice47
  · exact point121slice48
  · exact point121slice49
  · exact point121slice50
  · exact point121slice51
  · exact point121slice52
  · exact point121slice53
  · exact point121slice54
  · exact point121slice55
  · exact point121slice56
  · exact point121slice57
  · exact point121slice58
  · exact point121slice59
  · exact point121slice60
  · exact point121slice61
  · exact point121slice62
  · exact point121slice63
  · exact point121slice64
  · exact point121slice65
  · exact point121slice66
  · exact point121slice67
  · exact point121slice68
  · exact point121slice69
  · exact point121slice70
  · exact point121slice71
  · exact point121slice72
  · exact point121slice73
  · exact point121slice74
  · exact point121slice75
  · exact point121slice76
  · exact point121slice77
  · exact point121slice78
  · exact point121slice79
  · exact point121slice80
  · exact point121slice81
  · exact point121slice82
  · exact point121slice83
  · exact point121slice84
  · exact point121slice85
  · exact point121slice86
  · exact point121slice87
  · exact point121slice88
  · exact point121slice89
  · exact point121slice90
  · exact point121slice91
  · exact point121slice92
  · exact point121slice93
  · exact point121slice94
  · exact point121slice95
  · exact point121slice96
  · exact point121slice97
  · exact point121slice98
  · exact point121slice99
  · exact point121slice100
  · exact point121slice101
  · exact point121slice102
  · exact point121slice103
  · exact point121slice104
  · exact point121slice105
  · exact point121slice106
  · exact point121slice107
  · exact point121slice108
  · exact point121slice109
  · exact point121slice110
  · exact point121slice111
  · exact point121slice112
  · exact point121slice113
  · exact point121slice114
  · exact point121slice115
  · exact point121slice116
  · exact point121slice117
  · exact point121slice118
  · exact point121slice119
  · exact point121slice120
  · exact point121slice121
  · exact point121slice122
  · exact point121slice123
  · exact point121slice124
  · exact point121slice125
  · exact point121slice126
  · exact point121slice127
  · exact point121slice128
  · exact point121slice129
  · exact point121slice130
  · exact point121slice131
  · exact point121slice132
  · exact point121slice133
  · exact point121slice134
  · exact point121slice135
  · exact point121slice136
  · exact point121slice137
  · exact point121slice138
  · exact point121slice139
  · exact point121slice140
  · exact point121slice141
  · exact point121slice142
  · exact point121slice143
  · exact point121slice144
  · exact point121slice145
  · exact point121slice146
  · exact point121slice147
  · exact point121slice148
  · exact point121slice149
  · exact point121slice150
  · exact point121slice151
  · exact point121slice152
  · exact point121slice153
  · exact point121slice154
  · exact point121slice155
  · exact point121slice156
  · exact point121slice157
  · exact point121slice158
  · exact point121slice159
  · exact point121slice160
  · exact point121slice161
  · exact point121slice162
  · exact point121slice163
  · exact point121slice164
  · exact point121slice165
  · exact point121slice166
  · exact point121slice167
  · exact point121slice168
  · exact point121slice169
  · exact point121slice170
  · exact point121slice171
  · exact point121slice172
  · exact point121slice173
  · exact point121slice174
  · exact point121slice175
  · exact point121slice176
  · exact point121slice177
  · exact point121slice178
  · exact point121slice179
  · exact point121slice180
  · exact point121slice181
  · exact point121slice182
  · exact point121slice183
  · exact point121slice184
  · exact point121slice185
  · exact point121slice186
  · exact point121slice187
  · exact point121slice188
  · exact point121slice189
  · exact point121slice190
  · exact point121slice191
  · exact point121slice192
  · exact point121slice193
  · exact point121slice194
  · exact point121slice195
  · exact point121slice196
  · exact point121slice197
  · exact point121slice198
  · exact point121slice199
  · exact point121slice200
  · exact point121slice201
  · exact point121slice202

set_option maxHeartbeats 1600000 in
public theorem point121 : stepCheck 1 2569 := by
  have hleft : L0Gen 1 * L0Rep 2569 = leftPerm121 := by
    change L0Gen 1 * evalWord L0Gen [1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1] = leftPerm121
    simp only [leftPerm121, p483, p86, p80, p48, p27, p20, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2569) * evalWord L1Gen (L0Factor 1 2569) = rightPerm121 := by
    change evalWord L0Gen [3, 0, 1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 1, 1] * evalWord L1Gen [2, 1, 2, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm121
    simp only [rightPerm121, p630, p259, p182, p140, p94, p89, p83, p70, p69, p59, p56, p52, p51, p49, p48, p47, p46, p45, p44, p43, p42, p41, p40, p39, p37, p36, p35, p34, p33, p32, p31, p29, p28, p26, p24, p23, p22, p21, p20, p19, p18, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2569) x =
    (L0Rep (L0Act 1 2569) * evalWord L1Gen (L0Factor 1 2569)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap121_eq, ← rightMap121_eq]
  exact Residual1Cache.ofSlices point121_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
