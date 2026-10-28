module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level08Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level12Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 124

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap124 (x : Nat) : Nat := force t246 (force t0 (t48 x))
private def leftPerm124 : Equiv.Perm (Fin 4060) := p246 * (p0 * (p48))
private theorem leftMap124_eq (x : Fin 4060) :
    leftMap124 x.val = (leftPerm124 x).val := (compose (t := fun x => force t246 (force t0 (t48 x))) (a := t246) (b := fun x => force t0 (t48 x)) (fun _ => rfl) c246 (compose (t := fun x => force t0 (t48 x)) (a := t0) (b := fun x => t48 x) (fun _ => rfl) c0 c48)) x

private def rightMap124 (x : Nat) : Nat := force t59 (force t59 (force t14 (force t48 (force t731 (force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x)))))))))))))
private def rightPerm124 : Equiv.Perm (Fin 4060) := p59 * (p59 * (p14 * (p48 * (p731 * (p132 * (p108 * (p87 * (p13 * (p431 * (p630 * (p69 * (p6 * (p66)))))))))))))
private theorem rightMap124_eq (x : Fin 4060) :
    rightMap124 x.val = (rightPerm124 x).val := (compose (t := fun x => force t59 (force t59 (force t14 (force t48 (force t731 (force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x)))))))))))))) (a := t59) (b := fun x => force t59 (force t14 (force t48 (force t731 (force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x))))))))))))) (fun _ => rfl) c59 (compose (t := fun x => force t59 (force t14 (force t48 (force t731 (force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x))))))))))))) (a := t59) (b := fun x => force t14 (force t48 (force t731 (force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x)))))))))))) (fun _ => rfl) c59 (compose (t := fun x => force t14 (force t48 (force t731 (force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x)))))))))))) (a := t14) (b := fun x => force t48 (force t731 (force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x))))))))))) (fun _ => rfl) c14 (compose (t := fun x => force t48 (force t731 (force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x))))))))))) (a := t48) (b := fun x => force t731 (force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x)))))))))) (fun _ => rfl) c48 (compose (t := fun x => force t731 (force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x)))))))))) (a := t731) (b := fun x => force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x))))))))) (fun _ => rfl) c731 (compose (t := fun x => force t132 (force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x))))))))) (a := t132) (b := fun x => force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x)))))))) (fun _ => rfl) c132 (compose (t := fun x => force t108 (force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x)))))))) (a := t108) (b := fun x => force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x))))))) (fun _ => rfl) c108 (compose (t := fun x => force t87 (force t13 (force t431 (force t630 (force t69 (force t6 (t66 x))))))) (a := t87) (b := fun x => force t13 (force t431 (force t630 (force t69 (force t6 (t66 x)))))) (fun _ => rfl) c87 (compose (t := fun x => force t13 (force t431 (force t630 (force t69 (force t6 (t66 x)))))) (a := t13) (b := fun x => force t431 (force t630 (force t69 (force t6 (t66 x))))) (fun _ => rfl) c13 (compose (t := fun x => force t431 (force t630 (force t69 (force t6 (t66 x))))) (a := t431) (b := fun x => force t630 (force t69 (force t6 (t66 x)))) (fun _ => rfl) c431 (compose (t := fun x => force t630 (force t69 (force t6 (t66 x)))) (a := t630) (b := fun x => force t69 (force t6 (t66 x))) (fun _ => rfl) c630 (compose (t := fun x => force t69 (force t6 (t66 x))) (a := t69) (b := fun x => force t6 (t66 x)) (fun _ => rfl) c69 (compose (t := fun x => force t6 (t66 x)) (a := t6) (b := fun x => t66 x) (fun _ => rfl) c6 c66))))))))))))) x

set_option maxHeartbeats 1600000 in
private theorem point124slice0 : Residual1Cache.slice leftMap124 rightMap124 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice1 : Residual1Cache.slice leftMap124 rightMap124 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice2 : Residual1Cache.slice leftMap124 rightMap124 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice3 : Residual1Cache.slice leftMap124 rightMap124 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice4 : Residual1Cache.slice leftMap124 rightMap124 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice5 : Residual1Cache.slice leftMap124 rightMap124 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice6 : Residual1Cache.slice leftMap124 rightMap124 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice7 : Residual1Cache.slice leftMap124 rightMap124 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice8 : Residual1Cache.slice leftMap124 rightMap124 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice9 : Residual1Cache.slice leftMap124 rightMap124 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice10 : Residual1Cache.slice leftMap124 rightMap124 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice11 : Residual1Cache.slice leftMap124 rightMap124 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice12 : Residual1Cache.slice leftMap124 rightMap124 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice13 : Residual1Cache.slice leftMap124 rightMap124 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice14 : Residual1Cache.slice leftMap124 rightMap124 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice15 : Residual1Cache.slice leftMap124 rightMap124 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice16 : Residual1Cache.slice leftMap124 rightMap124 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice17 : Residual1Cache.slice leftMap124 rightMap124 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice18 : Residual1Cache.slice leftMap124 rightMap124 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice19 : Residual1Cache.slice leftMap124 rightMap124 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice20 : Residual1Cache.slice leftMap124 rightMap124 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice21 : Residual1Cache.slice leftMap124 rightMap124 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice22 : Residual1Cache.slice leftMap124 rightMap124 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice23 : Residual1Cache.slice leftMap124 rightMap124 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice24 : Residual1Cache.slice leftMap124 rightMap124 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice25 : Residual1Cache.slice leftMap124 rightMap124 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice26 : Residual1Cache.slice leftMap124 rightMap124 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice27 : Residual1Cache.slice leftMap124 rightMap124 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice28 : Residual1Cache.slice leftMap124 rightMap124 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice29 : Residual1Cache.slice leftMap124 rightMap124 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice30 : Residual1Cache.slice leftMap124 rightMap124 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice31 : Residual1Cache.slice leftMap124 rightMap124 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice32 : Residual1Cache.slice leftMap124 rightMap124 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice33 : Residual1Cache.slice leftMap124 rightMap124 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice34 : Residual1Cache.slice leftMap124 rightMap124 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice35 : Residual1Cache.slice leftMap124 rightMap124 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice36 : Residual1Cache.slice leftMap124 rightMap124 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice37 : Residual1Cache.slice leftMap124 rightMap124 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice38 : Residual1Cache.slice leftMap124 rightMap124 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice39 : Residual1Cache.slice leftMap124 rightMap124 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice40 : Residual1Cache.slice leftMap124 rightMap124 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice41 : Residual1Cache.slice leftMap124 rightMap124 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice42 : Residual1Cache.slice leftMap124 rightMap124 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice43 : Residual1Cache.slice leftMap124 rightMap124 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice44 : Residual1Cache.slice leftMap124 rightMap124 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice45 : Residual1Cache.slice leftMap124 rightMap124 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice46 : Residual1Cache.slice leftMap124 rightMap124 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice47 : Residual1Cache.slice leftMap124 rightMap124 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice48 : Residual1Cache.slice leftMap124 rightMap124 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice49 : Residual1Cache.slice leftMap124 rightMap124 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice50 : Residual1Cache.slice leftMap124 rightMap124 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice51 : Residual1Cache.slice leftMap124 rightMap124 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice52 : Residual1Cache.slice leftMap124 rightMap124 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice53 : Residual1Cache.slice leftMap124 rightMap124 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice54 : Residual1Cache.slice leftMap124 rightMap124 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice55 : Residual1Cache.slice leftMap124 rightMap124 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice56 : Residual1Cache.slice leftMap124 rightMap124 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice57 : Residual1Cache.slice leftMap124 rightMap124 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice58 : Residual1Cache.slice leftMap124 rightMap124 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice59 : Residual1Cache.slice leftMap124 rightMap124 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice60 : Residual1Cache.slice leftMap124 rightMap124 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice61 : Residual1Cache.slice leftMap124 rightMap124 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice62 : Residual1Cache.slice leftMap124 rightMap124 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice63 : Residual1Cache.slice leftMap124 rightMap124 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice64 : Residual1Cache.slice leftMap124 rightMap124 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice65 : Residual1Cache.slice leftMap124 rightMap124 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice66 : Residual1Cache.slice leftMap124 rightMap124 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice67 : Residual1Cache.slice leftMap124 rightMap124 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice68 : Residual1Cache.slice leftMap124 rightMap124 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice69 : Residual1Cache.slice leftMap124 rightMap124 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice70 : Residual1Cache.slice leftMap124 rightMap124 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice71 : Residual1Cache.slice leftMap124 rightMap124 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice72 : Residual1Cache.slice leftMap124 rightMap124 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice73 : Residual1Cache.slice leftMap124 rightMap124 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice74 : Residual1Cache.slice leftMap124 rightMap124 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice75 : Residual1Cache.slice leftMap124 rightMap124 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice76 : Residual1Cache.slice leftMap124 rightMap124 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice77 : Residual1Cache.slice leftMap124 rightMap124 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice78 : Residual1Cache.slice leftMap124 rightMap124 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice79 : Residual1Cache.slice leftMap124 rightMap124 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice80 : Residual1Cache.slice leftMap124 rightMap124 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice81 : Residual1Cache.slice leftMap124 rightMap124 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice82 : Residual1Cache.slice leftMap124 rightMap124 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice83 : Residual1Cache.slice leftMap124 rightMap124 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice84 : Residual1Cache.slice leftMap124 rightMap124 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice85 : Residual1Cache.slice leftMap124 rightMap124 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice86 : Residual1Cache.slice leftMap124 rightMap124 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice87 : Residual1Cache.slice leftMap124 rightMap124 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice88 : Residual1Cache.slice leftMap124 rightMap124 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice89 : Residual1Cache.slice leftMap124 rightMap124 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice90 : Residual1Cache.slice leftMap124 rightMap124 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice91 : Residual1Cache.slice leftMap124 rightMap124 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice92 : Residual1Cache.slice leftMap124 rightMap124 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice93 : Residual1Cache.slice leftMap124 rightMap124 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice94 : Residual1Cache.slice leftMap124 rightMap124 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice95 : Residual1Cache.slice leftMap124 rightMap124 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice96 : Residual1Cache.slice leftMap124 rightMap124 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice97 : Residual1Cache.slice leftMap124 rightMap124 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice98 : Residual1Cache.slice leftMap124 rightMap124 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice99 : Residual1Cache.slice leftMap124 rightMap124 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice100 : Residual1Cache.slice leftMap124 rightMap124 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice101 : Residual1Cache.slice leftMap124 rightMap124 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice102 : Residual1Cache.slice leftMap124 rightMap124 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice103 : Residual1Cache.slice leftMap124 rightMap124 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice104 : Residual1Cache.slice leftMap124 rightMap124 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice105 : Residual1Cache.slice leftMap124 rightMap124 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice106 : Residual1Cache.slice leftMap124 rightMap124 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice107 : Residual1Cache.slice leftMap124 rightMap124 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice108 : Residual1Cache.slice leftMap124 rightMap124 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice109 : Residual1Cache.slice leftMap124 rightMap124 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice110 : Residual1Cache.slice leftMap124 rightMap124 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice111 : Residual1Cache.slice leftMap124 rightMap124 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice112 : Residual1Cache.slice leftMap124 rightMap124 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice113 : Residual1Cache.slice leftMap124 rightMap124 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice114 : Residual1Cache.slice leftMap124 rightMap124 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice115 : Residual1Cache.slice leftMap124 rightMap124 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice116 : Residual1Cache.slice leftMap124 rightMap124 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice117 : Residual1Cache.slice leftMap124 rightMap124 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice118 : Residual1Cache.slice leftMap124 rightMap124 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice119 : Residual1Cache.slice leftMap124 rightMap124 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice120 : Residual1Cache.slice leftMap124 rightMap124 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice121 : Residual1Cache.slice leftMap124 rightMap124 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice122 : Residual1Cache.slice leftMap124 rightMap124 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice123 : Residual1Cache.slice leftMap124 rightMap124 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice124 : Residual1Cache.slice leftMap124 rightMap124 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice125 : Residual1Cache.slice leftMap124 rightMap124 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice126 : Residual1Cache.slice leftMap124 rightMap124 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice127 : Residual1Cache.slice leftMap124 rightMap124 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice128 : Residual1Cache.slice leftMap124 rightMap124 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice129 : Residual1Cache.slice leftMap124 rightMap124 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice130 : Residual1Cache.slice leftMap124 rightMap124 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice131 : Residual1Cache.slice leftMap124 rightMap124 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice132 : Residual1Cache.slice leftMap124 rightMap124 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice133 : Residual1Cache.slice leftMap124 rightMap124 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice134 : Residual1Cache.slice leftMap124 rightMap124 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice135 : Residual1Cache.slice leftMap124 rightMap124 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice136 : Residual1Cache.slice leftMap124 rightMap124 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice137 : Residual1Cache.slice leftMap124 rightMap124 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice138 : Residual1Cache.slice leftMap124 rightMap124 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice139 : Residual1Cache.slice leftMap124 rightMap124 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice140 : Residual1Cache.slice leftMap124 rightMap124 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice141 : Residual1Cache.slice leftMap124 rightMap124 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice142 : Residual1Cache.slice leftMap124 rightMap124 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice143 : Residual1Cache.slice leftMap124 rightMap124 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice144 : Residual1Cache.slice leftMap124 rightMap124 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice145 : Residual1Cache.slice leftMap124 rightMap124 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice146 : Residual1Cache.slice leftMap124 rightMap124 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice147 : Residual1Cache.slice leftMap124 rightMap124 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice148 : Residual1Cache.slice leftMap124 rightMap124 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice149 : Residual1Cache.slice leftMap124 rightMap124 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice150 : Residual1Cache.slice leftMap124 rightMap124 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice151 : Residual1Cache.slice leftMap124 rightMap124 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice152 : Residual1Cache.slice leftMap124 rightMap124 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice153 : Residual1Cache.slice leftMap124 rightMap124 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice154 : Residual1Cache.slice leftMap124 rightMap124 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice155 : Residual1Cache.slice leftMap124 rightMap124 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice156 : Residual1Cache.slice leftMap124 rightMap124 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice157 : Residual1Cache.slice leftMap124 rightMap124 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice158 : Residual1Cache.slice leftMap124 rightMap124 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice159 : Residual1Cache.slice leftMap124 rightMap124 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice160 : Residual1Cache.slice leftMap124 rightMap124 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice161 : Residual1Cache.slice leftMap124 rightMap124 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice162 : Residual1Cache.slice leftMap124 rightMap124 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice163 : Residual1Cache.slice leftMap124 rightMap124 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice164 : Residual1Cache.slice leftMap124 rightMap124 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice165 : Residual1Cache.slice leftMap124 rightMap124 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice166 : Residual1Cache.slice leftMap124 rightMap124 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice167 : Residual1Cache.slice leftMap124 rightMap124 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice168 : Residual1Cache.slice leftMap124 rightMap124 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice169 : Residual1Cache.slice leftMap124 rightMap124 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice170 : Residual1Cache.slice leftMap124 rightMap124 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice171 : Residual1Cache.slice leftMap124 rightMap124 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice172 : Residual1Cache.slice leftMap124 rightMap124 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice173 : Residual1Cache.slice leftMap124 rightMap124 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice174 : Residual1Cache.slice leftMap124 rightMap124 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice175 : Residual1Cache.slice leftMap124 rightMap124 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice176 : Residual1Cache.slice leftMap124 rightMap124 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice177 : Residual1Cache.slice leftMap124 rightMap124 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice178 : Residual1Cache.slice leftMap124 rightMap124 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice179 : Residual1Cache.slice leftMap124 rightMap124 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice180 : Residual1Cache.slice leftMap124 rightMap124 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice181 : Residual1Cache.slice leftMap124 rightMap124 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice182 : Residual1Cache.slice leftMap124 rightMap124 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice183 : Residual1Cache.slice leftMap124 rightMap124 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice184 : Residual1Cache.slice leftMap124 rightMap124 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice185 : Residual1Cache.slice leftMap124 rightMap124 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice186 : Residual1Cache.slice leftMap124 rightMap124 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice187 : Residual1Cache.slice leftMap124 rightMap124 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice188 : Residual1Cache.slice leftMap124 rightMap124 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice189 : Residual1Cache.slice leftMap124 rightMap124 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice190 : Residual1Cache.slice leftMap124 rightMap124 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice191 : Residual1Cache.slice leftMap124 rightMap124 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice192 : Residual1Cache.slice leftMap124 rightMap124 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice193 : Residual1Cache.slice leftMap124 rightMap124 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice194 : Residual1Cache.slice leftMap124 rightMap124 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice195 : Residual1Cache.slice leftMap124 rightMap124 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice196 : Residual1Cache.slice leftMap124 rightMap124 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice197 : Residual1Cache.slice leftMap124 rightMap124 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice198 : Residual1Cache.slice leftMap124 rightMap124 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice199 : Residual1Cache.slice leftMap124 rightMap124 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice200 : Residual1Cache.slice leftMap124 rightMap124 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice201 : Residual1Cache.slice leftMap124 rightMap124 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point124slice202 : Residual1Cache.slice leftMap124 rightMap124 202 = true := by
  decide +kernel

private theorem point124_slices : ∀ c, Residual1Cache.slice leftMap124 rightMap124 c = true := by
  intro c
  fin_cases c
  · exact point124slice0
  · exact point124slice1
  · exact point124slice2
  · exact point124slice3
  · exact point124slice4
  · exact point124slice5
  · exact point124slice6
  · exact point124slice7
  · exact point124slice8
  · exact point124slice9
  · exact point124slice10
  · exact point124slice11
  · exact point124slice12
  · exact point124slice13
  · exact point124slice14
  · exact point124slice15
  · exact point124slice16
  · exact point124slice17
  · exact point124slice18
  · exact point124slice19
  · exact point124slice20
  · exact point124slice21
  · exact point124slice22
  · exact point124slice23
  · exact point124slice24
  · exact point124slice25
  · exact point124slice26
  · exact point124slice27
  · exact point124slice28
  · exact point124slice29
  · exact point124slice30
  · exact point124slice31
  · exact point124slice32
  · exact point124slice33
  · exact point124slice34
  · exact point124slice35
  · exact point124slice36
  · exact point124slice37
  · exact point124slice38
  · exact point124slice39
  · exact point124slice40
  · exact point124slice41
  · exact point124slice42
  · exact point124slice43
  · exact point124slice44
  · exact point124slice45
  · exact point124slice46
  · exact point124slice47
  · exact point124slice48
  · exact point124slice49
  · exact point124slice50
  · exact point124slice51
  · exact point124slice52
  · exact point124slice53
  · exact point124slice54
  · exact point124slice55
  · exact point124slice56
  · exact point124slice57
  · exact point124slice58
  · exact point124slice59
  · exact point124slice60
  · exact point124slice61
  · exact point124slice62
  · exact point124slice63
  · exact point124slice64
  · exact point124slice65
  · exact point124slice66
  · exact point124slice67
  · exact point124slice68
  · exact point124slice69
  · exact point124slice70
  · exact point124slice71
  · exact point124slice72
  · exact point124slice73
  · exact point124slice74
  · exact point124slice75
  · exact point124slice76
  · exact point124slice77
  · exact point124slice78
  · exact point124slice79
  · exact point124slice80
  · exact point124slice81
  · exact point124slice82
  · exact point124slice83
  · exact point124slice84
  · exact point124slice85
  · exact point124slice86
  · exact point124slice87
  · exact point124slice88
  · exact point124slice89
  · exact point124slice90
  · exact point124slice91
  · exact point124slice92
  · exact point124slice93
  · exact point124slice94
  · exact point124slice95
  · exact point124slice96
  · exact point124slice97
  · exact point124slice98
  · exact point124slice99
  · exact point124slice100
  · exact point124slice101
  · exact point124slice102
  · exact point124slice103
  · exact point124slice104
  · exact point124slice105
  · exact point124slice106
  · exact point124slice107
  · exact point124slice108
  · exact point124slice109
  · exact point124slice110
  · exact point124slice111
  · exact point124slice112
  · exact point124slice113
  · exact point124slice114
  · exact point124slice115
  · exact point124slice116
  · exact point124slice117
  · exact point124slice118
  · exact point124slice119
  · exact point124slice120
  · exact point124slice121
  · exact point124slice122
  · exact point124slice123
  · exact point124slice124
  · exact point124slice125
  · exact point124slice126
  · exact point124slice127
  · exact point124slice128
  · exact point124slice129
  · exact point124slice130
  · exact point124slice131
  · exact point124slice132
  · exact point124slice133
  · exact point124slice134
  · exact point124slice135
  · exact point124slice136
  · exact point124slice137
  · exact point124slice138
  · exact point124slice139
  · exact point124slice140
  · exact point124slice141
  · exact point124slice142
  · exact point124slice143
  · exact point124slice144
  · exact point124slice145
  · exact point124slice146
  · exact point124slice147
  · exact point124slice148
  · exact point124slice149
  · exact point124slice150
  · exact point124slice151
  · exact point124slice152
  · exact point124slice153
  · exact point124slice154
  · exact point124slice155
  · exact point124slice156
  · exact point124slice157
  · exact point124slice158
  · exact point124slice159
  · exact point124slice160
  · exact point124slice161
  · exact point124slice162
  · exact point124slice163
  · exact point124slice164
  · exact point124slice165
  · exact point124slice166
  · exact point124slice167
  · exact point124slice168
  · exact point124slice169
  · exact point124slice170
  · exact point124slice171
  · exact point124slice172
  · exact point124slice173
  · exact point124slice174
  · exact point124slice175
  · exact point124slice176
  · exact point124slice177
  · exact point124slice178
  · exact point124slice179
  · exact point124slice180
  · exact point124slice181
  · exact point124slice182
  · exact point124slice183
  · exact point124slice184
  · exact point124slice185
  · exact point124slice186
  · exact point124slice187
  · exact point124slice188
  · exact point124slice189
  · exact point124slice190
  · exact point124slice191
  · exact point124slice192
  · exact point124slice193
  · exact point124slice194
  · exact point124slice195
  · exact point124slice196
  · exact point124slice197
  · exact point124slice198
  · exact point124slice199
  · exact point124slice200
  · exact point124slice201
  · exact point124slice202

set_option maxHeartbeats 1600000 in
public theorem point124 : stepCheck 1 2576 := by
  have hleft : L0Gen 1 * L0Rep 2576 = leftPerm124 := by
    change L0Gen 1 * evalWord L0Gen [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] = leftPerm124
    simp only [leftPerm124, p246, p80, p68, p48, p30, p20, p17, p11, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2576) * evalWord L1Gen (L0Factor 1 2576) = rightPerm124 := by
    change evalWord L0Gen [3, 0, 1, 1, 0, 3, 0, 1, 1, 0, 3, 0, 1, 1] * evalWord L1Gen [0, 1, 0, 1, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3] = rightPerm124
    simp only [rightPerm124, p731, p630, p431, p430, p259, p132, p108, p96, p87, p69, p66, p65, p64, p61, p59, p58, p55, p48, p46, p44, p43, p42, p39, p38, p37, p36, p34, p33, p32, p31, p29, p28, p26, p25, p24, p23, p22, p21, p20, p19, p18, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2576) x =
    (L0Rep (L0Act 1 2576) * evalWord L1Gen (L0Factor 1 2576)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap124_eq, ← rightMap124_eq]
  exact Residual1Cache.ofSlices point124_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
