module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level13Part1
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 133

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap133 (x : Nat) : Nat := force t703 (t153 x)
private def leftPerm133 : Equiv.Perm (Fin 4060) := p703 * (p153)
private theorem leftMap133_eq (x : Fin 4060) :
    leftMap133 x.val = (leftPerm133 x).val := (compose (t := fun x => force t703 (t153 x)) (a := t703) (b := fun x => t153 x) (fun _ => rfl) c703 c153) x

private def rightMap133 (x : Nat) : Nat := force t102 (force t50 (force t48 (force t35 (force t132 (force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x))))))))))))
private def rightPerm133 : Equiv.Perm (Fin 4060) := p102 * (p50 * (p48 * (p35 * (p132 * (p179 * (p19 * (p87 * (p58 * (p109 * (p630 * (p390 * (p570))))))))))))
private theorem rightMap133_eq (x : Fin 4060) :
    rightMap133 x.val = (rightPerm133 x).val := (compose (t := fun x => force t102 (force t50 (force t48 (force t35 (force t132 (force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x))))))))))))) (a := t102) (b := fun x => force t50 (force t48 (force t35 (force t132 (force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x)))))))))))) (fun _ => rfl) c102 (compose (t := fun x => force t50 (force t48 (force t35 (force t132 (force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x)))))))))))) (a := t50) (b := fun x => force t48 (force t35 (force t132 (force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x))))))))))) (fun _ => rfl) c50 (compose (t := fun x => force t48 (force t35 (force t132 (force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x))))))))))) (a := t48) (b := fun x => force t35 (force t132 (force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x)))))))))) (fun _ => rfl) c48 (compose (t := fun x => force t35 (force t132 (force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x)))))))))) (a := t35) (b := fun x => force t132 (force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x))))))))) (fun _ => rfl) c35 (compose (t := fun x => force t132 (force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x))))))))) (a := t132) (b := fun x => force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x)))))))) (fun _ => rfl) c132 (compose (t := fun x => force t179 (force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x)))))))) (a := t179) (b := fun x => force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x))))))) (fun _ => rfl) c179 (compose (t := fun x => force t19 (force t87 (force t58 (force t109 (force t630 (force t390 (t570 x))))))) (a := t19) (b := fun x => force t87 (force t58 (force t109 (force t630 (force t390 (t570 x)))))) (fun _ => rfl) c19 (compose (t := fun x => force t87 (force t58 (force t109 (force t630 (force t390 (t570 x)))))) (a := t87) (b := fun x => force t58 (force t109 (force t630 (force t390 (t570 x))))) (fun _ => rfl) c87 (compose (t := fun x => force t58 (force t109 (force t630 (force t390 (t570 x))))) (a := t58) (b := fun x => force t109 (force t630 (force t390 (t570 x)))) (fun _ => rfl) c58 (compose (t := fun x => force t109 (force t630 (force t390 (t570 x)))) (a := t109) (b := fun x => force t630 (force t390 (t570 x))) (fun _ => rfl) c109 (compose (t := fun x => force t630 (force t390 (t570 x))) (a := t630) (b := fun x => force t390 (t570 x)) (fun _ => rfl) c630 (compose (t := fun x => force t390 (t570 x)) (a := t390) (b := fun x => t570 x) (fun _ => rfl) c390 c570)))))))))))) x

set_option maxHeartbeats 1600000 in
private theorem point133slice0 : Residual1Cache.slice leftMap133 rightMap133 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice1 : Residual1Cache.slice leftMap133 rightMap133 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice2 : Residual1Cache.slice leftMap133 rightMap133 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice3 : Residual1Cache.slice leftMap133 rightMap133 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice4 : Residual1Cache.slice leftMap133 rightMap133 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice5 : Residual1Cache.slice leftMap133 rightMap133 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice6 : Residual1Cache.slice leftMap133 rightMap133 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice7 : Residual1Cache.slice leftMap133 rightMap133 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice8 : Residual1Cache.slice leftMap133 rightMap133 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice9 : Residual1Cache.slice leftMap133 rightMap133 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice10 : Residual1Cache.slice leftMap133 rightMap133 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice11 : Residual1Cache.slice leftMap133 rightMap133 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice12 : Residual1Cache.slice leftMap133 rightMap133 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice13 : Residual1Cache.slice leftMap133 rightMap133 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice14 : Residual1Cache.slice leftMap133 rightMap133 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice15 : Residual1Cache.slice leftMap133 rightMap133 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice16 : Residual1Cache.slice leftMap133 rightMap133 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice17 : Residual1Cache.slice leftMap133 rightMap133 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice18 : Residual1Cache.slice leftMap133 rightMap133 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice19 : Residual1Cache.slice leftMap133 rightMap133 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice20 : Residual1Cache.slice leftMap133 rightMap133 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice21 : Residual1Cache.slice leftMap133 rightMap133 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice22 : Residual1Cache.slice leftMap133 rightMap133 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice23 : Residual1Cache.slice leftMap133 rightMap133 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice24 : Residual1Cache.slice leftMap133 rightMap133 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice25 : Residual1Cache.slice leftMap133 rightMap133 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice26 : Residual1Cache.slice leftMap133 rightMap133 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice27 : Residual1Cache.slice leftMap133 rightMap133 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice28 : Residual1Cache.slice leftMap133 rightMap133 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice29 : Residual1Cache.slice leftMap133 rightMap133 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice30 : Residual1Cache.slice leftMap133 rightMap133 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice31 : Residual1Cache.slice leftMap133 rightMap133 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice32 : Residual1Cache.slice leftMap133 rightMap133 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice33 : Residual1Cache.slice leftMap133 rightMap133 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice34 : Residual1Cache.slice leftMap133 rightMap133 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice35 : Residual1Cache.slice leftMap133 rightMap133 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice36 : Residual1Cache.slice leftMap133 rightMap133 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice37 : Residual1Cache.slice leftMap133 rightMap133 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice38 : Residual1Cache.slice leftMap133 rightMap133 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice39 : Residual1Cache.slice leftMap133 rightMap133 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice40 : Residual1Cache.slice leftMap133 rightMap133 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice41 : Residual1Cache.slice leftMap133 rightMap133 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice42 : Residual1Cache.slice leftMap133 rightMap133 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice43 : Residual1Cache.slice leftMap133 rightMap133 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice44 : Residual1Cache.slice leftMap133 rightMap133 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice45 : Residual1Cache.slice leftMap133 rightMap133 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice46 : Residual1Cache.slice leftMap133 rightMap133 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice47 : Residual1Cache.slice leftMap133 rightMap133 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice48 : Residual1Cache.slice leftMap133 rightMap133 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice49 : Residual1Cache.slice leftMap133 rightMap133 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice50 : Residual1Cache.slice leftMap133 rightMap133 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice51 : Residual1Cache.slice leftMap133 rightMap133 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice52 : Residual1Cache.slice leftMap133 rightMap133 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice53 : Residual1Cache.slice leftMap133 rightMap133 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice54 : Residual1Cache.slice leftMap133 rightMap133 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice55 : Residual1Cache.slice leftMap133 rightMap133 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice56 : Residual1Cache.slice leftMap133 rightMap133 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice57 : Residual1Cache.slice leftMap133 rightMap133 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice58 : Residual1Cache.slice leftMap133 rightMap133 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice59 : Residual1Cache.slice leftMap133 rightMap133 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice60 : Residual1Cache.slice leftMap133 rightMap133 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice61 : Residual1Cache.slice leftMap133 rightMap133 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice62 : Residual1Cache.slice leftMap133 rightMap133 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice63 : Residual1Cache.slice leftMap133 rightMap133 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice64 : Residual1Cache.slice leftMap133 rightMap133 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice65 : Residual1Cache.slice leftMap133 rightMap133 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice66 : Residual1Cache.slice leftMap133 rightMap133 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice67 : Residual1Cache.slice leftMap133 rightMap133 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice68 : Residual1Cache.slice leftMap133 rightMap133 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice69 : Residual1Cache.slice leftMap133 rightMap133 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice70 : Residual1Cache.slice leftMap133 rightMap133 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice71 : Residual1Cache.slice leftMap133 rightMap133 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice72 : Residual1Cache.slice leftMap133 rightMap133 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice73 : Residual1Cache.slice leftMap133 rightMap133 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice74 : Residual1Cache.slice leftMap133 rightMap133 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice75 : Residual1Cache.slice leftMap133 rightMap133 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice76 : Residual1Cache.slice leftMap133 rightMap133 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice77 : Residual1Cache.slice leftMap133 rightMap133 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice78 : Residual1Cache.slice leftMap133 rightMap133 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice79 : Residual1Cache.slice leftMap133 rightMap133 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice80 : Residual1Cache.slice leftMap133 rightMap133 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice81 : Residual1Cache.slice leftMap133 rightMap133 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice82 : Residual1Cache.slice leftMap133 rightMap133 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice83 : Residual1Cache.slice leftMap133 rightMap133 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice84 : Residual1Cache.slice leftMap133 rightMap133 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice85 : Residual1Cache.slice leftMap133 rightMap133 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice86 : Residual1Cache.slice leftMap133 rightMap133 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice87 : Residual1Cache.slice leftMap133 rightMap133 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice88 : Residual1Cache.slice leftMap133 rightMap133 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice89 : Residual1Cache.slice leftMap133 rightMap133 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice90 : Residual1Cache.slice leftMap133 rightMap133 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice91 : Residual1Cache.slice leftMap133 rightMap133 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice92 : Residual1Cache.slice leftMap133 rightMap133 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice93 : Residual1Cache.slice leftMap133 rightMap133 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice94 : Residual1Cache.slice leftMap133 rightMap133 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice95 : Residual1Cache.slice leftMap133 rightMap133 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice96 : Residual1Cache.slice leftMap133 rightMap133 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice97 : Residual1Cache.slice leftMap133 rightMap133 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice98 : Residual1Cache.slice leftMap133 rightMap133 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice99 : Residual1Cache.slice leftMap133 rightMap133 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice100 : Residual1Cache.slice leftMap133 rightMap133 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice101 : Residual1Cache.slice leftMap133 rightMap133 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice102 : Residual1Cache.slice leftMap133 rightMap133 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice103 : Residual1Cache.slice leftMap133 rightMap133 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice104 : Residual1Cache.slice leftMap133 rightMap133 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice105 : Residual1Cache.slice leftMap133 rightMap133 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice106 : Residual1Cache.slice leftMap133 rightMap133 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice107 : Residual1Cache.slice leftMap133 rightMap133 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice108 : Residual1Cache.slice leftMap133 rightMap133 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice109 : Residual1Cache.slice leftMap133 rightMap133 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice110 : Residual1Cache.slice leftMap133 rightMap133 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice111 : Residual1Cache.slice leftMap133 rightMap133 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice112 : Residual1Cache.slice leftMap133 rightMap133 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice113 : Residual1Cache.slice leftMap133 rightMap133 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice114 : Residual1Cache.slice leftMap133 rightMap133 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice115 : Residual1Cache.slice leftMap133 rightMap133 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice116 : Residual1Cache.slice leftMap133 rightMap133 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice117 : Residual1Cache.slice leftMap133 rightMap133 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice118 : Residual1Cache.slice leftMap133 rightMap133 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice119 : Residual1Cache.slice leftMap133 rightMap133 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice120 : Residual1Cache.slice leftMap133 rightMap133 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice121 : Residual1Cache.slice leftMap133 rightMap133 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice122 : Residual1Cache.slice leftMap133 rightMap133 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice123 : Residual1Cache.slice leftMap133 rightMap133 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice124 : Residual1Cache.slice leftMap133 rightMap133 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice125 : Residual1Cache.slice leftMap133 rightMap133 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice126 : Residual1Cache.slice leftMap133 rightMap133 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice127 : Residual1Cache.slice leftMap133 rightMap133 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice128 : Residual1Cache.slice leftMap133 rightMap133 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice129 : Residual1Cache.slice leftMap133 rightMap133 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice130 : Residual1Cache.slice leftMap133 rightMap133 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice131 : Residual1Cache.slice leftMap133 rightMap133 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice132 : Residual1Cache.slice leftMap133 rightMap133 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice133 : Residual1Cache.slice leftMap133 rightMap133 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice134 : Residual1Cache.slice leftMap133 rightMap133 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice135 : Residual1Cache.slice leftMap133 rightMap133 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice136 : Residual1Cache.slice leftMap133 rightMap133 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice137 : Residual1Cache.slice leftMap133 rightMap133 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice138 : Residual1Cache.slice leftMap133 rightMap133 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice139 : Residual1Cache.slice leftMap133 rightMap133 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice140 : Residual1Cache.slice leftMap133 rightMap133 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice141 : Residual1Cache.slice leftMap133 rightMap133 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice142 : Residual1Cache.slice leftMap133 rightMap133 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice143 : Residual1Cache.slice leftMap133 rightMap133 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice144 : Residual1Cache.slice leftMap133 rightMap133 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice145 : Residual1Cache.slice leftMap133 rightMap133 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice146 : Residual1Cache.slice leftMap133 rightMap133 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice147 : Residual1Cache.slice leftMap133 rightMap133 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice148 : Residual1Cache.slice leftMap133 rightMap133 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice149 : Residual1Cache.slice leftMap133 rightMap133 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice150 : Residual1Cache.slice leftMap133 rightMap133 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice151 : Residual1Cache.slice leftMap133 rightMap133 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice152 : Residual1Cache.slice leftMap133 rightMap133 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice153 : Residual1Cache.slice leftMap133 rightMap133 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice154 : Residual1Cache.slice leftMap133 rightMap133 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice155 : Residual1Cache.slice leftMap133 rightMap133 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice156 : Residual1Cache.slice leftMap133 rightMap133 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice157 : Residual1Cache.slice leftMap133 rightMap133 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice158 : Residual1Cache.slice leftMap133 rightMap133 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice159 : Residual1Cache.slice leftMap133 rightMap133 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice160 : Residual1Cache.slice leftMap133 rightMap133 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice161 : Residual1Cache.slice leftMap133 rightMap133 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice162 : Residual1Cache.slice leftMap133 rightMap133 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice163 : Residual1Cache.slice leftMap133 rightMap133 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice164 : Residual1Cache.slice leftMap133 rightMap133 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice165 : Residual1Cache.slice leftMap133 rightMap133 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice166 : Residual1Cache.slice leftMap133 rightMap133 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice167 : Residual1Cache.slice leftMap133 rightMap133 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice168 : Residual1Cache.slice leftMap133 rightMap133 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice169 : Residual1Cache.slice leftMap133 rightMap133 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice170 : Residual1Cache.slice leftMap133 rightMap133 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice171 : Residual1Cache.slice leftMap133 rightMap133 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice172 : Residual1Cache.slice leftMap133 rightMap133 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice173 : Residual1Cache.slice leftMap133 rightMap133 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice174 : Residual1Cache.slice leftMap133 rightMap133 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice175 : Residual1Cache.slice leftMap133 rightMap133 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice176 : Residual1Cache.slice leftMap133 rightMap133 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice177 : Residual1Cache.slice leftMap133 rightMap133 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice178 : Residual1Cache.slice leftMap133 rightMap133 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice179 : Residual1Cache.slice leftMap133 rightMap133 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice180 : Residual1Cache.slice leftMap133 rightMap133 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice181 : Residual1Cache.slice leftMap133 rightMap133 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice182 : Residual1Cache.slice leftMap133 rightMap133 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice183 : Residual1Cache.slice leftMap133 rightMap133 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice184 : Residual1Cache.slice leftMap133 rightMap133 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice185 : Residual1Cache.slice leftMap133 rightMap133 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice186 : Residual1Cache.slice leftMap133 rightMap133 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice187 : Residual1Cache.slice leftMap133 rightMap133 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice188 : Residual1Cache.slice leftMap133 rightMap133 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice189 : Residual1Cache.slice leftMap133 rightMap133 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice190 : Residual1Cache.slice leftMap133 rightMap133 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice191 : Residual1Cache.slice leftMap133 rightMap133 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice192 : Residual1Cache.slice leftMap133 rightMap133 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice193 : Residual1Cache.slice leftMap133 rightMap133 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice194 : Residual1Cache.slice leftMap133 rightMap133 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice195 : Residual1Cache.slice leftMap133 rightMap133 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice196 : Residual1Cache.slice leftMap133 rightMap133 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice197 : Residual1Cache.slice leftMap133 rightMap133 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice198 : Residual1Cache.slice leftMap133 rightMap133 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice199 : Residual1Cache.slice leftMap133 rightMap133 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice200 : Residual1Cache.slice leftMap133 rightMap133 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice201 : Residual1Cache.slice leftMap133 rightMap133 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point133slice202 : Residual1Cache.slice leftMap133 rightMap133 202 = true := by
  decide +kernel

private theorem point133_slices : ∀ c, Residual1Cache.slice leftMap133 rightMap133 c = true := by
  intro c
  fin_cases c
  · exact point133slice0
  · exact point133slice1
  · exact point133slice2
  · exact point133slice3
  · exact point133slice4
  · exact point133slice5
  · exact point133slice6
  · exact point133slice7
  · exact point133slice8
  · exact point133slice9
  · exact point133slice10
  · exact point133slice11
  · exact point133slice12
  · exact point133slice13
  · exact point133slice14
  · exact point133slice15
  · exact point133slice16
  · exact point133slice17
  · exact point133slice18
  · exact point133slice19
  · exact point133slice20
  · exact point133slice21
  · exact point133slice22
  · exact point133slice23
  · exact point133slice24
  · exact point133slice25
  · exact point133slice26
  · exact point133slice27
  · exact point133slice28
  · exact point133slice29
  · exact point133slice30
  · exact point133slice31
  · exact point133slice32
  · exact point133slice33
  · exact point133slice34
  · exact point133slice35
  · exact point133slice36
  · exact point133slice37
  · exact point133slice38
  · exact point133slice39
  · exact point133slice40
  · exact point133slice41
  · exact point133slice42
  · exact point133slice43
  · exact point133slice44
  · exact point133slice45
  · exact point133slice46
  · exact point133slice47
  · exact point133slice48
  · exact point133slice49
  · exact point133slice50
  · exact point133slice51
  · exact point133slice52
  · exact point133slice53
  · exact point133slice54
  · exact point133slice55
  · exact point133slice56
  · exact point133slice57
  · exact point133slice58
  · exact point133slice59
  · exact point133slice60
  · exact point133slice61
  · exact point133slice62
  · exact point133slice63
  · exact point133slice64
  · exact point133slice65
  · exact point133slice66
  · exact point133slice67
  · exact point133slice68
  · exact point133slice69
  · exact point133slice70
  · exact point133slice71
  · exact point133slice72
  · exact point133slice73
  · exact point133slice74
  · exact point133slice75
  · exact point133slice76
  · exact point133slice77
  · exact point133slice78
  · exact point133slice79
  · exact point133slice80
  · exact point133slice81
  · exact point133slice82
  · exact point133slice83
  · exact point133slice84
  · exact point133slice85
  · exact point133slice86
  · exact point133slice87
  · exact point133slice88
  · exact point133slice89
  · exact point133slice90
  · exact point133slice91
  · exact point133slice92
  · exact point133slice93
  · exact point133slice94
  · exact point133slice95
  · exact point133slice96
  · exact point133slice97
  · exact point133slice98
  · exact point133slice99
  · exact point133slice100
  · exact point133slice101
  · exact point133slice102
  · exact point133slice103
  · exact point133slice104
  · exact point133slice105
  · exact point133slice106
  · exact point133slice107
  · exact point133slice108
  · exact point133slice109
  · exact point133slice110
  · exact point133slice111
  · exact point133slice112
  · exact point133slice113
  · exact point133slice114
  · exact point133slice115
  · exact point133slice116
  · exact point133slice117
  · exact point133slice118
  · exact point133slice119
  · exact point133slice120
  · exact point133slice121
  · exact point133slice122
  · exact point133slice123
  · exact point133slice124
  · exact point133slice125
  · exact point133slice126
  · exact point133slice127
  · exact point133slice128
  · exact point133slice129
  · exact point133slice130
  · exact point133slice131
  · exact point133slice132
  · exact point133slice133
  · exact point133slice134
  · exact point133slice135
  · exact point133slice136
  · exact point133slice137
  · exact point133slice138
  · exact point133slice139
  · exact point133slice140
  · exact point133slice141
  · exact point133slice142
  · exact point133slice143
  · exact point133slice144
  · exact point133slice145
  · exact point133slice146
  · exact point133slice147
  · exact point133slice148
  · exact point133slice149
  · exact point133slice150
  · exact point133slice151
  · exact point133slice152
  · exact point133slice153
  · exact point133slice154
  · exact point133slice155
  · exact point133slice156
  · exact point133slice157
  · exact point133slice158
  · exact point133slice159
  · exact point133slice160
  · exact point133slice161
  · exact point133slice162
  · exact point133slice163
  · exact point133slice164
  · exact point133slice165
  · exact point133slice166
  · exact point133slice167
  · exact point133slice168
  · exact point133slice169
  · exact point133slice170
  · exact point133slice171
  · exact point133slice172
  · exact point133slice173
  · exact point133slice174
  · exact point133slice175
  · exact point133slice176
  · exact point133slice177
  · exact point133slice178
  · exact point133slice179
  · exact point133slice180
  · exact point133slice181
  · exact point133slice182
  · exact point133slice183
  · exact point133slice184
  · exact point133slice185
  · exact point133slice186
  · exact point133slice187
  · exact point133slice188
  · exact point133slice189
  · exact point133slice190
  · exact point133slice191
  · exact point133slice192
  · exact point133slice193
  · exact point133slice194
  · exact point133slice195
  · exact point133slice196
  · exact point133slice197
  · exact point133slice198
  · exact point133slice199
  · exact point133slice200
  · exact point133slice201
  · exact point133slice202

set_option maxHeartbeats 1600000 in
public theorem point133 : stepCheck 1 2700 := by
  have hleft : L0Gen 1 * L0Rep 2700 = leftPerm133 := by
    change L0Gen 1 * evalWord L0Gen [1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3] = leftPerm133
    simp only [leftPerm133, p703, p153, p92, p54, p30, p20, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2700) * evalWord L1Gen (L0Factor 1 2700) = rightPerm133 := by
    change evalWord L0Gen [3, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] * evalWord L1Gen [1, 0, 0, 1, 1, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm133
    simp only [rightPerm133, p630, p570, p390, p259, p179, p132, p109, p102, p87, p69, p58, p56, p51, p50, p49, p48, p46, p45, p44, p43, p42, p41, p40, p39, p37, p36, p35, p34, p33, p32, p31, p29, p28, p26, p25, p24, p23, p22, p21, p20, p19, p18, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2700) x =
    (L0Rep (L0Act 1 2700) * evalWord L1Gen (L0Factor 1 2700)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap133_eq, ← rightMap133_eq]
  exact Residual1Cache.ofSlices point133_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
