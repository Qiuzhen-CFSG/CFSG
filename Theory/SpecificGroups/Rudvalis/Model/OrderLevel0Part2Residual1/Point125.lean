module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level07Part1
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 125

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap125 (x : Nat) : Nat := force t840 (force t50 (t48 x))
private def leftPerm125 : Equiv.Perm (Fin 4060) := p840 * (p50 * (p48))
private theorem leftMap125_eq (x : Fin 4060) :
    leftMap125 x.val = (leftPerm125 x).val := (compose (t := fun x => force t840 (force t50 (t48 x))) (a := t840) (b := fun x => force t50 (t48 x)) (fun _ => rfl) c840 (compose (t := fun x => force t50 (t48 x)) (a := t50) (b := fun x => t48 x) (fun _ => rfl) c50 c48)) x

private def rightMap125 (x : Nat) : Nat := force t149 (force t740 (force t0 (force t10 (force t84 (force t12 (force t261 (force t105 (force t269 (force t747 (t31 x))))))))))
private def rightPerm125 : Equiv.Perm (Fin 4060) := p149 * (p740 * (p0 * (p10 * (p84 * (p12 * (p261 * (p105 * (p269 * (p747 * (p31))))))))))
private theorem rightMap125_eq (x : Fin 4060) :
    rightMap125 x.val = (rightPerm125 x).val := (compose (t := fun x => force t149 (force t740 (force t0 (force t10 (force t84 (force t12 (force t261 (force t105 (force t269 (force t747 (t31 x))))))))))) (a := t149) (b := fun x => force t740 (force t0 (force t10 (force t84 (force t12 (force t261 (force t105 (force t269 (force t747 (t31 x)))))))))) (fun _ => rfl) c149 (compose (t := fun x => force t740 (force t0 (force t10 (force t84 (force t12 (force t261 (force t105 (force t269 (force t747 (t31 x)))))))))) (a := t740) (b := fun x => force t0 (force t10 (force t84 (force t12 (force t261 (force t105 (force t269 (force t747 (t31 x))))))))) (fun _ => rfl) c740 (compose (t := fun x => force t0 (force t10 (force t84 (force t12 (force t261 (force t105 (force t269 (force t747 (t31 x))))))))) (a := t0) (b := fun x => force t10 (force t84 (force t12 (force t261 (force t105 (force t269 (force t747 (t31 x)))))))) (fun _ => rfl) c0 (compose (t := fun x => force t10 (force t84 (force t12 (force t261 (force t105 (force t269 (force t747 (t31 x)))))))) (a := t10) (b := fun x => force t84 (force t12 (force t261 (force t105 (force t269 (force t747 (t31 x))))))) (fun _ => rfl) c10 (compose (t := fun x => force t84 (force t12 (force t261 (force t105 (force t269 (force t747 (t31 x))))))) (a := t84) (b := fun x => force t12 (force t261 (force t105 (force t269 (force t747 (t31 x)))))) (fun _ => rfl) c84 (compose (t := fun x => force t12 (force t261 (force t105 (force t269 (force t747 (t31 x)))))) (a := t12) (b := fun x => force t261 (force t105 (force t269 (force t747 (t31 x))))) (fun _ => rfl) c12 (compose (t := fun x => force t261 (force t105 (force t269 (force t747 (t31 x))))) (a := t261) (b := fun x => force t105 (force t269 (force t747 (t31 x)))) (fun _ => rfl) c261 (compose (t := fun x => force t105 (force t269 (force t747 (t31 x)))) (a := t105) (b := fun x => force t269 (force t747 (t31 x))) (fun _ => rfl) c105 (compose (t := fun x => force t269 (force t747 (t31 x))) (a := t269) (b := fun x => force t747 (t31 x)) (fun _ => rfl) c269 (compose (t := fun x => force t747 (t31 x)) (a := t747) (b := fun x => t31 x) (fun _ => rfl) c747 c31)))))))))) x

set_option maxHeartbeats 1600000 in
private theorem point125slice0 : Residual1Cache.slice leftMap125 rightMap125 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice1 : Residual1Cache.slice leftMap125 rightMap125 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice2 : Residual1Cache.slice leftMap125 rightMap125 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice3 : Residual1Cache.slice leftMap125 rightMap125 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice4 : Residual1Cache.slice leftMap125 rightMap125 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice5 : Residual1Cache.slice leftMap125 rightMap125 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice6 : Residual1Cache.slice leftMap125 rightMap125 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice7 : Residual1Cache.slice leftMap125 rightMap125 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice8 : Residual1Cache.slice leftMap125 rightMap125 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice9 : Residual1Cache.slice leftMap125 rightMap125 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice10 : Residual1Cache.slice leftMap125 rightMap125 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice11 : Residual1Cache.slice leftMap125 rightMap125 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice12 : Residual1Cache.slice leftMap125 rightMap125 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice13 : Residual1Cache.slice leftMap125 rightMap125 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice14 : Residual1Cache.slice leftMap125 rightMap125 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice15 : Residual1Cache.slice leftMap125 rightMap125 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice16 : Residual1Cache.slice leftMap125 rightMap125 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice17 : Residual1Cache.slice leftMap125 rightMap125 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice18 : Residual1Cache.slice leftMap125 rightMap125 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice19 : Residual1Cache.slice leftMap125 rightMap125 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice20 : Residual1Cache.slice leftMap125 rightMap125 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice21 : Residual1Cache.slice leftMap125 rightMap125 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice22 : Residual1Cache.slice leftMap125 rightMap125 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice23 : Residual1Cache.slice leftMap125 rightMap125 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice24 : Residual1Cache.slice leftMap125 rightMap125 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice25 : Residual1Cache.slice leftMap125 rightMap125 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice26 : Residual1Cache.slice leftMap125 rightMap125 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice27 : Residual1Cache.slice leftMap125 rightMap125 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice28 : Residual1Cache.slice leftMap125 rightMap125 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice29 : Residual1Cache.slice leftMap125 rightMap125 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice30 : Residual1Cache.slice leftMap125 rightMap125 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice31 : Residual1Cache.slice leftMap125 rightMap125 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice32 : Residual1Cache.slice leftMap125 rightMap125 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice33 : Residual1Cache.slice leftMap125 rightMap125 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice34 : Residual1Cache.slice leftMap125 rightMap125 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice35 : Residual1Cache.slice leftMap125 rightMap125 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice36 : Residual1Cache.slice leftMap125 rightMap125 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice37 : Residual1Cache.slice leftMap125 rightMap125 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice38 : Residual1Cache.slice leftMap125 rightMap125 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice39 : Residual1Cache.slice leftMap125 rightMap125 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice40 : Residual1Cache.slice leftMap125 rightMap125 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice41 : Residual1Cache.slice leftMap125 rightMap125 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice42 : Residual1Cache.slice leftMap125 rightMap125 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice43 : Residual1Cache.slice leftMap125 rightMap125 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice44 : Residual1Cache.slice leftMap125 rightMap125 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice45 : Residual1Cache.slice leftMap125 rightMap125 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice46 : Residual1Cache.slice leftMap125 rightMap125 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice47 : Residual1Cache.slice leftMap125 rightMap125 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice48 : Residual1Cache.slice leftMap125 rightMap125 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice49 : Residual1Cache.slice leftMap125 rightMap125 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice50 : Residual1Cache.slice leftMap125 rightMap125 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice51 : Residual1Cache.slice leftMap125 rightMap125 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice52 : Residual1Cache.slice leftMap125 rightMap125 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice53 : Residual1Cache.slice leftMap125 rightMap125 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice54 : Residual1Cache.slice leftMap125 rightMap125 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice55 : Residual1Cache.slice leftMap125 rightMap125 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice56 : Residual1Cache.slice leftMap125 rightMap125 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice57 : Residual1Cache.slice leftMap125 rightMap125 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice58 : Residual1Cache.slice leftMap125 rightMap125 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice59 : Residual1Cache.slice leftMap125 rightMap125 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice60 : Residual1Cache.slice leftMap125 rightMap125 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice61 : Residual1Cache.slice leftMap125 rightMap125 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice62 : Residual1Cache.slice leftMap125 rightMap125 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice63 : Residual1Cache.slice leftMap125 rightMap125 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice64 : Residual1Cache.slice leftMap125 rightMap125 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice65 : Residual1Cache.slice leftMap125 rightMap125 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice66 : Residual1Cache.slice leftMap125 rightMap125 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice67 : Residual1Cache.slice leftMap125 rightMap125 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice68 : Residual1Cache.slice leftMap125 rightMap125 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice69 : Residual1Cache.slice leftMap125 rightMap125 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice70 : Residual1Cache.slice leftMap125 rightMap125 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice71 : Residual1Cache.slice leftMap125 rightMap125 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice72 : Residual1Cache.slice leftMap125 rightMap125 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice73 : Residual1Cache.slice leftMap125 rightMap125 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice74 : Residual1Cache.slice leftMap125 rightMap125 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice75 : Residual1Cache.slice leftMap125 rightMap125 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice76 : Residual1Cache.slice leftMap125 rightMap125 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice77 : Residual1Cache.slice leftMap125 rightMap125 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice78 : Residual1Cache.slice leftMap125 rightMap125 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice79 : Residual1Cache.slice leftMap125 rightMap125 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice80 : Residual1Cache.slice leftMap125 rightMap125 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice81 : Residual1Cache.slice leftMap125 rightMap125 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice82 : Residual1Cache.slice leftMap125 rightMap125 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice83 : Residual1Cache.slice leftMap125 rightMap125 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice84 : Residual1Cache.slice leftMap125 rightMap125 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice85 : Residual1Cache.slice leftMap125 rightMap125 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice86 : Residual1Cache.slice leftMap125 rightMap125 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice87 : Residual1Cache.slice leftMap125 rightMap125 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice88 : Residual1Cache.slice leftMap125 rightMap125 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice89 : Residual1Cache.slice leftMap125 rightMap125 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice90 : Residual1Cache.slice leftMap125 rightMap125 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice91 : Residual1Cache.slice leftMap125 rightMap125 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice92 : Residual1Cache.slice leftMap125 rightMap125 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice93 : Residual1Cache.slice leftMap125 rightMap125 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice94 : Residual1Cache.slice leftMap125 rightMap125 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice95 : Residual1Cache.slice leftMap125 rightMap125 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice96 : Residual1Cache.slice leftMap125 rightMap125 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice97 : Residual1Cache.slice leftMap125 rightMap125 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice98 : Residual1Cache.slice leftMap125 rightMap125 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice99 : Residual1Cache.slice leftMap125 rightMap125 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice100 : Residual1Cache.slice leftMap125 rightMap125 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice101 : Residual1Cache.slice leftMap125 rightMap125 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice102 : Residual1Cache.slice leftMap125 rightMap125 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice103 : Residual1Cache.slice leftMap125 rightMap125 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice104 : Residual1Cache.slice leftMap125 rightMap125 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice105 : Residual1Cache.slice leftMap125 rightMap125 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice106 : Residual1Cache.slice leftMap125 rightMap125 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice107 : Residual1Cache.slice leftMap125 rightMap125 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice108 : Residual1Cache.slice leftMap125 rightMap125 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice109 : Residual1Cache.slice leftMap125 rightMap125 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice110 : Residual1Cache.slice leftMap125 rightMap125 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice111 : Residual1Cache.slice leftMap125 rightMap125 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice112 : Residual1Cache.slice leftMap125 rightMap125 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice113 : Residual1Cache.slice leftMap125 rightMap125 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice114 : Residual1Cache.slice leftMap125 rightMap125 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice115 : Residual1Cache.slice leftMap125 rightMap125 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice116 : Residual1Cache.slice leftMap125 rightMap125 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice117 : Residual1Cache.slice leftMap125 rightMap125 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice118 : Residual1Cache.slice leftMap125 rightMap125 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice119 : Residual1Cache.slice leftMap125 rightMap125 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice120 : Residual1Cache.slice leftMap125 rightMap125 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice121 : Residual1Cache.slice leftMap125 rightMap125 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice122 : Residual1Cache.slice leftMap125 rightMap125 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice123 : Residual1Cache.slice leftMap125 rightMap125 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice124 : Residual1Cache.slice leftMap125 rightMap125 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice125 : Residual1Cache.slice leftMap125 rightMap125 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice126 : Residual1Cache.slice leftMap125 rightMap125 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice127 : Residual1Cache.slice leftMap125 rightMap125 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice128 : Residual1Cache.slice leftMap125 rightMap125 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice129 : Residual1Cache.slice leftMap125 rightMap125 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice130 : Residual1Cache.slice leftMap125 rightMap125 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice131 : Residual1Cache.slice leftMap125 rightMap125 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice132 : Residual1Cache.slice leftMap125 rightMap125 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice133 : Residual1Cache.slice leftMap125 rightMap125 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice134 : Residual1Cache.slice leftMap125 rightMap125 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice135 : Residual1Cache.slice leftMap125 rightMap125 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice136 : Residual1Cache.slice leftMap125 rightMap125 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice137 : Residual1Cache.slice leftMap125 rightMap125 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice138 : Residual1Cache.slice leftMap125 rightMap125 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice139 : Residual1Cache.slice leftMap125 rightMap125 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice140 : Residual1Cache.slice leftMap125 rightMap125 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice141 : Residual1Cache.slice leftMap125 rightMap125 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice142 : Residual1Cache.slice leftMap125 rightMap125 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice143 : Residual1Cache.slice leftMap125 rightMap125 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice144 : Residual1Cache.slice leftMap125 rightMap125 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice145 : Residual1Cache.slice leftMap125 rightMap125 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice146 : Residual1Cache.slice leftMap125 rightMap125 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice147 : Residual1Cache.slice leftMap125 rightMap125 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice148 : Residual1Cache.slice leftMap125 rightMap125 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice149 : Residual1Cache.slice leftMap125 rightMap125 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice150 : Residual1Cache.slice leftMap125 rightMap125 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice151 : Residual1Cache.slice leftMap125 rightMap125 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice152 : Residual1Cache.slice leftMap125 rightMap125 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice153 : Residual1Cache.slice leftMap125 rightMap125 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice154 : Residual1Cache.slice leftMap125 rightMap125 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice155 : Residual1Cache.slice leftMap125 rightMap125 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice156 : Residual1Cache.slice leftMap125 rightMap125 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice157 : Residual1Cache.slice leftMap125 rightMap125 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice158 : Residual1Cache.slice leftMap125 rightMap125 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice159 : Residual1Cache.slice leftMap125 rightMap125 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice160 : Residual1Cache.slice leftMap125 rightMap125 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice161 : Residual1Cache.slice leftMap125 rightMap125 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice162 : Residual1Cache.slice leftMap125 rightMap125 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice163 : Residual1Cache.slice leftMap125 rightMap125 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice164 : Residual1Cache.slice leftMap125 rightMap125 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice165 : Residual1Cache.slice leftMap125 rightMap125 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice166 : Residual1Cache.slice leftMap125 rightMap125 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice167 : Residual1Cache.slice leftMap125 rightMap125 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice168 : Residual1Cache.slice leftMap125 rightMap125 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice169 : Residual1Cache.slice leftMap125 rightMap125 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice170 : Residual1Cache.slice leftMap125 rightMap125 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice171 : Residual1Cache.slice leftMap125 rightMap125 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice172 : Residual1Cache.slice leftMap125 rightMap125 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice173 : Residual1Cache.slice leftMap125 rightMap125 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice174 : Residual1Cache.slice leftMap125 rightMap125 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice175 : Residual1Cache.slice leftMap125 rightMap125 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice176 : Residual1Cache.slice leftMap125 rightMap125 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice177 : Residual1Cache.slice leftMap125 rightMap125 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice178 : Residual1Cache.slice leftMap125 rightMap125 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice179 : Residual1Cache.slice leftMap125 rightMap125 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice180 : Residual1Cache.slice leftMap125 rightMap125 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice181 : Residual1Cache.slice leftMap125 rightMap125 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice182 : Residual1Cache.slice leftMap125 rightMap125 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice183 : Residual1Cache.slice leftMap125 rightMap125 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice184 : Residual1Cache.slice leftMap125 rightMap125 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice185 : Residual1Cache.slice leftMap125 rightMap125 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice186 : Residual1Cache.slice leftMap125 rightMap125 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice187 : Residual1Cache.slice leftMap125 rightMap125 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice188 : Residual1Cache.slice leftMap125 rightMap125 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice189 : Residual1Cache.slice leftMap125 rightMap125 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice190 : Residual1Cache.slice leftMap125 rightMap125 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice191 : Residual1Cache.slice leftMap125 rightMap125 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice192 : Residual1Cache.slice leftMap125 rightMap125 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice193 : Residual1Cache.slice leftMap125 rightMap125 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice194 : Residual1Cache.slice leftMap125 rightMap125 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice195 : Residual1Cache.slice leftMap125 rightMap125 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice196 : Residual1Cache.slice leftMap125 rightMap125 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice197 : Residual1Cache.slice leftMap125 rightMap125 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice198 : Residual1Cache.slice leftMap125 rightMap125 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice199 : Residual1Cache.slice leftMap125 rightMap125 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice200 : Residual1Cache.slice leftMap125 rightMap125 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice201 : Residual1Cache.slice leftMap125 rightMap125 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point125slice202 : Residual1Cache.slice leftMap125 rightMap125 202 = true := by
  decide +kernel

private theorem point125_slices : ∀ c, Residual1Cache.slice leftMap125 rightMap125 c = true := by
  intro c
  fin_cases c
  · exact point125slice0
  · exact point125slice1
  · exact point125slice2
  · exact point125slice3
  · exact point125slice4
  · exact point125slice5
  · exact point125slice6
  · exact point125slice7
  · exact point125slice8
  · exact point125slice9
  · exact point125slice10
  · exact point125slice11
  · exact point125slice12
  · exact point125slice13
  · exact point125slice14
  · exact point125slice15
  · exact point125slice16
  · exact point125slice17
  · exact point125slice18
  · exact point125slice19
  · exact point125slice20
  · exact point125slice21
  · exact point125slice22
  · exact point125slice23
  · exact point125slice24
  · exact point125slice25
  · exact point125slice26
  · exact point125slice27
  · exact point125slice28
  · exact point125slice29
  · exact point125slice30
  · exact point125slice31
  · exact point125slice32
  · exact point125slice33
  · exact point125slice34
  · exact point125slice35
  · exact point125slice36
  · exact point125slice37
  · exact point125slice38
  · exact point125slice39
  · exact point125slice40
  · exact point125slice41
  · exact point125slice42
  · exact point125slice43
  · exact point125slice44
  · exact point125slice45
  · exact point125slice46
  · exact point125slice47
  · exact point125slice48
  · exact point125slice49
  · exact point125slice50
  · exact point125slice51
  · exact point125slice52
  · exact point125slice53
  · exact point125slice54
  · exact point125slice55
  · exact point125slice56
  · exact point125slice57
  · exact point125slice58
  · exact point125slice59
  · exact point125slice60
  · exact point125slice61
  · exact point125slice62
  · exact point125slice63
  · exact point125slice64
  · exact point125slice65
  · exact point125slice66
  · exact point125slice67
  · exact point125slice68
  · exact point125slice69
  · exact point125slice70
  · exact point125slice71
  · exact point125slice72
  · exact point125slice73
  · exact point125slice74
  · exact point125slice75
  · exact point125slice76
  · exact point125slice77
  · exact point125slice78
  · exact point125slice79
  · exact point125slice80
  · exact point125slice81
  · exact point125slice82
  · exact point125slice83
  · exact point125slice84
  · exact point125slice85
  · exact point125slice86
  · exact point125slice87
  · exact point125slice88
  · exact point125slice89
  · exact point125slice90
  · exact point125slice91
  · exact point125slice92
  · exact point125slice93
  · exact point125slice94
  · exact point125slice95
  · exact point125slice96
  · exact point125slice97
  · exact point125slice98
  · exact point125slice99
  · exact point125slice100
  · exact point125slice101
  · exact point125slice102
  · exact point125slice103
  · exact point125slice104
  · exact point125slice105
  · exact point125slice106
  · exact point125slice107
  · exact point125slice108
  · exact point125slice109
  · exact point125slice110
  · exact point125slice111
  · exact point125slice112
  · exact point125slice113
  · exact point125slice114
  · exact point125slice115
  · exact point125slice116
  · exact point125slice117
  · exact point125slice118
  · exact point125slice119
  · exact point125slice120
  · exact point125slice121
  · exact point125slice122
  · exact point125slice123
  · exact point125slice124
  · exact point125slice125
  · exact point125slice126
  · exact point125slice127
  · exact point125slice128
  · exact point125slice129
  · exact point125slice130
  · exact point125slice131
  · exact point125slice132
  · exact point125slice133
  · exact point125slice134
  · exact point125slice135
  · exact point125slice136
  · exact point125slice137
  · exact point125slice138
  · exact point125slice139
  · exact point125slice140
  · exact point125slice141
  · exact point125slice142
  · exact point125slice143
  · exact point125slice144
  · exact point125slice145
  · exact point125slice146
  · exact point125slice147
  · exact point125slice148
  · exact point125slice149
  · exact point125slice150
  · exact point125slice151
  · exact point125slice152
  · exact point125slice153
  · exact point125slice154
  · exact point125slice155
  · exact point125slice156
  · exact point125slice157
  · exact point125slice158
  · exact point125slice159
  · exact point125slice160
  · exact point125slice161
  · exact point125slice162
  · exact point125slice163
  · exact point125slice164
  · exact point125slice165
  · exact point125slice166
  · exact point125slice167
  · exact point125slice168
  · exact point125slice169
  · exact point125slice170
  · exact point125slice171
  · exact point125slice172
  · exact point125slice173
  · exact point125slice174
  · exact point125slice175
  · exact point125slice176
  · exact point125slice177
  · exact point125slice178
  · exact point125slice179
  · exact point125slice180
  · exact point125slice181
  · exact point125slice182
  · exact point125slice183
  · exact point125slice184
  · exact point125slice185
  · exact point125slice186
  · exact point125slice187
  · exact point125slice188
  · exact point125slice189
  · exact point125slice190
  · exact point125slice191
  · exact point125slice192
  · exact point125slice193
  · exact point125slice194
  · exact point125slice195
  · exact point125slice196
  · exact point125slice197
  · exact point125slice198
  · exact point125slice199
  · exact point125slice200
  · exact point125slice201
  · exact point125slice202

set_option maxHeartbeats 1600000 in
public theorem point125 : stepCheck 1 2577 := by
  have hleft : L0Gen 1 * L0Rep 2577 = leftPerm125 := by
    change L0Gen 1 * evalWord L0Gen [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] = leftPerm125
    simp only [leftPerm125, p840, p50, p48, p30, p20, p17, p11, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2577) * evalWord L1Gen (L0Factor 1 2577) = rightPerm125 := by
    change evalWord L0Gen [3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0] * evalWord L1Gen [3, 2, 1, 1, 0, 0, 1, 0, 3, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm125
    simp only [rightPerm125, p747, p740, p269, p261, p239, p149, p105, p84, p69, p47, p35, p34, p32, p31, p27, p26, p23, p22, p21, p19, p18, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2577) x =
    (L0Rep (L0Act 1 2577) * evalWord L1Gen (L0Factor 1 2577)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap125_eq, ← rightMap125_eq]
  exact Residual1Cache.ofSlices point125_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
