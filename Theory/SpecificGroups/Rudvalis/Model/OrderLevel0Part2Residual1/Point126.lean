module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level14Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 126

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap126 (x : Nat) : Nat := force t374 (force t107 (t48 x))
private def leftPerm126 : Equiv.Perm (Fin 4060) := p374 * (p107 * (p48))
private theorem leftMap126_eq (x : Fin 4060) :
    leftMap126 x.val = (leftPerm126 x).val := (compose (t := fun x => force t374 (force t107 (t48 x))) (a := t374) (b := fun x => force t107 (t48 x)) (fun _ => rfl) c374 (compose (t := fun x => force t107 (t48 x)) (a := t107) (b := fun x => t48 x) (fun _ => rfl) c107 c48)) x

private def rightMap126 (x : Nat) : Nat := force t228 (force t374 (force t3 (force t12 (force t10 (force t276 (force t58 (force t57 (force t69 (force t24 (t139 x))))))))))
private def rightPerm126 : Equiv.Perm (Fin 4060) := p228 * (p374 * (p3 * (p12 * (p10 * (p276 * (p58 * (p57 * (p69 * (p24 * (p139))))))))))
private theorem rightMap126_eq (x : Fin 4060) :
    rightMap126 x.val = (rightPerm126 x).val := (compose (t := fun x => force t228 (force t374 (force t3 (force t12 (force t10 (force t276 (force t58 (force t57 (force t69 (force t24 (t139 x))))))))))) (a := t228) (b := fun x => force t374 (force t3 (force t12 (force t10 (force t276 (force t58 (force t57 (force t69 (force t24 (t139 x)))))))))) (fun _ => rfl) c228 (compose (t := fun x => force t374 (force t3 (force t12 (force t10 (force t276 (force t58 (force t57 (force t69 (force t24 (t139 x)))))))))) (a := t374) (b := fun x => force t3 (force t12 (force t10 (force t276 (force t58 (force t57 (force t69 (force t24 (t139 x))))))))) (fun _ => rfl) c374 (compose (t := fun x => force t3 (force t12 (force t10 (force t276 (force t58 (force t57 (force t69 (force t24 (t139 x))))))))) (a := t3) (b := fun x => force t12 (force t10 (force t276 (force t58 (force t57 (force t69 (force t24 (t139 x)))))))) (fun _ => rfl) c3 (compose (t := fun x => force t12 (force t10 (force t276 (force t58 (force t57 (force t69 (force t24 (t139 x)))))))) (a := t12) (b := fun x => force t10 (force t276 (force t58 (force t57 (force t69 (force t24 (t139 x))))))) (fun _ => rfl) c12 (compose (t := fun x => force t10 (force t276 (force t58 (force t57 (force t69 (force t24 (t139 x))))))) (a := t10) (b := fun x => force t276 (force t58 (force t57 (force t69 (force t24 (t139 x)))))) (fun _ => rfl) c10 (compose (t := fun x => force t276 (force t58 (force t57 (force t69 (force t24 (t139 x)))))) (a := t276) (b := fun x => force t58 (force t57 (force t69 (force t24 (t139 x))))) (fun _ => rfl) c276 (compose (t := fun x => force t58 (force t57 (force t69 (force t24 (t139 x))))) (a := t58) (b := fun x => force t57 (force t69 (force t24 (t139 x)))) (fun _ => rfl) c58 (compose (t := fun x => force t57 (force t69 (force t24 (t139 x)))) (a := t57) (b := fun x => force t69 (force t24 (t139 x))) (fun _ => rfl) c57 (compose (t := fun x => force t69 (force t24 (t139 x))) (a := t69) (b := fun x => force t24 (t139 x)) (fun _ => rfl) c69 (compose (t := fun x => force t24 (t139 x)) (a := t24) (b := fun x => t139 x) (fun _ => rfl) c24 c139)))))))))) x

set_option maxHeartbeats 1600000 in
private theorem point126slice0 : Residual1Cache.slice leftMap126 rightMap126 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice1 : Residual1Cache.slice leftMap126 rightMap126 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice2 : Residual1Cache.slice leftMap126 rightMap126 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice3 : Residual1Cache.slice leftMap126 rightMap126 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice4 : Residual1Cache.slice leftMap126 rightMap126 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice5 : Residual1Cache.slice leftMap126 rightMap126 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice6 : Residual1Cache.slice leftMap126 rightMap126 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice7 : Residual1Cache.slice leftMap126 rightMap126 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice8 : Residual1Cache.slice leftMap126 rightMap126 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice9 : Residual1Cache.slice leftMap126 rightMap126 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice10 : Residual1Cache.slice leftMap126 rightMap126 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice11 : Residual1Cache.slice leftMap126 rightMap126 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice12 : Residual1Cache.slice leftMap126 rightMap126 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice13 : Residual1Cache.slice leftMap126 rightMap126 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice14 : Residual1Cache.slice leftMap126 rightMap126 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice15 : Residual1Cache.slice leftMap126 rightMap126 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice16 : Residual1Cache.slice leftMap126 rightMap126 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice17 : Residual1Cache.slice leftMap126 rightMap126 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice18 : Residual1Cache.slice leftMap126 rightMap126 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice19 : Residual1Cache.slice leftMap126 rightMap126 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice20 : Residual1Cache.slice leftMap126 rightMap126 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice21 : Residual1Cache.slice leftMap126 rightMap126 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice22 : Residual1Cache.slice leftMap126 rightMap126 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice23 : Residual1Cache.slice leftMap126 rightMap126 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice24 : Residual1Cache.slice leftMap126 rightMap126 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice25 : Residual1Cache.slice leftMap126 rightMap126 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice26 : Residual1Cache.slice leftMap126 rightMap126 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice27 : Residual1Cache.slice leftMap126 rightMap126 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice28 : Residual1Cache.slice leftMap126 rightMap126 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice29 : Residual1Cache.slice leftMap126 rightMap126 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice30 : Residual1Cache.slice leftMap126 rightMap126 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice31 : Residual1Cache.slice leftMap126 rightMap126 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice32 : Residual1Cache.slice leftMap126 rightMap126 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice33 : Residual1Cache.slice leftMap126 rightMap126 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice34 : Residual1Cache.slice leftMap126 rightMap126 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice35 : Residual1Cache.slice leftMap126 rightMap126 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice36 : Residual1Cache.slice leftMap126 rightMap126 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice37 : Residual1Cache.slice leftMap126 rightMap126 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice38 : Residual1Cache.slice leftMap126 rightMap126 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice39 : Residual1Cache.slice leftMap126 rightMap126 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice40 : Residual1Cache.slice leftMap126 rightMap126 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice41 : Residual1Cache.slice leftMap126 rightMap126 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice42 : Residual1Cache.slice leftMap126 rightMap126 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice43 : Residual1Cache.slice leftMap126 rightMap126 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice44 : Residual1Cache.slice leftMap126 rightMap126 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice45 : Residual1Cache.slice leftMap126 rightMap126 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice46 : Residual1Cache.slice leftMap126 rightMap126 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice47 : Residual1Cache.slice leftMap126 rightMap126 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice48 : Residual1Cache.slice leftMap126 rightMap126 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice49 : Residual1Cache.slice leftMap126 rightMap126 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice50 : Residual1Cache.slice leftMap126 rightMap126 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice51 : Residual1Cache.slice leftMap126 rightMap126 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice52 : Residual1Cache.slice leftMap126 rightMap126 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice53 : Residual1Cache.slice leftMap126 rightMap126 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice54 : Residual1Cache.slice leftMap126 rightMap126 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice55 : Residual1Cache.slice leftMap126 rightMap126 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice56 : Residual1Cache.slice leftMap126 rightMap126 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice57 : Residual1Cache.slice leftMap126 rightMap126 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice58 : Residual1Cache.slice leftMap126 rightMap126 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice59 : Residual1Cache.slice leftMap126 rightMap126 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice60 : Residual1Cache.slice leftMap126 rightMap126 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice61 : Residual1Cache.slice leftMap126 rightMap126 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice62 : Residual1Cache.slice leftMap126 rightMap126 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice63 : Residual1Cache.slice leftMap126 rightMap126 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice64 : Residual1Cache.slice leftMap126 rightMap126 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice65 : Residual1Cache.slice leftMap126 rightMap126 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice66 : Residual1Cache.slice leftMap126 rightMap126 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice67 : Residual1Cache.slice leftMap126 rightMap126 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice68 : Residual1Cache.slice leftMap126 rightMap126 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice69 : Residual1Cache.slice leftMap126 rightMap126 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice70 : Residual1Cache.slice leftMap126 rightMap126 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice71 : Residual1Cache.slice leftMap126 rightMap126 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice72 : Residual1Cache.slice leftMap126 rightMap126 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice73 : Residual1Cache.slice leftMap126 rightMap126 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice74 : Residual1Cache.slice leftMap126 rightMap126 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice75 : Residual1Cache.slice leftMap126 rightMap126 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice76 : Residual1Cache.slice leftMap126 rightMap126 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice77 : Residual1Cache.slice leftMap126 rightMap126 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice78 : Residual1Cache.slice leftMap126 rightMap126 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice79 : Residual1Cache.slice leftMap126 rightMap126 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice80 : Residual1Cache.slice leftMap126 rightMap126 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice81 : Residual1Cache.slice leftMap126 rightMap126 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice82 : Residual1Cache.slice leftMap126 rightMap126 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice83 : Residual1Cache.slice leftMap126 rightMap126 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice84 : Residual1Cache.slice leftMap126 rightMap126 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice85 : Residual1Cache.slice leftMap126 rightMap126 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice86 : Residual1Cache.slice leftMap126 rightMap126 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice87 : Residual1Cache.slice leftMap126 rightMap126 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice88 : Residual1Cache.slice leftMap126 rightMap126 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice89 : Residual1Cache.slice leftMap126 rightMap126 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice90 : Residual1Cache.slice leftMap126 rightMap126 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice91 : Residual1Cache.slice leftMap126 rightMap126 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice92 : Residual1Cache.slice leftMap126 rightMap126 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice93 : Residual1Cache.slice leftMap126 rightMap126 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice94 : Residual1Cache.slice leftMap126 rightMap126 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice95 : Residual1Cache.slice leftMap126 rightMap126 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice96 : Residual1Cache.slice leftMap126 rightMap126 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice97 : Residual1Cache.slice leftMap126 rightMap126 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice98 : Residual1Cache.slice leftMap126 rightMap126 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice99 : Residual1Cache.slice leftMap126 rightMap126 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice100 : Residual1Cache.slice leftMap126 rightMap126 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice101 : Residual1Cache.slice leftMap126 rightMap126 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice102 : Residual1Cache.slice leftMap126 rightMap126 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice103 : Residual1Cache.slice leftMap126 rightMap126 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice104 : Residual1Cache.slice leftMap126 rightMap126 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice105 : Residual1Cache.slice leftMap126 rightMap126 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice106 : Residual1Cache.slice leftMap126 rightMap126 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice107 : Residual1Cache.slice leftMap126 rightMap126 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice108 : Residual1Cache.slice leftMap126 rightMap126 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice109 : Residual1Cache.slice leftMap126 rightMap126 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice110 : Residual1Cache.slice leftMap126 rightMap126 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice111 : Residual1Cache.slice leftMap126 rightMap126 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice112 : Residual1Cache.slice leftMap126 rightMap126 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice113 : Residual1Cache.slice leftMap126 rightMap126 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice114 : Residual1Cache.slice leftMap126 rightMap126 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice115 : Residual1Cache.slice leftMap126 rightMap126 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice116 : Residual1Cache.slice leftMap126 rightMap126 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice117 : Residual1Cache.slice leftMap126 rightMap126 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice118 : Residual1Cache.slice leftMap126 rightMap126 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice119 : Residual1Cache.slice leftMap126 rightMap126 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice120 : Residual1Cache.slice leftMap126 rightMap126 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice121 : Residual1Cache.slice leftMap126 rightMap126 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice122 : Residual1Cache.slice leftMap126 rightMap126 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice123 : Residual1Cache.slice leftMap126 rightMap126 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice124 : Residual1Cache.slice leftMap126 rightMap126 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice125 : Residual1Cache.slice leftMap126 rightMap126 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice126 : Residual1Cache.slice leftMap126 rightMap126 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice127 : Residual1Cache.slice leftMap126 rightMap126 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice128 : Residual1Cache.slice leftMap126 rightMap126 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice129 : Residual1Cache.slice leftMap126 rightMap126 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice130 : Residual1Cache.slice leftMap126 rightMap126 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice131 : Residual1Cache.slice leftMap126 rightMap126 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice132 : Residual1Cache.slice leftMap126 rightMap126 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice133 : Residual1Cache.slice leftMap126 rightMap126 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice134 : Residual1Cache.slice leftMap126 rightMap126 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice135 : Residual1Cache.slice leftMap126 rightMap126 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice136 : Residual1Cache.slice leftMap126 rightMap126 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice137 : Residual1Cache.slice leftMap126 rightMap126 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice138 : Residual1Cache.slice leftMap126 rightMap126 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice139 : Residual1Cache.slice leftMap126 rightMap126 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice140 : Residual1Cache.slice leftMap126 rightMap126 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice141 : Residual1Cache.slice leftMap126 rightMap126 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice142 : Residual1Cache.slice leftMap126 rightMap126 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice143 : Residual1Cache.slice leftMap126 rightMap126 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice144 : Residual1Cache.slice leftMap126 rightMap126 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice145 : Residual1Cache.slice leftMap126 rightMap126 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice146 : Residual1Cache.slice leftMap126 rightMap126 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice147 : Residual1Cache.slice leftMap126 rightMap126 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice148 : Residual1Cache.slice leftMap126 rightMap126 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice149 : Residual1Cache.slice leftMap126 rightMap126 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice150 : Residual1Cache.slice leftMap126 rightMap126 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice151 : Residual1Cache.slice leftMap126 rightMap126 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice152 : Residual1Cache.slice leftMap126 rightMap126 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice153 : Residual1Cache.slice leftMap126 rightMap126 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice154 : Residual1Cache.slice leftMap126 rightMap126 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice155 : Residual1Cache.slice leftMap126 rightMap126 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice156 : Residual1Cache.slice leftMap126 rightMap126 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice157 : Residual1Cache.slice leftMap126 rightMap126 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice158 : Residual1Cache.slice leftMap126 rightMap126 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice159 : Residual1Cache.slice leftMap126 rightMap126 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice160 : Residual1Cache.slice leftMap126 rightMap126 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice161 : Residual1Cache.slice leftMap126 rightMap126 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice162 : Residual1Cache.slice leftMap126 rightMap126 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice163 : Residual1Cache.slice leftMap126 rightMap126 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice164 : Residual1Cache.slice leftMap126 rightMap126 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice165 : Residual1Cache.slice leftMap126 rightMap126 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice166 : Residual1Cache.slice leftMap126 rightMap126 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice167 : Residual1Cache.slice leftMap126 rightMap126 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice168 : Residual1Cache.slice leftMap126 rightMap126 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice169 : Residual1Cache.slice leftMap126 rightMap126 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice170 : Residual1Cache.slice leftMap126 rightMap126 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice171 : Residual1Cache.slice leftMap126 rightMap126 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice172 : Residual1Cache.slice leftMap126 rightMap126 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice173 : Residual1Cache.slice leftMap126 rightMap126 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice174 : Residual1Cache.slice leftMap126 rightMap126 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice175 : Residual1Cache.slice leftMap126 rightMap126 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice176 : Residual1Cache.slice leftMap126 rightMap126 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice177 : Residual1Cache.slice leftMap126 rightMap126 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice178 : Residual1Cache.slice leftMap126 rightMap126 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice179 : Residual1Cache.slice leftMap126 rightMap126 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice180 : Residual1Cache.slice leftMap126 rightMap126 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice181 : Residual1Cache.slice leftMap126 rightMap126 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice182 : Residual1Cache.slice leftMap126 rightMap126 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice183 : Residual1Cache.slice leftMap126 rightMap126 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice184 : Residual1Cache.slice leftMap126 rightMap126 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice185 : Residual1Cache.slice leftMap126 rightMap126 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice186 : Residual1Cache.slice leftMap126 rightMap126 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice187 : Residual1Cache.slice leftMap126 rightMap126 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice188 : Residual1Cache.slice leftMap126 rightMap126 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice189 : Residual1Cache.slice leftMap126 rightMap126 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice190 : Residual1Cache.slice leftMap126 rightMap126 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice191 : Residual1Cache.slice leftMap126 rightMap126 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice192 : Residual1Cache.slice leftMap126 rightMap126 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice193 : Residual1Cache.slice leftMap126 rightMap126 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice194 : Residual1Cache.slice leftMap126 rightMap126 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice195 : Residual1Cache.slice leftMap126 rightMap126 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice196 : Residual1Cache.slice leftMap126 rightMap126 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice197 : Residual1Cache.slice leftMap126 rightMap126 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice198 : Residual1Cache.slice leftMap126 rightMap126 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice199 : Residual1Cache.slice leftMap126 rightMap126 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice200 : Residual1Cache.slice leftMap126 rightMap126 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice201 : Residual1Cache.slice leftMap126 rightMap126 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point126slice202 : Residual1Cache.slice leftMap126 rightMap126 202 = true := by
  decide +kernel

private theorem point126_slices : ∀ c, Residual1Cache.slice leftMap126 rightMap126 c = true := by
  intro c
  fin_cases c
  · exact point126slice0
  · exact point126slice1
  · exact point126slice2
  · exact point126slice3
  · exact point126slice4
  · exact point126slice5
  · exact point126slice6
  · exact point126slice7
  · exact point126slice8
  · exact point126slice9
  · exact point126slice10
  · exact point126slice11
  · exact point126slice12
  · exact point126slice13
  · exact point126slice14
  · exact point126slice15
  · exact point126slice16
  · exact point126slice17
  · exact point126slice18
  · exact point126slice19
  · exact point126slice20
  · exact point126slice21
  · exact point126slice22
  · exact point126slice23
  · exact point126slice24
  · exact point126slice25
  · exact point126slice26
  · exact point126slice27
  · exact point126slice28
  · exact point126slice29
  · exact point126slice30
  · exact point126slice31
  · exact point126slice32
  · exact point126slice33
  · exact point126slice34
  · exact point126slice35
  · exact point126slice36
  · exact point126slice37
  · exact point126slice38
  · exact point126slice39
  · exact point126slice40
  · exact point126slice41
  · exact point126slice42
  · exact point126slice43
  · exact point126slice44
  · exact point126slice45
  · exact point126slice46
  · exact point126slice47
  · exact point126slice48
  · exact point126slice49
  · exact point126slice50
  · exact point126slice51
  · exact point126slice52
  · exact point126slice53
  · exact point126slice54
  · exact point126slice55
  · exact point126slice56
  · exact point126slice57
  · exact point126slice58
  · exact point126slice59
  · exact point126slice60
  · exact point126slice61
  · exact point126slice62
  · exact point126slice63
  · exact point126slice64
  · exact point126slice65
  · exact point126slice66
  · exact point126slice67
  · exact point126slice68
  · exact point126slice69
  · exact point126slice70
  · exact point126slice71
  · exact point126slice72
  · exact point126slice73
  · exact point126slice74
  · exact point126slice75
  · exact point126slice76
  · exact point126slice77
  · exact point126slice78
  · exact point126slice79
  · exact point126slice80
  · exact point126slice81
  · exact point126slice82
  · exact point126slice83
  · exact point126slice84
  · exact point126slice85
  · exact point126slice86
  · exact point126slice87
  · exact point126slice88
  · exact point126slice89
  · exact point126slice90
  · exact point126slice91
  · exact point126slice92
  · exact point126slice93
  · exact point126slice94
  · exact point126slice95
  · exact point126slice96
  · exact point126slice97
  · exact point126slice98
  · exact point126slice99
  · exact point126slice100
  · exact point126slice101
  · exact point126slice102
  · exact point126slice103
  · exact point126slice104
  · exact point126slice105
  · exact point126slice106
  · exact point126slice107
  · exact point126slice108
  · exact point126slice109
  · exact point126slice110
  · exact point126slice111
  · exact point126slice112
  · exact point126slice113
  · exact point126slice114
  · exact point126slice115
  · exact point126slice116
  · exact point126slice117
  · exact point126slice118
  · exact point126slice119
  · exact point126slice120
  · exact point126slice121
  · exact point126slice122
  · exact point126slice123
  · exact point126slice124
  · exact point126slice125
  · exact point126slice126
  · exact point126slice127
  · exact point126slice128
  · exact point126slice129
  · exact point126slice130
  · exact point126slice131
  · exact point126slice132
  · exact point126slice133
  · exact point126slice134
  · exact point126slice135
  · exact point126slice136
  · exact point126slice137
  · exact point126slice138
  · exact point126slice139
  · exact point126slice140
  · exact point126slice141
  · exact point126slice142
  · exact point126slice143
  · exact point126slice144
  · exact point126slice145
  · exact point126slice146
  · exact point126slice147
  · exact point126slice148
  · exact point126slice149
  · exact point126slice150
  · exact point126slice151
  · exact point126slice152
  · exact point126slice153
  · exact point126slice154
  · exact point126slice155
  · exact point126slice156
  · exact point126slice157
  · exact point126slice158
  · exact point126slice159
  · exact point126slice160
  · exact point126slice161
  · exact point126slice162
  · exact point126slice163
  · exact point126slice164
  · exact point126slice165
  · exact point126slice166
  · exact point126slice167
  · exact point126slice168
  · exact point126slice169
  · exact point126slice170
  · exact point126slice171
  · exact point126slice172
  · exact point126slice173
  · exact point126slice174
  · exact point126slice175
  · exact point126slice176
  · exact point126slice177
  · exact point126slice178
  · exact point126slice179
  · exact point126slice180
  · exact point126slice181
  · exact point126slice182
  · exact point126slice183
  · exact point126slice184
  · exact point126slice185
  · exact point126slice186
  · exact point126slice187
  · exact point126slice188
  · exact point126slice189
  · exact point126slice190
  · exact point126slice191
  · exact point126slice192
  · exact point126slice193
  · exact point126slice194
  · exact point126slice195
  · exact point126slice196
  · exact point126slice197
  · exact point126slice198
  · exact point126slice199
  · exact point126slice200
  · exact point126slice201
  · exact point126slice202

set_option maxHeartbeats 1600000 in
public theorem point126 : stepCheck 1 2578 := by
  have hleft : L0Gen 1 * L0Rep 2578 = leftPerm126 := by
    change L0Gen 1 * evalWord L0Gen [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] = leftPerm126
    simp only [leftPerm126, p374, p107, p50, p48, p20, p11, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2578) * evalWord L1Gen (L0Factor 1 2578) = rightPerm126 := by
    change evalWord L0Gen [0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3] * evalWord L1Gen [1, 0, 3, 2, 1, 2, 3, 2, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm126
    simp only [rightPerm126, p374, p276, p228, p139, p110, p99, p69, p58, p57, p54, p52, p51, p49, p46, p45, p44, p43, p42, p41, p39, p37, p36, p35, p34, p32, p31, p30, p29, p28, p26, p25, p24, p23, p22, p21, p20, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2578) x =
    (L0Rep (L0Act 1 2578) * evalWord L1Gen (L0Factor 1 2578)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap126_eq, ← rightMap126_eq]
  exact Residual1Cache.ofSlices point126_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
