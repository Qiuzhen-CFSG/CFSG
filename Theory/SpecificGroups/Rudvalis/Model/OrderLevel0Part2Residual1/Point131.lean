module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level14Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 131

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap131 (x : Nat) : Nat := force t97 (force t169 (force t0 (t3 x)))
private def leftPerm131 : Equiv.Perm (Fin 4060) := p97 * (p169 * (p0 * (p3)))
private theorem leftMap131_eq (x : Fin 4060) :
    leftMap131 x.val = (leftPerm131 x).val := (compose (t := fun x => force t97 (force t169 (force t0 (t3 x)))) (a := t97) (b := fun x => force t169 (force t0 (t3 x))) (fun _ => rfl) c97 (compose (t := fun x => force t169 (force t0 (t3 x))) (a := t169) (b := fun x => force t0 (t3 x)) (fun _ => rfl) c169 (compose (t := fun x => force t0 (t3 x)) (a := t0) (b := fun x => t3 x) (fun _ => rfl) c0 c3))) x

private def rightMap131 (x : Nat) : Nat := force t483 (force t0 (force t153 (force t0 (force t179 (force t179 (force t111 (force t87 (force t74 (t192 x)))))))))
private def rightPerm131 : Equiv.Perm (Fin 4060) := p483 * (p0 * (p153 * (p0 * (p179 * (p179 * (p111 * (p87 * (p74 * (p192)))))))))
private theorem rightMap131_eq (x : Fin 4060) :
    rightMap131 x.val = (rightPerm131 x).val := (compose (t := fun x => force t483 (force t0 (force t153 (force t0 (force t179 (force t179 (force t111 (force t87 (force t74 (t192 x)))))))))) (a := t483) (b := fun x => force t0 (force t153 (force t0 (force t179 (force t179 (force t111 (force t87 (force t74 (t192 x))))))))) (fun _ => rfl) c483 (compose (t := fun x => force t0 (force t153 (force t0 (force t179 (force t179 (force t111 (force t87 (force t74 (t192 x))))))))) (a := t0) (b := fun x => force t153 (force t0 (force t179 (force t179 (force t111 (force t87 (force t74 (t192 x)))))))) (fun _ => rfl) c0 (compose (t := fun x => force t153 (force t0 (force t179 (force t179 (force t111 (force t87 (force t74 (t192 x)))))))) (a := t153) (b := fun x => force t0 (force t179 (force t179 (force t111 (force t87 (force t74 (t192 x))))))) (fun _ => rfl) c153 (compose (t := fun x => force t0 (force t179 (force t179 (force t111 (force t87 (force t74 (t192 x))))))) (a := t0) (b := fun x => force t179 (force t179 (force t111 (force t87 (force t74 (t192 x)))))) (fun _ => rfl) c0 (compose (t := fun x => force t179 (force t179 (force t111 (force t87 (force t74 (t192 x)))))) (a := t179) (b := fun x => force t179 (force t111 (force t87 (force t74 (t192 x))))) (fun _ => rfl) c179 (compose (t := fun x => force t179 (force t111 (force t87 (force t74 (t192 x))))) (a := t179) (b := fun x => force t111 (force t87 (force t74 (t192 x)))) (fun _ => rfl) c179 (compose (t := fun x => force t111 (force t87 (force t74 (t192 x)))) (a := t111) (b := fun x => force t87 (force t74 (t192 x))) (fun _ => rfl) c111 (compose (t := fun x => force t87 (force t74 (t192 x))) (a := t87) (b := fun x => force t74 (t192 x)) (fun _ => rfl) c87 (compose (t := fun x => force t74 (t192 x)) (a := t74) (b := fun x => t192 x) (fun _ => rfl) c74 c192))))))))) x

set_option maxHeartbeats 1600000 in
private theorem point131slice0 : Residual1Cache.slice leftMap131 rightMap131 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice1 : Residual1Cache.slice leftMap131 rightMap131 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice2 : Residual1Cache.slice leftMap131 rightMap131 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice3 : Residual1Cache.slice leftMap131 rightMap131 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice4 : Residual1Cache.slice leftMap131 rightMap131 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice5 : Residual1Cache.slice leftMap131 rightMap131 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice6 : Residual1Cache.slice leftMap131 rightMap131 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice7 : Residual1Cache.slice leftMap131 rightMap131 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice8 : Residual1Cache.slice leftMap131 rightMap131 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice9 : Residual1Cache.slice leftMap131 rightMap131 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice10 : Residual1Cache.slice leftMap131 rightMap131 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice11 : Residual1Cache.slice leftMap131 rightMap131 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice12 : Residual1Cache.slice leftMap131 rightMap131 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice13 : Residual1Cache.slice leftMap131 rightMap131 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice14 : Residual1Cache.slice leftMap131 rightMap131 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice15 : Residual1Cache.slice leftMap131 rightMap131 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice16 : Residual1Cache.slice leftMap131 rightMap131 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice17 : Residual1Cache.slice leftMap131 rightMap131 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice18 : Residual1Cache.slice leftMap131 rightMap131 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice19 : Residual1Cache.slice leftMap131 rightMap131 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice20 : Residual1Cache.slice leftMap131 rightMap131 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice21 : Residual1Cache.slice leftMap131 rightMap131 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice22 : Residual1Cache.slice leftMap131 rightMap131 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice23 : Residual1Cache.slice leftMap131 rightMap131 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice24 : Residual1Cache.slice leftMap131 rightMap131 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice25 : Residual1Cache.slice leftMap131 rightMap131 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice26 : Residual1Cache.slice leftMap131 rightMap131 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice27 : Residual1Cache.slice leftMap131 rightMap131 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice28 : Residual1Cache.slice leftMap131 rightMap131 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice29 : Residual1Cache.slice leftMap131 rightMap131 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice30 : Residual1Cache.slice leftMap131 rightMap131 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice31 : Residual1Cache.slice leftMap131 rightMap131 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice32 : Residual1Cache.slice leftMap131 rightMap131 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice33 : Residual1Cache.slice leftMap131 rightMap131 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice34 : Residual1Cache.slice leftMap131 rightMap131 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice35 : Residual1Cache.slice leftMap131 rightMap131 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice36 : Residual1Cache.slice leftMap131 rightMap131 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice37 : Residual1Cache.slice leftMap131 rightMap131 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice38 : Residual1Cache.slice leftMap131 rightMap131 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice39 : Residual1Cache.slice leftMap131 rightMap131 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice40 : Residual1Cache.slice leftMap131 rightMap131 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice41 : Residual1Cache.slice leftMap131 rightMap131 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice42 : Residual1Cache.slice leftMap131 rightMap131 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice43 : Residual1Cache.slice leftMap131 rightMap131 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice44 : Residual1Cache.slice leftMap131 rightMap131 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice45 : Residual1Cache.slice leftMap131 rightMap131 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice46 : Residual1Cache.slice leftMap131 rightMap131 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice47 : Residual1Cache.slice leftMap131 rightMap131 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice48 : Residual1Cache.slice leftMap131 rightMap131 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice49 : Residual1Cache.slice leftMap131 rightMap131 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice50 : Residual1Cache.slice leftMap131 rightMap131 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice51 : Residual1Cache.slice leftMap131 rightMap131 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice52 : Residual1Cache.slice leftMap131 rightMap131 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice53 : Residual1Cache.slice leftMap131 rightMap131 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice54 : Residual1Cache.slice leftMap131 rightMap131 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice55 : Residual1Cache.slice leftMap131 rightMap131 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice56 : Residual1Cache.slice leftMap131 rightMap131 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice57 : Residual1Cache.slice leftMap131 rightMap131 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice58 : Residual1Cache.slice leftMap131 rightMap131 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice59 : Residual1Cache.slice leftMap131 rightMap131 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice60 : Residual1Cache.slice leftMap131 rightMap131 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice61 : Residual1Cache.slice leftMap131 rightMap131 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice62 : Residual1Cache.slice leftMap131 rightMap131 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice63 : Residual1Cache.slice leftMap131 rightMap131 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice64 : Residual1Cache.slice leftMap131 rightMap131 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice65 : Residual1Cache.slice leftMap131 rightMap131 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice66 : Residual1Cache.slice leftMap131 rightMap131 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice67 : Residual1Cache.slice leftMap131 rightMap131 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice68 : Residual1Cache.slice leftMap131 rightMap131 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice69 : Residual1Cache.slice leftMap131 rightMap131 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice70 : Residual1Cache.slice leftMap131 rightMap131 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice71 : Residual1Cache.slice leftMap131 rightMap131 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice72 : Residual1Cache.slice leftMap131 rightMap131 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice73 : Residual1Cache.slice leftMap131 rightMap131 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice74 : Residual1Cache.slice leftMap131 rightMap131 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice75 : Residual1Cache.slice leftMap131 rightMap131 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice76 : Residual1Cache.slice leftMap131 rightMap131 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice77 : Residual1Cache.slice leftMap131 rightMap131 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice78 : Residual1Cache.slice leftMap131 rightMap131 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice79 : Residual1Cache.slice leftMap131 rightMap131 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice80 : Residual1Cache.slice leftMap131 rightMap131 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice81 : Residual1Cache.slice leftMap131 rightMap131 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice82 : Residual1Cache.slice leftMap131 rightMap131 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice83 : Residual1Cache.slice leftMap131 rightMap131 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice84 : Residual1Cache.slice leftMap131 rightMap131 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice85 : Residual1Cache.slice leftMap131 rightMap131 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice86 : Residual1Cache.slice leftMap131 rightMap131 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice87 : Residual1Cache.slice leftMap131 rightMap131 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice88 : Residual1Cache.slice leftMap131 rightMap131 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice89 : Residual1Cache.slice leftMap131 rightMap131 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice90 : Residual1Cache.slice leftMap131 rightMap131 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice91 : Residual1Cache.slice leftMap131 rightMap131 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice92 : Residual1Cache.slice leftMap131 rightMap131 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice93 : Residual1Cache.slice leftMap131 rightMap131 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice94 : Residual1Cache.slice leftMap131 rightMap131 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice95 : Residual1Cache.slice leftMap131 rightMap131 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice96 : Residual1Cache.slice leftMap131 rightMap131 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice97 : Residual1Cache.slice leftMap131 rightMap131 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice98 : Residual1Cache.slice leftMap131 rightMap131 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice99 : Residual1Cache.slice leftMap131 rightMap131 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice100 : Residual1Cache.slice leftMap131 rightMap131 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice101 : Residual1Cache.slice leftMap131 rightMap131 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice102 : Residual1Cache.slice leftMap131 rightMap131 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice103 : Residual1Cache.slice leftMap131 rightMap131 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice104 : Residual1Cache.slice leftMap131 rightMap131 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice105 : Residual1Cache.slice leftMap131 rightMap131 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice106 : Residual1Cache.slice leftMap131 rightMap131 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice107 : Residual1Cache.slice leftMap131 rightMap131 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice108 : Residual1Cache.slice leftMap131 rightMap131 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice109 : Residual1Cache.slice leftMap131 rightMap131 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice110 : Residual1Cache.slice leftMap131 rightMap131 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice111 : Residual1Cache.slice leftMap131 rightMap131 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice112 : Residual1Cache.slice leftMap131 rightMap131 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice113 : Residual1Cache.slice leftMap131 rightMap131 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice114 : Residual1Cache.slice leftMap131 rightMap131 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice115 : Residual1Cache.slice leftMap131 rightMap131 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice116 : Residual1Cache.slice leftMap131 rightMap131 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice117 : Residual1Cache.slice leftMap131 rightMap131 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice118 : Residual1Cache.slice leftMap131 rightMap131 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice119 : Residual1Cache.slice leftMap131 rightMap131 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice120 : Residual1Cache.slice leftMap131 rightMap131 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice121 : Residual1Cache.slice leftMap131 rightMap131 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice122 : Residual1Cache.slice leftMap131 rightMap131 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice123 : Residual1Cache.slice leftMap131 rightMap131 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice124 : Residual1Cache.slice leftMap131 rightMap131 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice125 : Residual1Cache.slice leftMap131 rightMap131 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice126 : Residual1Cache.slice leftMap131 rightMap131 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice127 : Residual1Cache.slice leftMap131 rightMap131 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice128 : Residual1Cache.slice leftMap131 rightMap131 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice129 : Residual1Cache.slice leftMap131 rightMap131 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice130 : Residual1Cache.slice leftMap131 rightMap131 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice131 : Residual1Cache.slice leftMap131 rightMap131 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice132 : Residual1Cache.slice leftMap131 rightMap131 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice133 : Residual1Cache.slice leftMap131 rightMap131 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice134 : Residual1Cache.slice leftMap131 rightMap131 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice135 : Residual1Cache.slice leftMap131 rightMap131 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice136 : Residual1Cache.slice leftMap131 rightMap131 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice137 : Residual1Cache.slice leftMap131 rightMap131 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice138 : Residual1Cache.slice leftMap131 rightMap131 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice139 : Residual1Cache.slice leftMap131 rightMap131 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice140 : Residual1Cache.slice leftMap131 rightMap131 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice141 : Residual1Cache.slice leftMap131 rightMap131 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice142 : Residual1Cache.slice leftMap131 rightMap131 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice143 : Residual1Cache.slice leftMap131 rightMap131 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice144 : Residual1Cache.slice leftMap131 rightMap131 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice145 : Residual1Cache.slice leftMap131 rightMap131 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice146 : Residual1Cache.slice leftMap131 rightMap131 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice147 : Residual1Cache.slice leftMap131 rightMap131 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice148 : Residual1Cache.slice leftMap131 rightMap131 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice149 : Residual1Cache.slice leftMap131 rightMap131 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice150 : Residual1Cache.slice leftMap131 rightMap131 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice151 : Residual1Cache.slice leftMap131 rightMap131 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice152 : Residual1Cache.slice leftMap131 rightMap131 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice153 : Residual1Cache.slice leftMap131 rightMap131 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice154 : Residual1Cache.slice leftMap131 rightMap131 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice155 : Residual1Cache.slice leftMap131 rightMap131 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice156 : Residual1Cache.slice leftMap131 rightMap131 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice157 : Residual1Cache.slice leftMap131 rightMap131 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice158 : Residual1Cache.slice leftMap131 rightMap131 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice159 : Residual1Cache.slice leftMap131 rightMap131 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice160 : Residual1Cache.slice leftMap131 rightMap131 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice161 : Residual1Cache.slice leftMap131 rightMap131 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice162 : Residual1Cache.slice leftMap131 rightMap131 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice163 : Residual1Cache.slice leftMap131 rightMap131 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice164 : Residual1Cache.slice leftMap131 rightMap131 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice165 : Residual1Cache.slice leftMap131 rightMap131 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice166 : Residual1Cache.slice leftMap131 rightMap131 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice167 : Residual1Cache.slice leftMap131 rightMap131 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice168 : Residual1Cache.slice leftMap131 rightMap131 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice169 : Residual1Cache.slice leftMap131 rightMap131 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice170 : Residual1Cache.slice leftMap131 rightMap131 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice171 : Residual1Cache.slice leftMap131 rightMap131 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice172 : Residual1Cache.slice leftMap131 rightMap131 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice173 : Residual1Cache.slice leftMap131 rightMap131 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice174 : Residual1Cache.slice leftMap131 rightMap131 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice175 : Residual1Cache.slice leftMap131 rightMap131 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice176 : Residual1Cache.slice leftMap131 rightMap131 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice177 : Residual1Cache.slice leftMap131 rightMap131 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice178 : Residual1Cache.slice leftMap131 rightMap131 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice179 : Residual1Cache.slice leftMap131 rightMap131 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice180 : Residual1Cache.slice leftMap131 rightMap131 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice181 : Residual1Cache.slice leftMap131 rightMap131 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice182 : Residual1Cache.slice leftMap131 rightMap131 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice183 : Residual1Cache.slice leftMap131 rightMap131 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice184 : Residual1Cache.slice leftMap131 rightMap131 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice185 : Residual1Cache.slice leftMap131 rightMap131 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice186 : Residual1Cache.slice leftMap131 rightMap131 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice187 : Residual1Cache.slice leftMap131 rightMap131 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice188 : Residual1Cache.slice leftMap131 rightMap131 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice189 : Residual1Cache.slice leftMap131 rightMap131 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice190 : Residual1Cache.slice leftMap131 rightMap131 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice191 : Residual1Cache.slice leftMap131 rightMap131 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice192 : Residual1Cache.slice leftMap131 rightMap131 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice193 : Residual1Cache.slice leftMap131 rightMap131 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice194 : Residual1Cache.slice leftMap131 rightMap131 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice195 : Residual1Cache.slice leftMap131 rightMap131 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice196 : Residual1Cache.slice leftMap131 rightMap131 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice197 : Residual1Cache.slice leftMap131 rightMap131 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice198 : Residual1Cache.slice leftMap131 rightMap131 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice199 : Residual1Cache.slice leftMap131 rightMap131 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice200 : Residual1Cache.slice leftMap131 rightMap131 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice201 : Residual1Cache.slice leftMap131 rightMap131 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point131slice202 : Residual1Cache.slice leftMap131 rightMap131 202 = true := by
  decide +kernel

private theorem point131_slices : ∀ c, Residual1Cache.slice leftMap131 rightMap131 c = true := by
  intro c
  fin_cases c
  · exact point131slice0
  · exact point131slice1
  · exact point131slice2
  · exact point131slice3
  · exact point131slice4
  · exact point131slice5
  · exact point131slice6
  · exact point131slice7
  · exact point131slice8
  · exact point131slice9
  · exact point131slice10
  · exact point131slice11
  · exact point131slice12
  · exact point131slice13
  · exact point131slice14
  · exact point131slice15
  · exact point131slice16
  · exact point131slice17
  · exact point131slice18
  · exact point131slice19
  · exact point131slice20
  · exact point131slice21
  · exact point131slice22
  · exact point131slice23
  · exact point131slice24
  · exact point131slice25
  · exact point131slice26
  · exact point131slice27
  · exact point131slice28
  · exact point131slice29
  · exact point131slice30
  · exact point131slice31
  · exact point131slice32
  · exact point131slice33
  · exact point131slice34
  · exact point131slice35
  · exact point131slice36
  · exact point131slice37
  · exact point131slice38
  · exact point131slice39
  · exact point131slice40
  · exact point131slice41
  · exact point131slice42
  · exact point131slice43
  · exact point131slice44
  · exact point131slice45
  · exact point131slice46
  · exact point131slice47
  · exact point131slice48
  · exact point131slice49
  · exact point131slice50
  · exact point131slice51
  · exact point131slice52
  · exact point131slice53
  · exact point131slice54
  · exact point131slice55
  · exact point131slice56
  · exact point131slice57
  · exact point131slice58
  · exact point131slice59
  · exact point131slice60
  · exact point131slice61
  · exact point131slice62
  · exact point131slice63
  · exact point131slice64
  · exact point131slice65
  · exact point131slice66
  · exact point131slice67
  · exact point131slice68
  · exact point131slice69
  · exact point131slice70
  · exact point131slice71
  · exact point131slice72
  · exact point131slice73
  · exact point131slice74
  · exact point131slice75
  · exact point131slice76
  · exact point131slice77
  · exact point131slice78
  · exact point131slice79
  · exact point131slice80
  · exact point131slice81
  · exact point131slice82
  · exact point131slice83
  · exact point131slice84
  · exact point131slice85
  · exact point131slice86
  · exact point131slice87
  · exact point131slice88
  · exact point131slice89
  · exact point131slice90
  · exact point131slice91
  · exact point131slice92
  · exact point131slice93
  · exact point131slice94
  · exact point131slice95
  · exact point131slice96
  · exact point131slice97
  · exact point131slice98
  · exact point131slice99
  · exact point131slice100
  · exact point131slice101
  · exact point131slice102
  · exact point131slice103
  · exact point131slice104
  · exact point131slice105
  · exact point131slice106
  · exact point131slice107
  · exact point131slice108
  · exact point131slice109
  · exact point131slice110
  · exact point131slice111
  · exact point131slice112
  · exact point131slice113
  · exact point131slice114
  · exact point131slice115
  · exact point131slice116
  · exact point131slice117
  · exact point131slice118
  · exact point131slice119
  · exact point131slice120
  · exact point131slice121
  · exact point131slice122
  · exact point131slice123
  · exact point131slice124
  · exact point131slice125
  · exact point131slice126
  · exact point131slice127
  · exact point131slice128
  · exact point131slice129
  · exact point131slice130
  · exact point131slice131
  · exact point131slice132
  · exact point131slice133
  · exact point131slice134
  · exact point131slice135
  · exact point131slice136
  · exact point131slice137
  · exact point131slice138
  · exact point131slice139
  · exact point131slice140
  · exact point131slice141
  · exact point131slice142
  · exact point131slice143
  · exact point131slice144
  · exact point131slice145
  · exact point131slice146
  · exact point131slice147
  · exact point131slice148
  · exact point131slice149
  · exact point131slice150
  · exact point131slice151
  · exact point131slice152
  · exact point131slice153
  · exact point131slice154
  · exact point131slice155
  · exact point131slice156
  · exact point131slice157
  · exact point131slice158
  · exact point131slice159
  · exact point131slice160
  · exact point131slice161
  · exact point131slice162
  · exact point131slice163
  · exact point131slice164
  · exact point131slice165
  · exact point131slice166
  · exact point131slice167
  · exact point131slice168
  · exact point131slice169
  · exact point131slice170
  · exact point131slice171
  · exact point131slice172
  · exact point131slice173
  · exact point131slice174
  · exact point131slice175
  · exact point131slice176
  · exact point131slice177
  · exact point131slice178
  · exact point131slice179
  · exact point131slice180
  · exact point131slice181
  · exact point131slice182
  · exact point131slice183
  · exact point131slice184
  · exact point131slice185
  · exact point131slice186
  · exact point131slice187
  · exact point131slice188
  · exact point131slice189
  · exact point131slice190
  · exact point131slice191
  · exact point131slice192
  · exact point131slice193
  · exact point131slice194
  · exact point131slice195
  · exact point131slice196
  · exact point131slice197
  · exact point131slice198
  · exact point131slice199
  · exact point131slice200
  · exact point131slice201
  · exact point131slice202

set_option maxHeartbeats 1600000 in
public theorem point131 : stepCheck 0 2715 := by
  have hleft : L0Gen 0 * L0Rep 2715 = leftPerm131 := by
    change L0Gen 0 * evalWord L0Gen [3, 0, 3, 0, 1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3] = leftPerm131
    simp only [leftPerm131, p169, p97, p76, p48, p47, p27, p20, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2715) * evalWord L1Gen (L0Factor 0 2715) = rightPerm131 := by
    change evalWord L0Gen [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 3, 0] * evalWord L1Gen [1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm131
    simp only [rightPerm131, p483, p192, p179, p153, p111, p87, p80, p78, p74, p70, p57, p56, p52, p51, p49, p48, p46, p45, p44, p43, p42, p41, p40, p39, p38, p37, p36, p35, p34, p33, p32, p31, p29, p28, p26, p25, p24, p23, p22, p21, p20, p19, p18, p17, p16, p15, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2715) x =
    (L0Rep (L0Act 0 2715) * evalWord L1Gen (L0Factor 0 2715)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap131_eq, ← rightMap131_eq]
  exact Residual1Cache.ofSlices point131_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
