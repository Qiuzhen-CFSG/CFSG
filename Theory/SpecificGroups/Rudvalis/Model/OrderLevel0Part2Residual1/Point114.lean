module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level12Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 114

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap114 (x : Nat) : Nat := force t137 (force t122 (t14 x))
private def leftPerm114 : Equiv.Perm (Fin 4060) := p137 * (p122 * (p14))
private theorem leftMap114_eq (x : Fin 4060) :
    leftMap114 x.val = (leftPerm114 x).val := (compose (t := fun x => force t137 (force t122 (t14 x))) (a := t137) (b := fun x => force t122 (t14 x)) (fun _ => rfl) c137 (compose (t := fun x => force t122 (t14 x)) (a := t122) (b := fun x => t14 x) (fun _ => rfl) c122 c14)) x

private def rightMap114 (x : Nat) : Nat := force t121 (force t255 (force t276 (force t780 (force t193 (force t15 (force t145 (force t259 (force t69 (force t99 (t56 x))))))))))
private def rightPerm114 : Equiv.Perm (Fin 4060) := p121 * (p255 * (p276 * (p780 * (p193 * (p15 * (p145 * (p259 * (p69 * (p99 * (p56))))))))))
private theorem rightMap114_eq (x : Fin 4060) :
    rightMap114 x.val = (rightPerm114 x).val := (compose (t := fun x => force t121 (force t255 (force t276 (force t780 (force t193 (force t15 (force t145 (force t259 (force t69 (force t99 (t56 x))))))))))) (a := t121) (b := fun x => force t255 (force t276 (force t780 (force t193 (force t15 (force t145 (force t259 (force t69 (force t99 (t56 x)))))))))) (fun _ => rfl) c121 (compose (t := fun x => force t255 (force t276 (force t780 (force t193 (force t15 (force t145 (force t259 (force t69 (force t99 (t56 x)))))))))) (a := t255) (b := fun x => force t276 (force t780 (force t193 (force t15 (force t145 (force t259 (force t69 (force t99 (t56 x))))))))) (fun _ => rfl) c255 (compose (t := fun x => force t276 (force t780 (force t193 (force t15 (force t145 (force t259 (force t69 (force t99 (t56 x))))))))) (a := t276) (b := fun x => force t780 (force t193 (force t15 (force t145 (force t259 (force t69 (force t99 (t56 x)))))))) (fun _ => rfl) c276 (compose (t := fun x => force t780 (force t193 (force t15 (force t145 (force t259 (force t69 (force t99 (t56 x)))))))) (a := t780) (b := fun x => force t193 (force t15 (force t145 (force t259 (force t69 (force t99 (t56 x))))))) (fun _ => rfl) c780 (compose (t := fun x => force t193 (force t15 (force t145 (force t259 (force t69 (force t99 (t56 x))))))) (a := t193) (b := fun x => force t15 (force t145 (force t259 (force t69 (force t99 (t56 x)))))) (fun _ => rfl) c193 (compose (t := fun x => force t15 (force t145 (force t259 (force t69 (force t99 (t56 x)))))) (a := t15) (b := fun x => force t145 (force t259 (force t69 (force t99 (t56 x))))) (fun _ => rfl) c15 (compose (t := fun x => force t145 (force t259 (force t69 (force t99 (t56 x))))) (a := t145) (b := fun x => force t259 (force t69 (force t99 (t56 x)))) (fun _ => rfl) c145 (compose (t := fun x => force t259 (force t69 (force t99 (t56 x)))) (a := t259) (b := fun x => force t69 (force t99 (t56 x))) (fun _ => rfl) c259 (compose (t := fun x => force t69 (force t99 (t56 x))) (a := t69) (b := fun x => force t99 (t56 x)) (fun _ => rfl) c69 (compose (t := fun x => force t99 (t56 x)) (a := t99) (b := fun x => t56 x) (fun _ => rfl) c99 c56)))))))))) x

set_option maxHeartbeats 1600000 in
private theorem point114slice0 : Residual1Cache.slice leftMap114 rightMap114 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice1 : Residual1Cache.slice leftMap114 rightMap114 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice2 : Residual1Cache.slice leftMap114 rightMap114 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice3 : Residual1Cache.slice leftMap114 rightMap114 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice4 : Residual1Cache.slice leftMap114 rightMap114 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice5 : Residual1Cache.slice leftMap114 rightMap114 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice6 : Residual1Cache.slice leftMap114 rightMap114 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice7 : Residual1Cache.slice leftMap114 rightMap114 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice8 : Residual1Cache.slice leftMap114 rightMap114 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice9 : Residual1Cache.slice leftMap114 rightMap114 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice10 : Residual1Cache.slice leftMap114 rightMap114 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice11 : Residual1Cache.slice leftMap114 rightMap114 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice12 : Residual1Cache.slice leftMap114 rightMap114 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice13 : Residual1Cache.slice leftMap114 rightMap114 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice14 : Residual1Cache.slice leftMap114 rightMap114 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice15 : Residual1Cache.slice leftMap114 rightMap114 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice16 : Residual1Cache.slice leftMap114 rightMap114 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice17 : Residual1Cache.slice leftMap114 rightMap114 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice18 : Residual1Cache.slice leftMap114 rightMap114 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice19 : Residual1Cache.slice leftMap114 rightMap114 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice20 : Residual1Cache.slice leftMap114 rightMap114 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice21 : Residual1Cache.slice leftMap114 rightMap114 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice22 : Residual1Cache.slice leftMap114 rightMap114 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice23 : Residual1Cache.slice leftMap114 rightMap114 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice24 : Residual1Cache.slice leftMap114 rightMap114 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice25 : Residual1Cache.slice leftMap114 rightMap114 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice26 : Residual1Cache.slice leftMap114 rightMap114 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice27 : Residual1Cache.slice leftMap114 rightMap114 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice28 : Residual1Cache.slice leftMap114 rightMap114 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice29 : Residual1Cache.slice leftMap114 rightMap114 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice30 : Residual1Cache.slice leftMap114 rightMap114 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice31 : Residual1Cache.slice leftMap114 rightMap114 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice32 : Residual1Cache.slice leftMap114 rightMap114 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice33 : Residual1Cache.slice leftMap114 rightMap114 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice34 : Residual1Cache.slice leftMap114 rightMap114 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice35 : Residual1Cache.slice leftMap114 rightMap114 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice36 : Residual1Cache.slice leftMap114 rightMap114 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice37 : Residual1Cache.slice leftMap114 rightMap114 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice38 : Residual1Cache.slice leftMap114 rightMap114 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice39 : Residual1Cache.slice leftMap114 rightMap114 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice40 : Residual1Cache.slice leftMap114 rightMap114 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice41 : Residual1Cache.slice leftMap114 rightMap114 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice42 : Residual1Cache.slice leftMap114 rightMap114 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice43 : Residual1Cache.slice leftMap114 rightMap114 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice44 : Residual1Cache.slice leftMap114 rightMap114 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice45 : Residual1Cache.slice leftMap114 rightMap114 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice46 : Residual1Cache.slice leftMap114 rightMap114 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice47 : Residual1Cache.slice leftMap114 rightMap114 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice48 : Residual1Cache.slice leftMap114 rightMap114 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice49 : Residual1Cache.slice leftMap114 rightMap114 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice50 : Residual1Cache.slice leftMap114 rightMap114 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice51 : Residual1Cache.slice leftMap114 rightMap114 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice52 : Residual1Cache.slice leftMap114 rightMap114 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice53 : Residual1Cache.slice leftMap114 rightMap114 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice54 : Residual1Cache.slice leftMap114 rightMap114 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice55 : Residual1Cache.slice leftMap114 rightMap114 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice56 : Residual1Cache.slice leftMap114 rightMap114 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice57 : Residual1Cache.slice leftMap114 rightMap114 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice58 : Residual1Cache.slice leftMap114 rightMap114 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice59 : Residual1Cache.slice leftMap114 rightMap114 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice60 : Residual1Cache.slice leftMap114 rightMap114 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice61 : Residual1Cache.slice leftMap114 rightMap114 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice62 : Residual1Cache.slice leftMap114 rightMap114 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice63 : Residual1Cache.slice leftMap114 rightMap114 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice64 : Residual1Cache.slice leftMap114 rightMap114 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice65 : Residual1Cache.slice leftMap114 rightMap114 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice66 : Residual1Cache.slice leftMap114 rightMap114 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice67 : Residual1Cache.slice leftMap114 rightMap114 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice68 : Residual1Cache.slice leftMap114 rightMap114 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice69 : Residual1Cache.slice leftMap114 rightMap114 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice70 : Residual1Cache.slice leftMap114 rightMap114 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice71 : Residual1Cache.slice leftMap114 rightMap114 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice72 : Residual1Cache.slice leftMap114 rightMap114 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice73 : Residual1Cache.slice leftMap114 rightMap114 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice74 : Residual1Cache.slice leftMap114 rightMap114 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice75 : Residual1Cache.slice leftMap114 rightMap114 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice76 : Residual1Cache.slice leftMap114 rightMap114 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice77 : Residual1Cache.slice leftMap114 rightMap114 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice78 : Residual1Cache.slice leftMap114 rightMap114 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice79 : Residual1Cache.slice leftMap114 rightMap114 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice80 : Residual1Cache.slice leftMap114 rightMap114 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice81 : Residual1Cache.slice leftMap114 rightMap114 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice82 : Residual1Cache.slice leftMap114 rightMap114 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice83 : Residual1Cache.slice leftMap114 rightMap114 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice84 : Residual1Cache.slice leftMap114 rightMap114 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice85 : Residual1Cache.slice leftMap114 rightMap114 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice86 : Residual1Cache.slice leftMap114 rightMap114 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice87 : Residual1Cache.slice leftMap114 rightMap114 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice88 : Residual1Cache.slice leftMap114 rightMap114 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice89 : Residual1Cache.slice leftMap114 rightMap114 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice90 : Residual1Cache.slice leftMap114 rightMap114 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice91 : Residual1Cache.slice leftMap114 rightMap114 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice92 : Residual1Cache.slice leftMap114 rightMap114 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice93 : Residual1Cache.slice leftMap114 rightMap114 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice94 : Residual1Cache.slice leftMap114 rightMap114 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice95 : Residual1Cache.slice leftMap114 rightMap114 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice96 : Residual1Cache.slice leftMap114 rightMap114 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice97 : Residual1Cache.slice leftMap114 rightMap114 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice98 : Residual1Cache.slice leftMap114 rightMap114 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice99 : Residual1Cache.slice leftMap114 rightMap114 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice100 : Residual1Cache.slice leftMap114 rightMap114 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice101 : Residual1Cache.slice leftMap114 rightMap114 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice102 : Residual1Cache.slice leftMap114 rightMap114 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice103 : Residual1Cache.slice leftMap114 rightMap114 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice104 : Residual1Cache.slice leftMap114 rightMap114 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice105 : Residual1Cache.slice leftMap114 rightMap114 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice106 : Residual1Cache.slice leftMap114 rightMap114 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice107 : Residual1Cache.slice leftMap114 rightMap114 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice108 : Residual1Cache.slice leftMap114 rightMap114 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice109 : Residual1Cache.slice leftMap114 rightMap114 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice110 : Residual1Cache.slice leftMap114 rightMap114 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice111 : Residual1Cache.slice leftMap114 rightMap114 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice112 : Residual1Cache.slice leftMap114 rightMap114 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice113 : Residual1Cache.slice leftMap114 rightMap114 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice114 : Residual1Cache.slice leftMap114 rightMap114 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice115 : Residual1Cache.slice leftMap114 rightMap114 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice116 : Residual1Cache.slice leftMap114 rightMap114 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice117 : Residual1Cache.slice leftMap114 rightMap114 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice118 : Residual1Cache.slice leftMap114 rightMap114 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice119 : Residual1Cache.slice leftMap114 rightMap114 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice120 : Residual1Cache.slice leftMap114 rightMap114 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice121 : Residual1Cache.slice leftMap114 rightMap114 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice122 : Residual1Cache.slice leftMap114 rightMap114 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice123 : Residual1Cache.slice leftMap114 rightMap114 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice124 : Residual1Cache.slice leftMap114 rightMap114 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice125 : Residual1Cache.slice leftMap114 rightMap114 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice126 : Residual1Cache.slice leftMap114 rightMap114 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice127 : Residual1Cache.slice leftMap114 rightMap114 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice128 : Residual1Cache.slice leftMap114 rightMap114 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice129 : Residual1Cache.slice leftMap114 rightMap114 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice130 : Residual1Cache.slice leftMap114 rightMap114 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice131 : Residual1Cache.slice leftMap114 rightMap114 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice132 : Residual1Cache.slice leftMap114 rightMap114 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice133 : Residual1Cache.slice leftMap114 rightMap114 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice134 : Residual1Cache.slice leftMap114 rightMap114 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice135 : Residual1Cache.slice leftMap114 rightMap114 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice136 : Residual1Cache.slice leftMap114 rightMap114 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice137 : Residual1Cache.slice leftMap114 rightMap114 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice138 : Residual1Cache.slice leftMap114 rightMap114 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice139 : Residual1Cache.slice leftMap114 rightMap114 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice140 : Residual1Cache.slice leftMap114 rightMap114 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice141 : Residual1Cache.slice leftMap114 rightMap114 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice142 : Residual1Cache.slice leftMap114 rightMap114 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice143 : Residual1Cache.slice leftMap114 rightMap114 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice144 : Residual1Cache.slice leftMap114 rightMap114 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice145 : Residual1Cache.slice leftMap114 rightMap114 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice146 : Residual1Cache.slice leftMap114 rightMap114 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice147 : Residual1Cache.slice leftMap114 rightMap114 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice148 : Residual1Cache.slice leftMap114 rightMap114 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice149 : Residual1Cache.slice leftMap114 rightMap114 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice150 : Residual1Cache.slice leftMap114 rightMap114 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice151 : Residual1Cache.slice leftMap114 rightMap114 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice152 : Residual1Cache.slice leftMap114 rightMap114 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice153 : Residual1Cache.slice leftMap114 rightMap114 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice154 : Residual1Cache.slice leftMap114 rightMap114 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice155 : Residual1Cache.slice leftMap114 rightMap114 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice156 : Residual1Cache.slice leftMap114 rightMap114 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice157 : Residual1Cache.slice leftMap114 rightMap114 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice158 : Residual1Cache.slice leftMap114 rightMap114 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice159 : Residual1Cache.slice leftMap114 rightMap114 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice160 : Residual1Cache.slice leftMap114 rightMap114 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice161 : Residual1Cache.slice leftMap114 rightMap114 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice162 : Residual1Cache.slice leftMap114 rightMap114 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice163 : Residual1Cache.slice leftMap114 rightMap114 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice164 : Residual1Cache.slice leftMap114 rightMap114 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice165 : Residual1Cache.slice leftMap114 rightMap114 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice166 : Residual1Cache.slice leftMap114 rightMap114 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice167 : Residual1Cache.slice leftMap114 rightMap114 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice168 : Residual1Cache.slice leftMap114 rightMap114 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice169 : Residual1Cache.slice leftMap114 rightMap114 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice170 : Residual1Cache.slice leftMap114 rightMap114 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice171 : Residual1Cache.slice leftMap114 rightMap114 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice172 : Residual1Cache.slice leftMap114 rightMap114 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice173 : Residual1Cache.slice leftMap114 rightMap114 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice174 : Residual1Cache.slice leftMap114 rightMap114 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice175 : Residual1Cache.slice leftMap114 rightMap114 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice176 : Residual1Cache.slice leftMap114 rightMap114 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice177 : Residual1Cache.slice leftMap114 rightMap114 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice178 : Residual1Cache.slice leftMap114 rightMap114 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice179 : Residual1Cache.slice leftMap114 rightMap114 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice180 : Residual1Cache.slice leftMap114 rightMap114 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice181 : Residual1Cache.slice leftMap114 rightMap114 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice182 : Residual1Cache.slice leftMap114 rightMap114 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice183 : Residual1Cache.slice leftMap114 rightMap114 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice184 : Residual1Cache.slice leftMap114 rightMap114 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice185 : Residual1Cache.slice leftMap114 rightMap114 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice186 : Residual1Cache.slice leftMap114 rightMap114 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice187 : Residual1Cache.slice leftMap114 rightMap114 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice188 : Residual1Cache.slice leftMap114 rightMap114 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice189 : Residual1Cache.slice leftMap114 rightMap114 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice190 : Residual1Cache.slice leftMap114 rightMap114 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice191 : Residual1Cache.slice leftMap114 rightMap114 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice192 : Residual1Cache.slice leftMap114 rightMap114 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice193 : Residual1Cache.slice leftMap114 rightMap114 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice194 : Residual1Cache.slice leftMap114 rightMap114 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice195 : Residual1Cache.slice leftMap114 rightMap114 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice196 : Residual1Cache.slice leftMap114 rightMap114 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice197 : Residual1Cache.slice leftMap114 rightMap114 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice198 : Residual1Cache.slice leftMap114 rightMap114 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice199 : Residual1Cache.slice leftMap114 rightMap114 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice200 : Residual1Cache.slice leftMap114 rightMap114 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice201 : Residual1Cache.slice leftMap114 rightMap114 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point114slice202 : Residual1Cache.slice leftMap114 rightMap114 202 = true := by
  decide +kernel

private theorem point114_slices : ∀ c, Residual1Cache.slice leftMap114 rightMap114 c = true := by
  intro c
  fin_cases c
  · exact point114slice0
  · exact point114slice1
  · exact point114slice2
  · exact point114slice3
  · exact point114slice4
  · exact point114slice5
  · exact point114slice6
  · exact point114slice7
  · exact point114slice8
  · exact point114slice9
  · exact point114slice10
  · exact point114slice11
  · exact point114slice12
  · exact point114slice13
  · exact point114slice14
  · exact point114slice15
  · exact point114slice16
  · exact point114slice17
  · exact point114slice18
  · exact point114slice19
  · exact point114slice20
  · exact point114slice21
  · exact point114slice22
  · exact point114slice23
  · exact point114slice24
  · exact point114slice25
  · exact point114slice26
  · exact point114slice27
  · exact point114slice28
  · exact point114slice29
  · exact point114slice30
  · exact point114slice31
  · exact point114slice32
  · exact point114slice33
  · exact point114slice34
  · exact point114slice35
  · exact point114slice36
  · exact point114slice37
  · exact point114slice38
  · exact point114slice39
  · exact point114slice40
  · exact point114slice41
  · exact point114slice42
  · exact point114slice43
  · exact point114slice44
  · exact point114slice45
  · exact point114slice46
  · exact point114slice47
  · exact point114slice48
  · exact point114slice49
  · exact point114slice50
  · exact point114slice51
  · exact point114slice52
  · exact point114slice53
  · exact point114slice54
  · exact point114slice55
  · exact point114slice56
  · exact point114slice57
  · exact point114slice58
  · exact point114slice59
  · exact point114slice60
  · exact point114slice61
  · exact point114slice62
  · exact point114slice63
  · exact point114slice64
  · exact point114slice65
  · exact point114slice66
  · exact point114slice67
  · exact point114slice68
  · exact point114slice69
  · exact point114slice70
  · exact point114slice71
  · exact point114slice72
  · exact point114slice73
  · exact point114slice74
  · exact point114slice75
  · exact point114slice76
  · exact point114slice77
  · exact point114slice78
  · exact point114slice79
  · exact point114slice80
  · exact point114slice81
  · exact point114slice82
  · exact point114slice83
  · exact point114slice84
  · exact point114slice85
  · exact point114slice86
  · exact point114slice87
  · exact point114slice88
  · exact point114slice89
  · exact point114slice90
  · exact point114slice91
  · exact point114slice92
  · exact point114slice93
  · exact point114slice94
  · exact point114slice95
  · exact point114slice96
  · exact point114slice97
  · exact point114slice98
  · exact point114slice99
  · exact point114slice100
  · exact point114slice101
  · exact point114slice102
  · exact point114slice103
  · exact point114slice104
  · exact point114slice105
  · exact point114slice106
  · exact point114slice107
  · exact point114slice108
  · exact point114slice109
  · exact point114slice110
  · exact point114slice111
  · exact point114slice112
  · exact point114slice113
  · exact point114slice114
  · exact point114slice115
  · exact point114slice116
  · exact point114slice117
  · exact point114slice118
  · exact point114slice119
  · exact point114slice120
  · exact point114slice121
  · exact point114slice122
  · exact point114slice123
  · exact point114slice124
  · exact point114slice125
  · exact point114slice126
  · exact point114slice127
  · exact point114slice128
  · exact point114slice129
  · exact point114slice130
  · exact point114slice131
  · exact point114slice132
  · exact point114slice133
  · exact point114slice134
  · exact point114slice135
  · exact point114slice136
  · exact point114slice137
  · exact point114slice138
  · exact point114slice139
  · exact point114slice140
  · exact point114slice141
  · exact point114slice142
  · exact point114slice143
  · exact point114slice144
  · exact point114slice145
  · exact point114slice146
  · exact point114slice147
  · exact point114slice148
  · exact point114slice149
  · exact point114slice150
  · exact point114slice151
  · exact point114slice152
  · exact point114slice153
  · exact point114slice154
  · exact point114slice155
  · exact point114slice156
  · exact point114slice157
  · exact point114slice158
  · exact point114slice159
  · exact point114slice160
  · exact point114slice161
  · exact point114slice162
  · exact point114slice163
  · exact point114slice164
  · exact point114slice165
  · exact point114slice166
  · exact point114slice167
  · exact point114slice168
  · exact point114slice169
  · exact point114slice170
  · exact point114slice171
  · exact point114slice172
  · exact point114slice173
  · exact point114slice174
  · exact point114slice175
  · exact point114slice176
  · exact point114slice177
  · exact point114slice178
  · exact point114slice179
  · exact point114slice180
  · exact point114slice181
  · exact point114slice182
  · exact point114slice183
  · exact point114slice184
  · exact point114slice185
  · exact point114slice186
  · exact point114slice187
  · exact point114slice188
  · exact point114slice189
  · exact point114slice190
  · exact point114slice191
  · exact point114slice192
  · exact point114slice193
  · exact point114slice194
  · exact point114slice195
  · exact point114slice196
  · exact point114slice197
  · exact point114slice198
  · exact point114slice199
  · exact point114slice200
  · exact point114slice201
  · exact point114slice202

set_option maxHeartbeats 1600000 in
public theorem point114 : stepCheck 1 2420 := by
  have hleft : L0Gen 1 * L0Rep 2420 = leftPerm114 := by
    change L0Gen 1 * evalWord L0Gen [0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0] = leftPerm114
    simp only [leftPerm114, p137, p122, p47, p27, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2420) * evalWord L1Gen (L0Factor 1 2420) = rightPerm114 := by
    change evalWord L0Gen [3, 0, 3, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] * evalWord L1Gen [1, 2, 3, 2, 1, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm114
    simp only [rightPerm114, p780, p276, p259, p255, p193, p145, p121, p99, p94, p90, p85, p69, p60, p56, p51, p49, p48, p46, p45, p44, p43, p42, p41, p40, p39, p37, p36, p35, p34, p33, p32, p31, p29, p28, p27, p26, p24, p23, p22, p21, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2420) x =
    (L0Rep (L0Act 1 2420) * evalWord L1Gen (L0Factor 1 2420)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap114_eq, ← rightMap114_eq]
  exact Residual1Cache.ofSlices point114_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
