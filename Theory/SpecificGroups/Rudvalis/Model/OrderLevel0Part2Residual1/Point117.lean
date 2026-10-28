module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level11Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 117

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap117 (x : Nat) : Nat := force t167 (force t840 (t48 x))
private def leftPerm117 : Equiv.Perm (Fin 4060) := p167 * (p840 * (p48))
private theorem leftMap117_eq (x : Fin 4060) :
    leftMap117 x.val = (leftPerm117 x).val := (compose (t := fun x => force t167 (force t840 (t48 x))) (a := t167) (b := fun x => force t840 (t48 x)) (fun _ => rfl) c167 (compose (t := fun x => force t840 (t48 x)) (a := t840) (b := fun x => t48 x) (fun _ => rfl) c840 c48)) x

private def rightMap117 (x : Nat) : Nat := force t204 (force t60 (force t12 (force t23 (force t16 (force t849 (force t58 (force t21 (t134 x))))))))
private def rightPerm117 : Equiv.Perm (Fin 4060) := p204 * (p60 * (p12 * (p23 * (p16 * (p849 * (p58 * (p21 * (p134))))))))
private theorem rightMap117_eq (x : Fin 4060) :
    rightMap117 x.val = (rightPerm117 x).val := (compose (t := fun x => force t204 (force t60 (force t12 (force t23 (force t16 (force t849 (force t58 (force t21 (t134 x))))))))) (a := t204) (b := fun x => force t60 (force t12 (force t23 (force t16 (force t849 (force t58 (force t21 (t134 x)))))))) (fun _ => rfl) c204 (compose (t := fun x => force t60 (force t12 (force t23 (force t16 (force t849 (force t58 (force t21 (t134 x)))))))) (a := t60) (b := fun x => force t12 (force t23 (force t16 (force t849 (force t58 (force t21 (t134 x))))))) (fun _ => rfl) c60 (compose (t := fun x => force t12 (force t23 (force t16 (force t849 (force t58 (force t21 (t134 x))))))) (a := t12) (b := fun x => force t23 (force t16 (force t849 (force t58 (force t21 (t134 x)))))) (fun _ => rfl) c12 (compose (t := fun x => force t23 (force t16 (force t849 (force t58 (force t21 (t134 x)))))) (a := t23) (b := fun x => force t16 (force t849 (force t58 (force t21 (t134 x))))) (fun _ => rfl) c23 (compose (t := fun x => force t16 (force t849 (force t58 (force t21 (t134 x))))) (a := t16) (b := fun x => force t849 (force t58 (force t21 (t134 x)))) (fun _ => rfl) c16 (compose (t := fun x => force t849 (force t58 (force t21 (t134 x)))) (a := t849) (b := fun x => force t58 (force t21 (t134 x))) (fun _ => rfl) c849 (compose (t := fun x => force t58 (force t21 (t134 x))) (a := t58) (b := fun x => force t21 (t134 x)) (fun _ => rfl) c58 (compose (t := fun x => force t21 (t134 x)) (a := t21) (b := fun x => t134 x) (fun _ => rfl) c21 c134)))))))) x

set_option maxHeartbeats 1600000 in
private theorem point117slice0 : Residual1Cache.slice leftMap117 rightMap117 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice1 : Residual1Cache.slice leftMap117 rightMap117 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice2 : Residual1Cache.slice leftMap117 rightMap117 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice3 : Residual1Cache.slice leftMap117 rightMap117 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice4 : Residual1Cache.slice leftMap117 rightMap117 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice5 : Residual1Cache.slice leftMap117 rightMap117 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice6 : Residual1Cache.slice leftMap117 rightMap117 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice7 : Residual1Cache.slice leftMap117 rightMap117 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice8 : Residual1Cache.slice leftMap117 rightMap117 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice9 : Residual1Cache.slice leftMap117 rightMap117 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice10 : Residual1Cache.slice leftMap117 rightMap117 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice11 : Residual1Cache.slice leftMap117 rightMap117 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice12 : Residual1Cache.slice leftMap117 rightMap117 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice13 : Residual1Cache.slice leftMap117 rightMap117 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice14 : Residual1Cache.slice leftMap117 rightMap117 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice15 : Residual1Cache.slice leftMap117 rightMap117 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice16 : Residual1Cache.slice leftMap117 rightMap117 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice17 : Residual1Cache.slice leftMap117 rightMap117 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice18 : Residual1Cache.slice leftMap117 rightMap117 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice19 : Residual1Cache.slice leftMap117 rightMap117 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice20 : Residual1Cache.slice leftMap117 rightMap117 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice21 : Residual1Cache.slice leftMap117 rightMap117 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice22 : Residual1Cache.slice leftMap117 rightMap117 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice23 : Residual1Cache.slice leftMap117 rightMap117 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice24 : Residual1Cache.slice leftMap117 rightMap117 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice25 : Residual1Cache.slice leftMap117 rightMap117 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice26 : Residual1Cache.slice leftMap117 rightMap117 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice27 : Residual1Cache.slice leftMap117 rightMap117 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice28 : Residual1Cache.slice leftMap117 rightMap117 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice29 : Residual1Cache.slice leftMap117 rightMap117 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice30 : Residual1Cache.slice leftMap117 rightMap117 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice31 : Residual1Cache.slice leftMap117 rightMap117 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice32 : Residual1Cache.slice leftMap117 rightMap117 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice33 : Residual1Cache.slice leftMap117 rightMap117 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice34 : Residual1Cache.slice leftMap117 rightMap117 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice35 : Residual1Cache.slice leftMap117 rightMap117 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice36 : Residual1Cache.slice leftMap117 rightMap117 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice37 : Residual1Cache.slice leftMap117 rightMap117 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice38 : Residual1Cache.slice leftMap117 rightMap117 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice39 : Residual1Cache.slice leftMap117 rightMap117 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice40 : Residual1Cache.slice leftMap117 rightMap117 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice41 : Residual1Cache.slice leftMap117 rightMap117 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice42 : Residual1Cache.slice leftMap117 rightMap117 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice43 : Residual1Cache.slice leftMap117 rightMap117 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice44 : Residual1Cache.slice leftMap117 rightMap117 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice45 : Residual1Cache.slice leftMap117 rightMap117 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice46 : Residual1Cache.slice leftMap117 rightMap117 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice47 : Residual1Cache.slice leftMap117 rightMap117 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice48 : Residual1Cache.slice leftMap117 rightMap117 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice49 : Residual1Cache.slice leftMap117 rightMap117 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice50 : Residual1Cache.slice leftMap117 rightMap117 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice51 : Residual1Cache.slice leftMap117 rightMap117 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice52 : Residual1Cache.slice leftMap117 rightMap117 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice53 : Residual1Cache.slice leftMap117 rightMap117 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice54 : Residual1Cache.slice leftMap117 rightMap117 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice55 : Residual1Cache.slice leftMap117 rightMap117 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice56 : Residual1Cache.slice leftMap117 rightMap117 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice57 : Residual1Cache.slice leftMap117 rightMap117 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice58 : Residual1Cache.slice leftMap117 rightMap117 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice59 : Residual1Cache.slice leftMap117 rightMap117 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice60 : Residual1Cache.slice leftMap117 rightMap117 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice61 : Residual1Cache.slice leftMap117 rightMap117 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice62 : Residual1Cache.slice leftMap117 rightMap117 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice63 : Residual1Cache.slice leftMap117 rightMap117 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice64 : Residual1Cache.slice leftMap117 rightMap117 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice65 : Residual1Cache.slice leftMap117 rightMap117 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice66 : Residual1Cache.slice leftMap117 rightMap117 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice67 : Residual1Cache.slice leftMap117 rightMap117 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice68 : Residual1Cache.slice leftMap117 rightMap117 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice69 : Residual1Cache.slice leftMap117 rightMap117 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice70 : Residual1Cache.slice leftMap117 rightMap117 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice71 : Residual1Cache.slice leftMap117 rightMap117 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice72 : Residual1Cache.slice leftMap117 rightMap117 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice73 : Residual1Cache.slice leftMap117 rightMap117 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice74 : Residual1Cache.slice leftMap117 rightMap117 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice75 : Residual1Cache.slice leftMap117 rightMap117 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice76 : Residual1Cache.slice leftMap117 rightMap117 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice77 : Residual1Cache.slice leftMap117 rightMap117 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice78 : Residual1Cache.slice leftMap117 rightMap117 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice79 : Residual1Cache.slice leftMap117 rightMap117 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice80 : Residual1Cache.slice leftMap117 rightMap117 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice81 : Residual1Cache.slice leftMap117 rightMap117 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice82 : Residual1Cache.slice leftMap117 rightMap117 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice83 : Residual1Cache.slice leftMap117 rightMap117 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice84 : Residual1Cache.slice leftMap117 rightMap117 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice85 : Residual1Cache.slice leftMap117 rightMap117 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice86 : Residual1Cache.slice leftMap117 rightMap117 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice87 : Residual1Cache.slice leftMap117 rightMap117 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice88 : Residual1Cache.slice leftMap117 rightMap117 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice89 : Residual1Cache.slice leftMap117 rightMap117 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice90 : Residual1Cache.slice leftMap117 rightMap117 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice91 : Residual1Cache.slice leftMap117 rightMap117 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice92 : Residual1Cache.slice leftMap117 rightMap117 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice93 : Residual1Cache.slice leftMap117 rightMap117 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice94 : Residual1Cache.slice leftMap117 rightMap117 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice95 : Residual1Cache.slice leftMap117 rightMap117 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice96 : Residual1Cache.slice leftMap117 rightMap117 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice97 : Residual1Cache.slice leftMap117 rightMap117 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice98 : Residual1Cache.slice leftMap117 rightMap117 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice99 : Residual1Cache.slice leftMap117 rightMap117 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice100 : Residual1Cache.slice leftMap117 rightMap117 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice101 : Residual1Cache.slice leftMap117 rightMap117 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice102 : Residual1Cache.slice leftMap117 rightMap117 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice103 : Residual1Cache.slice leftMap117 rightMap117 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice104 : Residual1Cache.slice leftMap117 rightMap117 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice105 : Residual1Cache.slice leftMap117 rightMap117 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice106 : Residual1Cache.slice leftMap117 rightMap117 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice107 : Residual1Cache.slice leftMap117 rightMap117 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice108 : Residual1Cache.slice leftMap117 rightMap117 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice109 : Residual1Cache.slice leftMap117 rightMap117 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice110 : Residual1Cache.slice leftMap117 rightMap117 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice111 : Residual1Cache.slice leftMap117 rightMap117 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice112 : Residual1Cache.slice leftMap117 rightMap117 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice113 : Residual1Cache.slice leftMap117 rightMap117 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice114 : Residual1Cache.slice leftMap117 rightMap117 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice115 : Residual1Cache.slice leftMap117 rightMap117 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice116 : Residual1Cache.slice leftMap117 rightMap117 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice117 : Residual1Cache.slice leftMap117 rightMap117 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice118 : Residual1Cache.slice leftMap117 rightMap117 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice119 : Residual1Cache.slice leftMap117 rightMap117 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice120 : Residual1Cache.slice leftMap117 rightMap117 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice121 : Residual1Cache.slice leftMap117 rightMap117 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice122 : Residual1Cache.slice leftMap117 rightMap117 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice123 : Residual1Cache.slice leftMap117 rightMap117 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice124 : Residual1Cache.slice leftMap117 rightMap117 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice125 : Residual1Cache.slice leftMap117 rightMap117 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice126 : Residual1Cache.slice leftMap117 rightMap117 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice127 : Residual1Cache.slice leftMap117 rightMap117 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice128 : Residual1Cache.slice leftMap117 rightMap117 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice129 : Residual1Cache.slice leftMap117 rightMap117 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice130 : Residual1Cache.slice leftMap117 rightMap117 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice131 : Residual1Cache.slice leftMap117 rightMap117 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice132 : Residual1Cache.slice leftMap117 rightMap117 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice133 : Residual1Cache.slice leftMap117 rightMap117 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice134 : Residual1Cache.slice leftMap117 rightMap117 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice135 : Residual1Cache.slice leftMap117 rightMap117 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice136 : Residual1Cache.slice leftMap117 rightMap117 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice137 : Residual1Cache.slice leftMap117 rightMap117 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice138 : Residual1Cache.slice leftMap117 rightMap117 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice139 : Residual1Cache.slice leftMap117 rightMap117 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice140 : Residual1Cache.slice leftMap117 rightMap117 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice141 : Residual1Cache.slice leftMap117 rightMap117 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice142 : Residual1Cache.slice leftMap117 rightMap117 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice143 : Residual1Cache.slice leftMap117 rightMap117 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice144 : Residual1Cache.slice leftMap117 rightMap117 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice145 : Residual1Cache.slice leftMap117 rightMap117 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice146 : Residual1Cache.slice leftMap117 rightMap117 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice147 : Residual1Cache.slice leftMap117 rightMap117 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice148 : Residual1Cache.slice leftMap117 rightMap117 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice149 : Residual1Cache.slice leftMap117 rightMap117 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice150 : Residual1Cache.slice leftMap117 rightMap117 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice151 : Residual1Cache.slice leftMap117 rightMap117 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice152 : Residual1Cache.slice leftMap117 rightMap117 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice153 : Residual1Cache.slice leftMap117 rightMap117 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice154 : Residual1Cache.slice leftMap117 rightMap117 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice155 : Residual1Cache.slice leftMap117 rightMap117 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice156 : Residual1Cache.slice leftMap117 rightMap117 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice157 : Residual1Cache.slice leftMap117 rightMap117 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice158 : Residual1Cache.slice leftMap117 rightMap117 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice159 : Residual1Cache.slice leftMap117 rightMap117 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice160 : Residual1Cache.slice leftMap117 rightMap117 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice161 : Residual1Cache.slice leftMap117 rightMap117 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice162 : Residual1Cache.slice leftMap117 rightMap117 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice163 : Residual1Cache.slice leftMap117 rightMap117 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice164 : Residual1Cache.slice leftMap117 rightMap117 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice165 : Residual1Cache.slice leftMap117 rightMap117 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice166 : Residual1Cache.slice leftMap117 rightMap117 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice167 : Residual1Cache.slice leftMap117 rightMap117 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice168 : Residual1Cache.slice leftMap117 rightMap117 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice169 : Residual1Cache.slice leftMap117 rightMap117 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice170 : Residual1Cache.slice leftMap117 rightMap117 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice171 : Residual1Cache.slice leftMap117 rightMap117 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice172 : Residual1Cache.slice leftMap117 rightMap117 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice173 : Residual1Cache.slice leftMap117 rightMap117 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice174 : Residual1Cache.slice leftMap117 rightMap117 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice175 : Residual1Cache.slice leftMap117 rightMap117 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice176 : Residual1Cache.slice leftMap117 rightMap117 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice177 : Residual1Cache.slice leftMap117 rightMap117 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice178 : Residual1Cache.slice leftMap117 rightMap117 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice179 : Residual1Cache.slice leftMap117 rightMap117 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice180 : Residual1Cache.slice leftMap117 rightMap117 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice181 : Residual1Cache.slice leftMap117 rightMap117 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice182 : Residual1Cache.slice leftMap117 rightMap117 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice183 : Residual1Cache.slice leftMap117 rightMap117 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice184 : Residual1Cache.slice leftMap117 rightMap117 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice185 : Residual1Cache.slice leftMap117 rightMap117 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice186 : Residual1Cache.slice leftMap117 rightMap117 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice187 : Residual1Cache.slice leftMap117 rightMap117 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice188 : Residual1Cache.slice leftMap117 rightMap117 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice189 : Residual1Cache.slice leftMap117 rightMap117 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice190 : Residual1Cache.slice leftMap117 rightMap117 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice191 : Residual1Cache.slice leftMap117 rightMap117 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice192 : Residual1Cache.slice leftMap117 rightMap117 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice193 : Residual1Cache.slice leftMap117 rightMap117 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice194 : Residual1Cache.slice leftMap117 rightMap117 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice195 : Residual1Cache.slice leftMap117 rightMap117 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice196 : Residual1Cache.slice leftMap117 rightMap117 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice197 : Residual1Cache.slice leftMap117 rightMap117 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice198 : Residual1Cache.slice leftMap117 rightMap117 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice199 : Residual1Cache.slice leftMap117 rightMap117 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice200 : Residual1Cache.slice leftMap117 rightMap117 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice201 : Residual1Cache.slice leftMap117 rightMap117 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point117slice202 : Residual1Cache.slice leftMap117 rightMap117 202 = true := by
  decide +kernel

private theorem point117_slices : ∀ c, Residual1Cache.slice leftMap117 rightMap117 c = true := by
  intro c
  fin_cases c
  · exact point117slice0
  · exact point117slice1
  · exact point117slice2
  · exact point117slice3
  · exact point117slice4
  · exact point117slice5
  · exact point117slice6
  · exact point117slice7
  · exact point117slice8
  · exact point117slice9
  · exact point117slice10
  · exact point117slice11
  · exact point117slice12
  · exact point117slice13
  · exact point117slice14
  · exact point117slice15
  · exact point117slice16
  · exact point117slice17
  · exact point117slice18
  · exact point117slice19
  · exact point117slice20
  · exact point117slice21
  · exact point117slice22
  · exact point117slice23
  · exact point117slice24
  · exact point117slice25
  · exact point117slice26
  · exact point117slice27
  · exact point117slice28
  · exact point117slice29
  · exact point117slice30
  · exact point117slice31
  · exact point117slice32
  · exact point117slice33
  · exact point117slice34
  · exact point117slice35
  · exact point117slice36
  · exact point117slice37
  · exact point117slice38
  · exact point117slice39
  · exact point117slice40
  · exact point117slice41
  · exact point117slice42
  · exact point117slice43
  · exact point117slice44
  · exact point117slice45
  · exact point117slice46
  · exact point117slice47
  · exact point117slice48
  · exact point117slice49
  · exact point117slice50
  · exact point117slice51
  · exact point117slice52
  · exact point117slice53
  · exact point117slice54
  · exact point117slice55
  · exact point117slice56
  · exact point117slice57
  · exact point117slice58
  · exact point117slice59
  · exact point117slice60
  · exact point117slice61
  · exact point117slice62
  · exact point117slice63
  · exact point117slice64
  · exact point117slice65
  · exact point117slice66
  · exact point117slice67
  · exact point117slice68
  · exact point117slice69
  · exact point117slice70
  · exact point117slice71
  · exact point117slice72
  · exact point117slice73
  · exact point117slice74
  · exact point117slice75
  · exact point117slice76
  · exact point117slice77
  · exact point117slice78
  · exact point117slice79
  · exact point117slice80
  · exact point117slice81
  · exact point117slice82
  · exact point117slice83
  · exact point117slice84
  · exact point117slice85
  · exact point117slice86
  · exact point117slice87
  · exact point117slice88
  · exact point117slice89
  · exact point117slice90
  · exact point117slice91
  · exact point117slice92
  · exact point117slice93
  · exact point117slice94
  · exact point117slice95
  · exact point117slice96
  · exact point117slice97
  · exact point117slice98
  · exact point117slice99
  · exact point117slice100
  · exact point117slice101
  · exact point117slice102
  · exact point117slice103
  · exact point117slice104
  · exact point117slice105
  · exact point117slice106
  · exact point117slice107
  · exact point117slice108
  · exact point117slice109
  · exact point117slice110
  · exact point117slice111
  · exact point117slice112
  · exact point117slice113
  · exact point117slice114
  · exact point117slice115
  · exact point117slice116
  · exact point117slice117
  · exact point117slice118
  · exact point117slice119
  · exact point117slice120
  · exact point117slice121
  · exact point117slice122
  · exact point117slice123
  · exact point117slice124
  · exact point117slice125
  · exact point117slice126
  · exact point117slice127
  · exact point117slice128
  · exact point117slice129
  · exact point117slice130
  · exact point117slice131
  · exact point117slice132
  · exact point117slice133
  · exact point117slice134
  · exact point117slice135
  · exact point117slice136
  · exact point117slice137
  · exact point117slice138
  · exact point117slice139
  · exact point117slice140
  · exact point117slice141
  · exact point117slice142
  · exact point117slice143
  · exact point117slice144
  · exact point117slice145
  · exact point117slice146
  · exact point117slice147
  · exact point117slice148
  · exact point117slice149
  · exact point117slice150
  · exact point117slice151
  · exact point117slice152
  · exact point117slice153
  · exact point117slice154
  · exact point117slice155
  · exact point117slice156
  · exact point117slice157
  · exact point117slice158
  · exact point117slice159
  · exact point117slice160
  · exact point117slice161
  · exact point117slice162
  · exact point117slice163
  · exact point117slice164
  · exact point117slice165
  · exact point117slice166
  · exact point117slice167
  · exact point117slice168
  · exact point117slice169
  · exact point117slice170
  · exact point117slice171
  · exact point117slice172
  · exact point117slice173
  · exact point117slice174
  · exact point117slice175
  · exact point117slice176
  · exact point117slice177
  · exact point117slice178
  · exact point117slice179
  · exact point117slice180
  · exact point117slice181
  · exact point117slice182
  · exact point117slice183
  · exact point117slice184
  · exact point117slice185
  · exact point117slice186
  · exact point117slice187
  · exact point117slice188
  · exact point117slice189
  · exact point117slice190
  · exact point117slice191
  · exact point117slice192
  · exact point117slice193
  · exact point117slice194
  · exact point117slice195
  · exact point117slice196
  · exact point117slice197
  · exact point117slice198
  · exact point117slice199
  · exact point117slice200
  · exact point117slice201
  · exact point117slice202

set_option maxHeartbeats 1600000 in
public theorem point117 : stepCheck 0 2571 := by
  have hleft : L0Gen 0 * L0Rep 2571 = leftPerm117 := by
    change L0Gen 0 * evalWord L0Gen [3, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1] = leftPerm117
    simp only [leftPerm117, p840, p167, p59, p48, p30, p20, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2571) * evalWord L1Gen (L0Factor 0 2571) = rightPerm117 := by
    change evalWord L0Gen [1, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] * evalWord L1Gen [1, 0, 3, 0, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3] = rightPerm117
    simp only [rightPerm117, p849, p204, p134, p119, p82, p77, p74, p66, p65, p64, p63, p61, p60, p58, p55, p40, p38, p34, p33, p32, p31, p30, p29, p28, p27, p26, p25, p24, p23, p22, p21, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2571) x =
    (L0Rep (L0Act 0 2571) * evalWord L1Gen (L0Factor 0 2571)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap117_eq, ← rightMap117_eq]
  exact Residual1Cache.ofSlices point117_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
