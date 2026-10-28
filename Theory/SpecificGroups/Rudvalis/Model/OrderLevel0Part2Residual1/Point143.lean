module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 143

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap143 (x : Nat) : Nat := force t17 (force t54 (t53 x))
private def leftPerm143 : Equiv.Perm (Fin 4060) := p17 * (p54 * (p53))
private theorem leftMap143_eq (x : Fin 4060) :
    leftMap143 x.val = (leftPerm143 x).val := (compose (t := fun x => force t17 (force t54 (t53 x))) (a := t17) (b := fun x => force t54 (t53 x)) (fun _ => rfl) c17 (compose (t := fun x => force t54 (t53 x)) (a := t54) (b := fun x => t53 x) (fun _ => rfl) c54 c53)) x

private def rightMap143 (x : Nat) : Nat := force t166 (force t125 (force t193 (force t16 (force t10 (force t57 (force t89 (t94 x)))))))
private def rightPerm143 : Equiv.Perm (Fin 4060) := p166 * (p125 * (p193 * (p16 * (p10 * (p57 * (p89 * (p94)))))))
private theorem rightMap143_eq (x : Fin 4060) :
    rightMap143 x.val = (rightPerm143 x).val := (compose (t := fun x => force t166 (force t125 (force t193 (force t16 (force t10 (force t57 (force t89 (t94 x)))))))) (a := t166) (b := fun x => force t125 (force t193 (force t16 (force t10 (force t57 (force t89 (t94 x))))))) (fun _ => rfl) c166 (compose (t := fun x => force t125 (force t193 (force t16 (force t10 (force t57 (force t89 (t94 x))))))) (a := t125) (b := fun x => force t193 (force t16 (force t10 (force t57 (force t89 (t94 x)))))) (fun _ => rfl) c125 (compose (t := fun x => force t193 (force t16 (force t10 (force t57 (force t89 (t94 x)))))) (a := t193) (b := fun x => force t16 (force t10 (force t57 (force t89 (t94 x))))) (fun _ => rfl) c193 (compose (t := fun x => force t16 (force t10 (force t57 (force t89 (t94 x))))) (a := t16) (b := fun x => force t10 (force t57 (force t89 (t94 x)))) (fun _ => rfl) c16 (compose (t := fun x => force t10 (force t57 (force t89 (t94 x)))) (a := t10) (b := fun x => force t57 (force t89 (t94 x))) (fun _ => rfl) c10 (compose (t := fun x => force t57 (force t89 (t94 x))) (a := t57) (b := fun x => force t89 (t94 x)) (fun _ => rfl) c57 (compose (t := fun x => force t89 (t94 x)) (a := t89) (b := fun x => t94 x) (fun _ => rfl) c89 c94))))))) x

set_option maxHeartbeats 1600000 in
private theorem point143slice0 : Residual1Cache.slice leftMap143 rightMap143 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice1 : Residual1Cache.slice leftMap143 rightMap143 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice2 : Residual1Cache.slice leftMap143 rightMap143 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice3 : Residual1Cache.slice leftMap143 rightMap143 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice4 : Residual1Cache.slice leftMap143 rightMap143 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice5 : Residual1Cache.slice leftMap143 rightMap143 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice6 : Residual1Cache.slice leftMap143 rightMap143 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice7 : Residual1Cache.slice leftMap143 rightMap143 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice8 : Residual1Cache.slice leftMap143 rightMap143 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice9 : Residual1Cache.slice leftMap143 rightMap143 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice10 : Residual1Cache.slice leftMap143 rightMap143 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice11 : Residual1Cache.slice leftMap143 rightMap143 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice12 : Residual1Cache.slice leftMap143 rightMap143 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice13 : Residual1Cache.slice leftMap143 rightMap143 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice14 : Residual1Cache.slice leftMap143 rightMap143 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice15 : Residual1Cache.slice leftMap143 rightMap143 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice16 : Residual1Cache.slice leftMap143 rightMap143 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice17 : Residual1Cache.slice leftMap143 rightMap143 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice18 : Residual1Cache.slice leftMap143 rightMap143 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice19 : Residual1Cache.slice leftMap143 rightMap143 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice20 : Residual1Cache.slice leftMap143 rightMap143 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice21 : Residual1Cache.slice leftMap143 rightMap143 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice22 : Residual1Cache.slice leftMap143 rightMap143 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice23 : Residual1Cache.slice leftMap143 rightMap143 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice24 : Residual1Cache.slice leftMap143 rightMap143 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice25 : Residual1Cache.slice leftMap143 rightMap143 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice26 : Residual1Cache.slice leftMap143 rightMap143 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice27 : Residual1Cache.slice leftMap143 rightMap143 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice28 : Residual1Cache.slice leftMap143 rightMap143 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice29 : Residual1Cache.slice leftMap143 rightMap143 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice30 : Residual1Cache.slice leftMap143 rightMap143 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice31 : Residual1Cache.slice leftMap143 rightMap143 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice32 : Residual1Cache.slice leftMap143 rightMap143 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice33 : Residual1Cache.slice leftMap143 rightMap143 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice34 : Residual1Cache.slice leftMap143 rightMap143 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice35 : Residual1Cache.slice leftMap143 rightMap143 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice36 : Residual1Cache.slice leftMap143 rightMap143 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice37 : Residual1Cache.slice leftMap143 rightMap143 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice38 : Residual1Cache.slice leftMap143 rightMap143 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice39 : Residual1Cache.slice leftMap143 rightMap143 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice40 : Residual1Cache.slice leftMap143 rightMap143 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice41 : Residual1Cache.slice leftMap143 rightMap143 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice42 : Residual1Cache.slice leftMap143 rightMap143 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice43 : Residual1Cache.slice leftMap143 rightMap143 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice44 : Residual1Cache.slice leftMap143 rightMap143 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice45 : Residual1Cache.slice leftMap143 rightMap143 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice46 : Residual1Cache.slice leftMap143 rightMap143 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice47 : Residual1Cache.slice leftMap143 rightMap143 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice48 : Residual1Cache.slice leftMap143 rightMap143 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice49 : Residual1Cache.slice leftMap143 rightMap143 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice50 : Residual1Cache.slice leftMap143 rightMap143 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice51 : Residual1Cache.slice leftMap143 rightMap143 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice52 : Residual1Cache.slice leftMap143 rightMap143 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice53 : Residual1Cache.slice leftMap143 rightMap143 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice54 : Residual1Cache.slice leftMap143 rightMap143 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice55 : Residual1Cache.slice leftMap143 rightMap143 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice56 : Residual1Cache.slice leftMap143 rightMap143 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice57 : Residual1Cache.slice leftMap143 rightMap143 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice58 : Residual1Cache.slice leftMap143 rightMap143 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice59 : Residual1Cache.slice leftMap143 rightMap143 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice60 : Residual1Cache.slice leftMap143 rightMap143 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice61 : Residual1Cache.slice leftMap143 rightMap143 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice62 : Residual1Cache.slice leftMap143 rightMap143 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice63 : Residual1Cache.slice leftMap143 rightMap143 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice64 : Residual1Cache.slice leftMap143 rightMap143 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice65 : Residual1Cache.slice leftMap143 rightMap143 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice66 : Residual1Cache.slice leftMap143 rightMap143 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice67 : Residual1Cache.slice leftMap143 rightMap143 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice68 : Residual1Cache.slice leftMap143 rightMap143 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice69 : Residual1Cache.slice leftMap143 rightMap143 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice70 : Residual1Cache.slice leftMap143 rightMap143 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice71 : Residual1Cache.slice leftMap143 rightMap143 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice72 : Residual1Cache.slice leftMap143 rightMap143 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice73 : Residual1Cache.slice leftMap143 rightMap143 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice74 : Residual1Cache.slice leftMap143 rightMap143 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice75 : Residual1Cache.slice leftMap143 rightMap143 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice76 : Residual1Cache.slice leftMap143 rightMap143 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice77 : Residual1Cache.slice leftMap143 rightMap143 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice78 : Residual1Cache.slice leftMap143 rightMap143 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice79 : Residual1Cache.slice leftMap143 rightMap143 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice80 : Residual1Cache.slice leftMap143 rightMap143 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice81 : Residual1Cache.slice leftMap143 rightMap143 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice82 : Residual1Cache.slice leftMap143 rightMap143 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice83 : Residual1Cache.slice leftMap143 rightMap143 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice84 : Residual1Cache.slice leftMap143 rightMap143 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice85 : Residual1Cache.slice leftMap143 rightMap143 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice86 : Residual1Cache.slice leftMap143 rightMap143 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice87 : Residual1Cache.slice leftMap143 rightMap143 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice88 : Residual1Cache.slice leftMap143 rightMap143 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice89 : Residual1Cache.slice leftMap143 rightMap143 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice90 : Residual1Cache.slice leftMap143 rightMap143 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice91 : Residual1Cache.slice leftMap143 rightMap143 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice92 : Residual1Cache.slice leftMap143 rightMap143 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice93 : Residual1Cache.slice leftMap143 rightMap143 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice94 : Residual1Cache.slice leftMap143 rightMap143 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice95 : Residual1Cache.slice leftMap143 rightMap143 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice96 : Residual1Cache.slice leftMap143 rightMap143 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice97 : Residual1Cache.slice leftMap143 rightMap143 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice98 : Residual1Cache.slice leftMap143 rightMap143 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice99 : Residual1Cache.slice leftMap143 rightMap143 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice100 : Residual1Cache.slice leftMap143 rightMap143 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice101 : Residual1Cache.slice leftMap143 rightMap143 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice102 : Residual1Cache.slice leftMap143 rightMap143 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice103 : Residual1Cache.slice leftMap143 rightMap143 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice104 : Residual1Cache.slice leftMap143 rightMap143 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice105 : Residual1Cache.slice leftMap143 rightMap143 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice106 : Residual1Cache.slice leftMap143 rightMap143 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice107 : Residual1Cache.slice leftMap143 rightMap143 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice108 : Residual1Cache.slice leftMap143 rightMap143 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice109 : Residual1Cache.slice leftMap143 rightMap143 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice110 : Residual1Cache.slice leftMap143 rightMap143 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice111 : Residual1Cache.slice leftMap143 rightMap143 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice112 : Residual1Cache.slice leftMap143 rightMap143 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice113 : Residual1Cache.slice leftMap143 rightMap143 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice114 : Residual1Cache.slice leftMap143 rightMap143 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice115 : Residual1Cache.slice leftMap143 rightMap143 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice116 : Residual1Cache.slice leftMap143 rightMap143 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice117 : Residual1Cache.slice leftMap143 rightMap143 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice118 : Residual1Cache.slice leftMap143 rightMap143 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice119 : Residual1Cache.slice leftMap143 rightMap143 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice120 : Residual1Cache.slice leftMap143 rightMap143 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice121 : Residual1Cache.slice leftMap143 rightMap143 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice122 : Residual1Cache.slice leftMap143 rightMap143 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice123 : Residual1Cache.slice leftMap143 rightMap143 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice124 : Residual1Cache.slice leftMap143 rightMap143 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice125 : Residual1Cache.slice leftMap143 rightMap143 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice126 : Residual1Cache.slice leftMap143 rightMap143 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice127 : Residual1Cache.slice leftMap143 rightMap143 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice128 : Residual1Cache.slice leftMap143 rightMap143 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice129 : Residual1Cache.slice leftMap143 rightMap143 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice130 : Residual1Cache.slice leftMap143 rightMap143 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice131 : Residual1Cache.slice leftMap143 rightMap143 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice132 : Residual1Cache.slice leftMap143 rightMap143 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice133 : Residual1Cache.slice leftMap143 rightMap143 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice134 : Residual1Cache.slice leftMap143 rightMap143 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice135 : Residual1Cache.slice leftMap143 rightMap143 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice136 : Residual1Cache.slice leftMap143 rightMap143 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice137 : Residual1Cache.slice leftMap143 rightMap143 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice138 : Residual1Cache.slice leftMap143 rightMap143 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice139 : Residual1Cache.slice leftMap143 rightMap143 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice140 : Residual1Cache.slice leftMap143 rightMap143 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice141 : Residual1Cache.slice leftMap143 rightMap143 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice142 : Residual1Cache.slice leftMap143 rightMap143 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice143 : Residual1Cache.slice leftMap143 rightMap143 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice144 : Residual1Cache.slice leftMap143 rightMap143 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice145 : Residual1Cache.slice leftMap143 rightMap143 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice146 : Residual1Cache.slice leftMap143 rightMap143 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice147 : Residual1Cache.slice leftMap143 rightMap143 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice148 : Residual1Cache.slice leftMap143 rightMap143 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice149 : Residual1Cache.slice leftMap143 rightMap143 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice150 : Residual1Cache.slice leftMap143 rightMap143 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice151 : Residual1Cache.slice leftMap143 rightMap143 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice152 : Residual1Cache.slice leftMap143 rightMap143 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice153 : Residual1Cache.slice leftMap143 rightMap143 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice154 : Residual1Cache.slice leftMap143 rightMap143 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice155 : Residual1Cache.slice leftMap143 rightMap143 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice156 : Residual1Cache.slice leftMap143 rightMap143 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice157 : Residual1Cache.slice leftMap143 rightMap143 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice158 : Residual1Cache.slice leftMap143 rightMap143 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice159 : Residual1Cache.slice leftMap143 rightMap143 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice160 : Residual1Cache.slice leftMap143 rightMap143 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice161 : Residual1Cache.slice leftMap143 rightMap143 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice162 : Residual1Cache.slice leftMap143 rightMap143 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice163 : Residual1Cache.slice leftMap143 rightMap143 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice164 : Residual1Cache.slice leftMap143 rightMap143 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice165 : Residual1Cache.slice leftMap143 rightMap143 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice166 : Residual1Cache.slice leftMap143 rightMap143 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice167 : Residual1Cache.slice leftMap143 rightMap143 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice168 : Residual1Cache.slice leftMap143 rightMap143 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice169 : Residual1Cache.slice leftMap143 rightMap143 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice170 : Residual1Cache.slice leftMap143 rightMap143 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice171 : Residual1Cache.slice leftMap143 rightMap143 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice172 : Residual1Cache.slice leftMap143 rightMap143 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice173 : Residual1Cache.slice leftMap143 rightMap143 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice174 : Residual1Cache.slice leftMap143 rightMap143 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice175 : Residual1Cache.slice leftMap143 rightMap143 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice176 : Residual1Cache.slice leftMap143 rightMap143 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice177 : Residual1Cache.slice leftMap143 rightMap143 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice178 : Residual1Cache.slice leftMap143 rightMap143 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice179 : Residual1Cache.slice leftMap143 rightMap143 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice180 : Residual1Cache.slice leftMap143 rightMap143 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice181 : Residual1Cache.slice leftMap143 rightMap143 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice182 : Residual1Cache.slice leftMap143 rightMap143 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice183 : Residual1Cache.slice leftMap143 rightMap143 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice184 : Residual1Cache.slice leftMap143 rightMap143 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice185 : Residual1Cache.slice leftMap143 rightMap143 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice186 : Residual1Cache.slice leftMap143 rightMap143 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice187 : Residual1Cache.slice leftMap143 rightMap143 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice188 : Residual1Cache.slice leftMap143 rightMap143 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice189 : Residual1Cache.slice leftMap143 rightMap143 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice190 : Residual1Cache.slice leftMap143 rightMap143 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice191 : Residual1Cache.slice leftMap143 rightMap143 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice192 : Residual1Cache.slice leftMap143 rightMap143 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice193 : Residual1Cache.slice leftMap143 rightMap143 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice194 : Residual1Cache.slice leftMap143 rightMap143 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice195 : Residual1Cache.slice leftMap143 rightMap143 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice196 : Residual1Cache.slice leftMap143 rightMap143 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice197 : Residual1Cache.slice leftMap143 rightMap143 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice198 : Residual1Cache.slice leftMap143 rightMap143 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice199 : Residual1Cache.slice leftMap143 rightMap143 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice200 : Residual1Cache.slice leftMap143 rightMap143 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice201 : Residual1Cache.slice leftMap143 rightMap143 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point143slice202 : Residual1Cache.slice leftMap143 rightMap143 202 = true := by
  decide +kernel

private theorem point143_slices : ∀ c, Residual1Cache.slice leftMap143 rightMap143 c = true := by
  intro c
  fin_cases c
  · exact point143slice0
  · exact point143slice1
  · exact point143slice2
  · exact point143slice3
  · exact point143slice4
  · exact point143slice5
  · exact point143slice6
  · exact point143slice7
  · exact point143slice8
  · exact point143slice9
  · exact point143slice10
  · exact point143slice11
  · exact point143slice12
  · exact point143slice13
  · exact point143slice14
  · exact point143slice15
  · exact point143slice16
  · exact point143slice17
  · exact point143slice18
  · exact point143slice19
  · exact point143slice20
  · exact point143slice21
  · exact point143slice22
  · exact point143slice23
  · exact point143slice24
  · exact point143slice25
  · exact point143slice26
  · exact point143slice27
  · exact point143slice28
  · exact point143slice29
  · exact point143slice30
  · exact point143slice31
  · exact point143slice32
  · exact point143slice33
  · exact point143slice34
  · exact point143slice35
  · exact point143slice36
  · exact point143slice37
  · exact point143slice38
  · exact point143slice39
  · exact point143slice40
  · exact point143slice41
  · exact point143slice42
  · exact point143slice43
  · exact point143slice44
  · exact point143slice45
  · exact point143slice46
  · exact point143slice47
  · exact point143slice48
  · exact point143slice49
  · exact point143slice50
  · exact point143slice51
  · exact point143slice52
  · exact point143slice53
  · exact point143slice54
  · exact point143slice55
  · exact point143slice56
  · exact point143slice57
  · exact point143slice58
  · exact point143slice59
  · exact point143slice60
  · exact point143slice61
  · exact point143slice62
  · exact point143slice63
  · exact point143slice64
  · exact point143slice65
  · exact point143slice66
  · exact point143slice67
  · exact point143slice68
  · exact point143slice69
  · exact point143slice70
  · exact point143slice71
  · exact point143slice72
  · exact point143slice73
  · exact point143slice74
  · exact point143slice75
  · exact point143slice76
  · exact point143slice77
  · exact point143slice78
  · exact point143slice79
  · exact point143slice80
  · exact point143slice81
  · exact point143slice82
  · exact point143slice83
  · exact point143slice84
  · exact point143slice85
  · exact point143slice86
  · exact point143slice87
  · exact point143slice88
  · exact point143slice89
  · exact point143slice90
  · exact point143slice91
  · exact point143slice92
  · exact point143slice93
  · exact point143slice94
  · exact point143slice95
  · exact point143slice96
  · exact point143slice97
  · exact point143slice98
  · exact point143slice99
  · exact point143slice100
  · exact point143slice101
  · exact point143slice102
  · exact point143slice103
  · exact point143slice104
  · exact point143slice105
  · exact point143slice106
  · exact point143slice107
  · exact point143slice108
  · exact point143slice109
  · exact point143slice110
  · exact point143slice111
  · exact point143slice112
  · exact point143slice113
  · exact point143slice114
  · exact point143slice115
  · exact point143slice116
  · exact point143slice117
  · exact point143slice118
  · exact point143slice119
  · exact point143slice120
  · exact point143slice121
  · exact point143slice122
  · exact point143slice123
  · exact point143slice124
  · exact point143slice125
  · exact point143slice126
  · exact point143slice127
  · exact point143slice128
  · exact point143slice129
  · exact point143slice130
  · exact point143slice131
  · exact point143slice132
  · exact point143slice133
  · exact point143slice134
  · exact point143slice135
  · exact point143slice136
  · exact point143slice137
  · exact point143slice138
  · exact point143slice139
  · exact point143slice140
  · exact point143slice141
  · exact point143slice142
  · exact point143slice143
  · exact point143slice144
  · exact point143slice145
  · exact point143slice146
  · exact point143slice147
  · exact point143slice148
  · exact point143slice149
  · exact point143slice150
  · exact point143slice151
  · exact point143slice152
  · exact point143slice153
  · exact point143slice154
  · exact point143slice155
  · exact point143slice156
  · exact point143slice157
  · exact point143slice158
  · exact point143slice159
  · exact point143slice160
  · exact point143slice161
  · exact point143slice162
  · exact point143slice163
  · exact point143slice164
  · exact point143slice165
  · exact point143slice166
  · exact point143slice167
  · exact point143slice168
  · exact point143slice169
  · exact point143slice170
  · exact point143slice171
  · exact point143slice172
  · exact point143slice173
  · exact point143slice174
  · exact point143slice175
  · exact point143slice176
  · exact point143slice177
  · exact point143slice178
  · exact point143slice179
  · exact point143slice180
  · exact point143slice181
  · exact point143slice182
  · exact point143slice183
  · exact point143slice184
  · exact point143slice185
  · exact point143slice186
  · exact point143slice187
  · exact point143slice188
  · exact point143slice189
  · exact point143slice190
  · exact point143slice191
  · exact point143slice192
  · exact point143slice193
  · exact point143slice194
  · exact point143slice195
  · exact point143slice196
  · exact point143slice197
  · exact point143slice198
  · exact point143slice199
  · exact point143slice200
  · exact point143slice201
  · exact point143slice202

set_option maxHeartbeats 1600000 in
public theorem point143 : stepCheck 1 2844 := by
  have hleft : L0Gen 1 * L0Rep 2844 = leftPerm143 := by
    change L0Gen 1 * evalWord L0Gen [0, 1, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0] = leftPerm143
    simp only [leftPerm143, p54, p53, p30, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2844) * evalWord L1Gen (L0Factor 1 2844) = rightPerm143 := by
    change evalWord L0Gen [0, 1, 1, 0, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] * evalWord L1Gen [0, 3, 2, 3, 0, 1, 0, 3, 2, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1] = rightPerm143
    simp only [rightPerm143, p193, p166, p125, p94, p89, p57, p54, p52, p33, p30, p29, p28, p24, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2844) x =
    (L0Rep (L0Act 1 2844) * evalWord L1Gen (L0Factor 1 2844)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap143_eq, ← rightMap143_eq]
  exact Residual1Cache.ofSlices point143_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
