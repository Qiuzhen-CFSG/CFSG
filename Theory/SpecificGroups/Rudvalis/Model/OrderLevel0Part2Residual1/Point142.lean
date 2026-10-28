module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level15Part1
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 142

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap142 (x : Nat) : Nat := force t85 (force t740 (t85 x))
private def leftPerm142 : Equiv.Perm (Fin 4060) := p85 * (p740 * (p85))
private theorem leftMap142_eq (x : Fin 4060) :
    leftMap142 x.val = (leftPerm142 x).val := (compose (t := fun x => force t85 (force t740 (t85 x))) (a := t85) (b := fun x => force t740 (t85 x)) (fun _ => rfl) c85 (compose (t := fun x => force t740 (t85 x)) (a := t740) (b := fun x => t85 x) (fun _ => rfl) c740 c85)) x

private def rightMap142 (x : Nat) : Nat := force t256 (force t1030 (force t4 (force t9 (force t773 (force t893 (force t21 (force t61 (t511 x))))))))
private def rightPerm142 : Equiv.Perm (Fin 4060) := p256 * (p1030 * (p4 * (p9 * (p773 * (p893 * (p21 * (p61 * (p511))))))))
private theorem rightMap142_eq (x : Fin 4060) :
    rightMap142 x.val = (rightPerm142 x).val := (compose (t := fun x => force t256 (force t1030 (force t4 (force t9 (force t773 (force t893 (force t21 (force t61 (t511 x))))))))) (a := t256) (b := fun x => force t1030 (force t4 (force t9 (force t773 (force t893 (force t21 (force t61 (t511 x)))))))) (fun _ => rfl) c256 (compose (t := fun x => force t1030 (force t4 (force t9 (force t773 (force t893 (force t21 (force t61 (t511 x)))))))) (a := t1030) (b := fun x => force t4 (force t9 (force t773 (force t893 (force t21 (force t61 (t511 x))))))) (fun _ => rfl) c1030 (compose (t := fun x => force t4 (force t9 (force t773 (force t893 (force t21 (force t61 (t511 x))))))) (a := t4) (b := fun x => force t9 (force t773 (force t893 (force t21 (force t61 (t511 x)))))) (fun _ => rfl) c4 (compose (t := fun x => force t9 (force t773 (force t893 (force t21 (force t61 (t511 x)))))) (a := t9) (b := fun x => force t773 (force t893 (force t21 (force t61 (t511 x))))) (fun _ => rfl) c9 (compose (t := fun x => force t773 (force t893 (force t21 (force t61 (t511 x))))) (a := t773) (b := fun x => force t893 (force t21 (force t61 (t511 x)))) (fun _ => rfl) c773 (compose (t := fun x => force t893 (force t21 (force t61 (t511 x)))) (a := t893) (b := fun x => force t21 (force t61 (t511 x))) (fun _ => rfl) c893 (compose (t := fun x => force t21 (force t61 (t511 x))) (a := t21) (b := fun x => force t61 (t511 x)) (fun _ => rfl) c21 (compose (t := fun x => force t61 (t511 x)) (a := t61) (b := fun x => t511 x) (fun _ => rfl) c61 c511)))))))) x

set_option maxHeartbeats 1600000 in
private theorem point142slice0 : Residual1Cache.slice leftMap142 rightMap142 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice1 : Residual1Cache.slice leftMap142 rightMap142 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice2 : Residual1Cache.slice leftMap142 rightMap142 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice3 : Residual1Cache.slice leftMap142 rightMap142 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice4 : Residual1Cache.slice leftMap142 rightMap142 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice5 : Residual1Cache.slice leftMap142 rightMap142 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice6 : Residual1Cache.slice leftMap142 rightMap142 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice7 : Residual1Cache.slice leftMap142 rightMap142 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice8 : Residual1Cache.slice leftMap142 rightMap142 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice9 : Residual1Cache.slice leftMap142 rightMap142 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice10 : Residual1Cache.slice leftMap142 rightMap142 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice11 : Residual1Cache.slice leftMap142 rightMap142 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice12 : Residual1Cache.slice leftMap142 rightMap142 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice13 : Residual1Cache.slice leftMap142 rightMap142 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice14 : Residual1Cache.slice leftMap142 rightMap142 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice15 : Residual1Cache.slice leftMap142 rightMap142 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice16 : Residual1Cache.slice leftMap142 rightMap142 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice17 : Residual1Cache.slice leftMap142 rightMap142 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice18 : Residual1Cache.slice leftMap142 rightMap142 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice19 : Residual1Cache.slice leftMap142 rightMap142 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice20 : Residual1Cache.slice leftMap142 rightMap142 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice21 : Residual1Cache.slice leftMap142 rightMap142 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice22 : Residual1Cache.slice leftMap142 rightMap142 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice23 : Residual1Cache.slice leftMap142 rightMap142 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice24 : Residual1Cache.slice leftMap142 rightMap142 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice25 : Residual1Cache.slice leftMap142 rightMap142 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice26 : Residual1Cache.slice leftMap142 rightMap142 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice27 : Residual1Cache.slice leftMap142 rightMap142 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice28 : Residual1Cache.slice leftMap142 rightMap142 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice29 : Residual1Cache.slice leftMap142 rightMap142 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice30 : Residual1Cache.slice leftMap142 rightMap142 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice31 : Residual1Cache.slice leftMap142 rightMap142 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice32 : Residual1Cache.slice leftMap142 rightMap142 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice33 : Residual1Cache.slice leftMap142 rightMap142 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice34 : Residual1Cache.slice leftMap142 rightMap142 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice35 : Residual1Cache.slice leftMap142 rightMap142 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice36 : Residual1Cache.slice leftMap142 rightMap142 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice37 : Residual1Cache.slice leftMap142 rightMap142 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice38 : Residual1Cache.slice leftMap142 rightMap142 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice39 : Residual1Cache.slice leftMap142 rightMap142 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice40 : Residual1Cache.slice leftMap142 rightMap142 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice41 : Residual1Cache.slice leftMap142 rightMap142 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice42 : Residual1Cache.slice leftMap142 rightMap142 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice43 : Residual1Cache.slice leftMap142 rightMap142 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice44 : Residual1Cache.slice leftMap142 rightMap142 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice45 : Residual1Cache.slice leftMap142 rightMap142 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice46 : Residual1Cache.slice leftMap142 rightMap142 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice47 : Residual1Cache.slice leftMap142 rightMap142 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice48 : Residual1Cache.slice leftMap142 rightMap142 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice49 : Residual1Cache.slice leftMap142 rightMap142 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice50 : Residual1Cache.slice leftMap142 rightMap142 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice51 : Residual1Cache.slice leftMap142 rightMap142 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice52 : Residual1Cache.slice leftMap142 rightMap142 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice53 : Residual1Cache.slice leftMap142 rightMap142 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice54 : Residual1Cache.slice leftMap142 rightMap142 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice55 : Residual1Cache.slice leftMap142 rightMap142 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice56 : Residual1Cache.slice leftMap142 rightMap142 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice57 : Residual1Cache.slice leftMap142 rightMap142 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice58 : Residual1Cache.slice leftMap142 rightMap142 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice59 : Residual1Cache.slice leftMap142 rightMap142 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice60 : Residual1Cache.slice leftMap142 rightMap142 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice61 : Residual1Cache.slice leftMap142 rightMap142 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice62 : Residual1Cache.slice leftMap142 rightMap142 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice63 : Residual1Cache.slice leftMap142 rightMap142 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice64 : Residual1Cache.slice leftMap142 rightMap142 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice65 : Residual1Cache.slice leftMap142 rightMap142 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice66 : Residual1Cache.slice leftMap142 rightMap142 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice67 : Residual1Cache.slice leftMap142 rightMap142 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice68 : Residual1Cache.slice leftMap142 rightMap142 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice69 : Residual1Cache.slice leftMap142 rightMap142 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice70 : Residual1Cache.slice leftMap142 rightMap142 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice71 : Residual1Cache.slice leftMap142 rightMap142 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice72 : Residual1Cache.slice leftMap142 rightMap142 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice73 : Residual1Cache.slice leftMap142 rightMap142 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice74 : Residual1Cache.slice leftMap142 rightMap142 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice75 : Residual1Cache.slice leftMap142 rightMap142 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice76 : Residual1Cache.slice leftMap142 rightMap142 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice77 : Residual1Cache.slice leftMap142 rightMap142 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice78 : Residual1Cache.slice leftMap142 rightMap142 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice79 : Residual1Cache.slice leftMap142 rightMap142 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice80 : Residual1Cache.slice leftMap142 rightMap142 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice81 : Residual1Cache.slice leftMap142 rightMap142 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice82 : Residual1Cache.slice leftMap142 rightMap142 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice83 : Residual1Cache.slice leftMap142 rightMap142 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice84 : Residual1Cache.slice leftMap142 rightMap142 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice85 : Residual1Cache.slice leftMap142 rightMap142 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice86 : Residual1Cache.slice leftMap142 rightMap142 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice87 : Residual1Cache.slice leftMap142 rightMap142 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice88 : Residual1Cache.slice leftMap142 rightMap142 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice89 : Residual1Cache.slice leftMap142 rightMap142 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice90 : Residual1Cache.slice leftMap142 rightMap142 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice91 : Residual1Cache.slice leftMap142 rightMap142 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice92 : Residual1Cache.slice leftMap142 rightMap142 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice93 : Residual1Cache.slice leftMap142 rightMap142 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice94 : Residual1Cache.slice leftMap142 rightMap142 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice95 : Residual1Cache.slice leftMap142 rightMap142 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice96 : Residual1Cache.slice leftMap142 rightMap142 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice97 : Residual1Cache.slice leftMap142 rightMap142 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice98 : Residual1Cache.slice leftMap142 rightMap142 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice99 : Residual1Cache.slice leftMap142 rightMap142 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice100 : Residual1Cache.slice leftMap142 rightMap142 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice101 : Residual1Cache.slice leftMap142 rightMap142 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice102 : Residual1Cache.slice leftMap142 rightMap142 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice103 : Residual1Cache.slice leftMap142 rightMap142 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice104 : Residual1Cache.slice leftMap142 rightMap142 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice105 : Residual1Cache.slice leftMap142 rightMap142 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice106 : Residual1Cache.slice leftMap142 rightMap142 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice107 : Residual1Cache.slice leftMap142 rightMap142 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice108 : Residual1Cache.slice leftMap142 rightMap142 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice109 : Residual1Cache.slice leftMap142 rightMap142 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice110 : Residual1Cache.slice leftMap142 rightMap142 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice111 : Residual1Cache.slice leftMap142 rightMap142 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice112 : Residual1Cache.slice leftMap142 rightMap142 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice113 : Residual1Cache.slice leftMap142 rightMap142 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice114 : Residual1Cache.slice leftMap142 rightMap142 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice115 : Residual1Cache.slice leftMap142 rightMap142 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice116 : Residual1Cache.slice leftMap142 rightMap142 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice117 : Residual1Cache.slice leftMap142 rightMap142 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice118 : Residual1Cache.slice leftMap142 rightMap142 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice119 : Residual1Cache.slice leftMap142 rightMap142 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice120 : Residual1Cache.slice leftMap142 rightMap142 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice121 : Residual1Cache.slice leftMap142 rightMap142 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice122 : Residual1Cache.slice leftMap142 rightMap142 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice123 : Residual1Cache.slice leftMap142 rightMap142 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice124 : Residual1Cache.slice leftMap142 rightMap142 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice125 : Residual1Cache.slice leftMap142 rightMap142 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice126 : Residual1Cache.slice leftMap142 rightMap142 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice127 : Residual1Cache.slice leftMap142 rightMap142 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice128 : Residual1Cache.slice leftMap142 rightMap142 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice129 : Residual1Cache.slice leftMap142 rightMap142 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice130 : Residual1Cache.slice leftMap142 rightMap142 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice131 : Residual1Cache.slice leftMap142 rightMap142 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice132 : Residual1Cache.slice leftMap142 rightMap142 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice133 : Residual1Cache.slice leftMap142 rightMap142 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice134 : Residual1Cache.slice leftMap142 rightMap142 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice135 : Residual1Cache.slice leftMap142 rightMap142 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice136 : Residual1Cache.slice leftMap142 rightMap142 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice137 : Residual1Cache.slice leftMap142 rightMap142 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice138 : Residual1Cache.slice leftMap142 rightMap142 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice139 : Residual1Cache.slice leftMap142 rightMap142 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice140 : Residual1Cache.slice leftMap142 rightMap142 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice141 : Residual1Cache.slice leftMap142 rightMap142 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice142 : Residual1Cache.slice leftMap142 rightMap142 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice143 : Residual1Cache.slice leftMap142 rightMap142 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice144 : Residual1Cache.slice leftMap142 rightMap142 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice145 : Residual1Cache.slice leftMap142 rightMap142 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice146 : Residual1Cache.slice leftMap142 rightMap142 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice147 : Residual1Cache.slice leftMap142 rightMap142 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice148 : Residual1Cache.slice leftMap142 rightMap142 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice149 : Residual1Cache.slice leftMap142 rightMap142 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice150 : Residual1Cache.slice leftMap142 rightMap142 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice151 : Residual1Cache.slice leftMap142 rightMap142 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice152 : Residual1Cache.slice leftMap142 rightMap142 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice153 : Residual1Cache.slice leftMap142 rightMap142 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice154 : Residual1Cache.slice leftMap142 rightMap142 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice155 : Residual1Cache.slice leftMap142 rightMap142 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice156 : Residual1Cache.slice leftMap142 rightMap142 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice157 : Residual1Cache.slice leftMap142 rightMap142 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice158 : Residual1Cache.slice leftMap142 rightMap142 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice159 : Residual1Cache.slice leftMap142 rightMap142 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice160 : Residual1Cache.slice leftMap142 rightMap142 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice161 : Residual1Cache.slice leftMap142 rightMap142 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice162 : Residual1Cache.slice leftMap142 rightMap142 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice163 : Residual1Cache.slice leftMap142 rightMap142 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice164 : Residual1Cache.slice leftMap142 rightMap142 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice165 : Residual1Cache.slice leftMap142 rightMap142 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice166 : Residual1Cache.slice leftMap142 rightMap142 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice167 : Residual1Cache.slice leftMap142 rightMap142 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice168 : Residual1Cache.slice leftMap142 rightMap142 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice169 : Residual1Cache.slice leftMap142 rightMap142 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice170 : Residual1Cache.slice leftMap142 rightMap142 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice171 : Residual1Cache.slice leftMap142 rightMap142 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice172 : Residual1Cache.slice leftMap142 rightMap142 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice173 : Residual1Cache.slice leftMap142 rightMap142 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice174 : Residual1Cache.slice leftMap142 rightMap142 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice175 : Residual1Cache.slice leftMap142 rightMap142 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice176 : Residual1Cache.slice leftMap142 rightMap142 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice177 : Residual1Cache.slice leftMap142 rightMap142 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice178 : Residual1Cache.slice leftMap142 rightMap142 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice179 : Residual1Cache.slice leftMap142 rightMap142 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice180 : Residual1Cache.slice leftMap142 rightMap142 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice181 : Residual1Cache.slice leftMap142 rightMap142 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice182 : Residual1Cache.slice leftMap142 rightMap142 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice183 : Residual1Cache.slice leftMap142 rightMap142 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice184 : Residual1Cache.slice leftMap142 rightMap142 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice185 : Residual1Cache.slice leftMap142 rightMap142 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice186 : Residual1Cache.slice leftMap142 rightMap142 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice187 : Residual1Cache.slice leftMap142 rightMap142 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice188 : Residual1Cache.slice leftMap142 rightMap142 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice189 : Residual1Cache.slice leftMap142 rightMap142 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice190 : Residual1Cache.slice leftMap142 rightMap142 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice191 : Residual1Cache.slice leftMap142 rightMap142 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice192 : Residual1Cache.slice leftMap142 rightMap142 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice193 : Residual1Cache.slice leftMap142 rightMap142 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice194 : Residual1Cache.slice leftMap142 rightMap142 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice195 : Residual1Cache.slice leftMap142 rightMap142 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice196 : Residual1Cache.slice leftMap142 rightMap142 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice197 : Residual1Cache.slice leftMap142 rightMap142 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice198 : Residual1Cache.slice leftMap142 rightMap142 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice199 : Residual1Cache.slice leftMap142 rightMap142 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice200 : Residual1Cache.slice leftMap142 rightMap142 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice201 : Residual1Cache.slice leftMap142 rightMap142 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point142slice202 : Residual1Cache.slice leftMap142 rightMap142 202 = true := by
  decide +kernel

private theorem point142_slices : ∀ c, Residual1Cache.slice leftMap142 rightMap142 c = true := by
  intro c
  fin_cases c
  · exact point142slice0
  · exact point142slice1
  · exact point142slice2
  · exact point142slice3
  · exact point142slice4
  · exact point142slice5
  · exact point142slice6
  · exact point142slice7
  · exact point142slice8
  · exact point142slice9
  · exact point142slice10
  · exact point142slice11
  · exact point142slice12
  · exact point142slice13
  · exact point142slice14
  · exact point142slice15
  · exact point142slice16
  · exact point142slice17
  · exact point142slice18
  · exact point142slice19
  · exact point142slice20
  · exact point142slice21
  · exact point142slice22
  · exact point142slice23
  · exact point142slice24
  · exact point142slice25
  · exact point142slice26
  · exact point142slice27
  · exact point142slice28
  · exact point142slice29
  · exact point142slice30
  · exact point142slice31
  · exact point142slice32
  · exact point142slice33
  · exact point142slice34
  · exact point142slice35
  · exact point142slice36
  · exact point142slice37
  · exact point142slice38
  · exact point142slice39
  · exact point142slice40
  · exact point142slice41
  · exact point142slice42
  · exact point142slice43
  · exact point142slice44
  · exact point142slice45
  · exact point142slice46
  · exact point142slice47
  · exact point142slice48
  · exact point142slice49
  · exact point142slice50
  · exact point142slice51
  · exact point142slice52
  · exact point142slice53
  · exact point142slice54
  · exact point142slice55
  · exact point142slice56
  · exact point142slice57
  · exact point142slice58
  · exact point142slice59
  · exact point142slice60
  · exact point142slice61
  · exact point142slice62
  · exact point142slice63
  · exact point142slice64
  · exact point142slice65
  · exact point142slice66
  · exact point142slice67
  · exact point142slice68
  · exact point142slice69
  · exact point142slice70
  · exact point142slice71
  · exact point142slice72
  · exact point142slice73
  · exact point142slice74
  · exact point142slice75
  · exact point142slice76
  · exact point142slice77
  · exact point142slice78
  · exact point142slice79
  · exact point142slice80
  · exact point142slice81
  · exact point142slice82
  · exact point142slice83
  · exact point142slice84
  · exact point142slice85
  · exact point142slice86
  · exact point142slice87
  · exact point142slice88
  · exact point142slice89
  · exact point142slice90
  · exact point142slice91
  · exact point142slice92
  · exact point142slice93
  · exact point142slice94
  · exact point142slice95
  · exact point142slice96
  · exact point142slice97
  · exact point142slice98
  · exact point142slice99
  · exact point142slice100
  · exact point142slice101
  · exact point142slice102
  · exact point142slice103
  · exact point142slice104
  · exact point142slice105
  · exact point142slice106
  · exact point142slice107
  · exact point142slice108
  · exact point142slice109
  · exact point142slice110
  · exact point142slice111
  · exact point142slice112
  · exact point142slice113
  · exact point142slice114
  · exact point142slice115
  · exact point142slice116
  · exact point142slice117
  · exact point142slice118
  · exact point142slice119
  · exact point142slice120
  · exact point142slice121
  · exact point142slice122
  · exact point142slice123
  · exact point142slice124
  · exact point142slice125
  · exact point142slice126
  · exact point142slice127
  · exact point142slice128
  · exact point142slice129
  · exact point142slice130
  · exact point142slice131
  · exact point142slice132
  · exact point142slice133
  · exact point142slice134
  · exact point142slice135
  · exact point142slice136
  · exact point142slice137
  · exact point142slice138
  · exact point142slice139
  · exact point142slice140
  · exact point142slice141
  · exact point142slice142
  · exact point142slice143
  · exact point142slice144
  · exact point142slice145
  · exact point142slice146
  · exact point142slice147
  · exact point142slice148
  · exact point142slice149
  · exact point142slice150
  · exact point142slice151
  · exact point142slice152
  · exact point142slice153
  · exact point142slice154
  · exact point142slice155
  · exact point142slice156
  · exact point142slice157
  · exact point142slice158
  · exact point142slice159
  · exact point142slice160
  · exact point142slice161
  · exact point142slice162
  · exact point142slice163
  · exact point142slice164
  · exact point142slice165
  · exact point142slice166
  · exact point142slice167
  · exact point142slice168
  · exact point142slice169
  · exact point142slice170
  · exact point142slice171
  · exact point142slice172
  · exact point142slice173
  · exact point142slice174
  · exact point142slice175
  · exact point142slice176
  · exact point142slice177
  · exact point142slice178
  · exact point142slice179
  · exact point142slice180
  · exact point142slice181
  · exact point142slice182
  · exact point142slice183
  · exact point142slice184
  · exact point142slice185
  · exact point142slice186
  · exact point142slice187
  · exact point142slice188
  · exact point142slice189
  · exact point142slice190
  · exact point142slice191
  · exact point142slice192
  · exact point142slice193
  · exact point142slice194
  · exact point142slice195
  · exact point142slice196
  · exact point142slice197
  · exact point142slice198
  · exact point142slice199
  · exact point142slice200
  · exact point142slice201
  · exact point142slice202

set_option maxHeartbeats 1600000 in
public theorem point142 : stepCheck 0 2858 := by
  have hleft : L0Gen 0 * L0Rep 2858 = leftPerm142 := by
    change L0Gen 0 * evalWord L0Gen [1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0] = leftPerm142
    simp only [leftPerm142, p740, p239, p85, p47, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2858) * evalWord L1Gen (L0Factor 0 2858) = rightPerm142 := by
    change evalWord L0Gen [3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3] * evalWord L1Gen [1, 0, 0, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm142
    simp only [rightPerm142, p1030, p893, p773, p511, p256, p153, p139, p110, p99, p90, p71, p61, p58, p55, p53, p51, p49, p46, p45, p44, p43, p42, p41, p40, p39, p38, p37, p36, p35, p34, p33, p32, p31, p29, p28, p27, p26, p25, p24, p23, p22, p21, p20, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2858) x =
    (L0Rep (L0Act 0 2858) * evalWord L1Gen (L0Factor 0 2858)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap142_eq, ← rightMap142_eq]
  exact Residual1Cache.ofSlices point142_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
