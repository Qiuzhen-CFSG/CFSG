module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level12Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 141

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap141 (x : Nat) : Nat := force t97 (force t150 (t11 x))
private def leftPerm141 : Equiv.Perm (Fin 4060) := p97 * (p150 * (p11))
private theorem leftMap141_eq (x : Fin 4060) :
    leftMap141 x.val = (leftPerm141 x).val := (compose (t := fun x => force t97 (force t150 (t11 x))) (a := t97) (b := fun x => force t150 (t11 x)) (fun _ => rfl) c97 (compose (t := fun x => force t150 (t11 x)) (a := t150) (b := fun x => t11 x) (fun _ => rfl) c150 c11)) x

private def rightMap141 (x : Nat) : Nat := force t183 (force t59 (force t731 (force t23 (force t1039 (force t4 (force t114 (force t13 (t431 x))))))))
private def rightPerm141 : Equiv.Perm (Fin 4060) := p183 * (p59 * (p731 * (p23 * (p1039 * (p4 * (p114 * (p13 * (p431))))))))
private theorem rightMap141_eq (x : Fin 4060) :
    rightMap141 x.val = (rightPerm141 x).val := (compose (t := fun x => force t183 (force t59 (force t731 (force t23 (force t1039 (force t4 (force t114 (force t13 (t431 x))))))))) (a := t183) (b := fun x => force t59 (force t731 (force t23 (force t1039 (force t4 (force t114 (force t13 (t431 x)))))))) (fun _ => rfl) c183 (compose (t := fun x => force t59 (force t731 (force t23 (force t1039 (force t4 (force t114 (force t13 (t431 x)))))))) (a := t59) (b := fun x => force t731 (force t23 (force t1039 (force t4 (force t114 (force t13 (t431 x))))))) (fun _ => rfl) c59 (compose (t := fun x => force t731 (force t23 (force t1039 (force t4 (force t114 (force t13 (t431 x))))))) (a := t731) (b := fun x => force t23 (force t1039 (force t4 (force t114 (force t13 (t431 x)))))) (fun _ => rfl) c731 (compose (t := fun x => force t23 (force t1039 (force t4 (force t114 (force t13 (t431 x)))))) (a := t23) (b := fun x => force t1039 (force t4 (force t114 (force t13 (t431 x))))) (fun _ => rfl) c23 (compose (t := fun x => force t1039 (force t4 (force t114 (force t13 (t431 x))))) (a := t1039) (b := fun x => force t4 (force t114 (force t13 (t431 x)))) (fun _ => rfl) c1039 (compose (t := fun x => force t4 (force t114 (force t13 (t431 x)))) (a := t4) (b := fun x => force t114 (force t13 (t431 x))) (fun _ => rfl) c4 (compose (t := fun x => force t114 (force t13 (t431 x))) (a := t114) (b := fun x => force t13 (t431 x)) (fun _ => rfl) c114 (compose (t := fun x => force t13 (t431 x)) (a := t13) (b := fun x => t431 x) (fun _ => rfl) c13 c431)))))))) x

set_option maxHeartbeats 1600000 in
private theorem point141slice0 : Residual1Cache.slice leftMap141 rightMap141 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice1 : Residual1Cache.slice leftMap141 rightMap141 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice2 : Residual1Cache.slice leftMap141 rightMap141 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice3 : Residual1Cache.slice leftMap141 rightMap141 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice4 : Residual1Cache.slice leftMap141 rightMap141 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice5 : Residual1Cache.slice leftMap141 rightMap141 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice6 : Residual1Cache.slice leftMap141 rightMap141 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice7 : Residual1Cache.slice leftMap141 rightMap141 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice8 : Residual1Cache.slice leftMap141 rightMap141 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice9 : Residual1Cache.slice leftMap141 rightMap141 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice10 : Residual1Cache.slice leftMap141 rightMap141 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice11 : Residual1Cache.slice leftMap141 rightMap141 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice12 : Residual1Cache.slice leftMap141 rightMap141 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice13 : Residual1Cache.slice leftMap141 rightMap141 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice14 : Residual1Cache.slice leftMap141 rightMap141 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice15 : Residual1Cache.slice leftMap141 rightMap141 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice16 : Residual1Cache.slice leftMap141 rightMap141 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice17 : Residual1Cache.slice leftMap141 rightMap141 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice18 : Residual1Cache.slice leftMap141 rightMap141 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice19 : Residual1Cache.slice leftMap141 rightMap141 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice20 : Residual1Cache.slice leftMap141 rightMap141 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice21 : Residual1Cache.slice leftMap141 rightMap141 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice22 : Residual1Cache.slice leftMap141 rightMap141 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice23 : Residual1Cache.slice leftMap141 rightMap141 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice24 : Residual1Cache.slice leftMap141 rightMap141 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice25 : Residual1Cache.slice leftMap141 rightMap141 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice26 : Residual1Cache.slice leftMap141 rightMap141 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice27 : Residual1Cache.slice leftMap141 rightMap141 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice28 : Residual1Cache.slice leftMap141 rightMap141 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice29 : Residual1Cache.slice leftMap141 rightMap141 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice30 : Residual1Cache.slice leftMap141 rightMap141 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice31 : Residual1Cache.slice leftMap141 rightMap141 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice32 : Residual1Cache.slice leftMap141 rightMap141 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice33 : Residual1Cache.slice leftMap141 rightMap141 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice34 : Residual1Cache.slice leftMap141 rightMap141 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice35 : Residual1Cache.slice leftMap141 rightMap141 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice36 : Residual1Cache.slice leftMap141 rightMap141 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice37 : Residual1Cache.slice leftMap141 rightMap141 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice38 : Residual1Cache.slice leftMap141 rightMap141 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice39 : Residual1Cache.slice leftMap141 rightMap141 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice40 : Residual1Cache.slice leftMap141 rightMap141 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice41 : Residual1Cache.slice leftMap141 rightMap141 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice42 : Residual1Cache.slice leftMap141 rightMap141 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice43 : Residual1Cache.slice leftMap141 rightMap141 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice44 : Residual1Cache.slice leftMap141 rightMap141 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice45 : Residual1Cache.slice leftMap141 rightMap141 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice46 : Residual1Cache.slice leftMap141 rightMap141 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice47 : Residual1Cache.slice leftMap141 rightMap141 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice48 : Residual1Cache.slice leftMap141 rightMap141 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice49 : Residual1Cache.slice leftMap141 rightMap141 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice50 : Residual1Cache.slice leftMap141 rightMap141 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice51 : Residual1Cache.slice leftMap141 rightMap141 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice52 : Residual1Cache.slice leftMap141 rightMap141 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice53 : Residual1Cache.slice leftMap141 rightMap141 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice54 : Residual1Cache.slice leftMap141 rightMap141 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice55 : Residual1Cache.slice leftMap141 rightMap141 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice56 : Residual1Cache.slice leftMap141 rightMap141 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice57 : Residual1Cache.slice leftMap141 rightMap141 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice58 : Residual1Cache.slice leftMap141 rightMap141 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice59 : Residual1Cache.slice leftMap141 rightMap141 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice60 : Residual1Cache.slice leftMap141 rightMap141 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice61 : Residual1Cache.slice leftMap141 rightMap141 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice62 : Residual1Cache.slice leftMap141 rightMap141 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice63 : Residual1Cache.slice leftMap141 rightMap141 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice64 : Residual1Cache.slice leftMap141 rightMap141 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice65 : Residual1Cache.slice leftMap141 rightMap141 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice66 : Residual1Cache.slice leftMap141 rightMap141 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice67 : Residual1Cache.slice leftMap141 rightMap141 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice68 : Residual1Cache.slice leftMap141 rightMap141 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice69 : Residual1Cache.slice leftMap141 rightMap141 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice70 : Residual1Cache.slice leftMap141 rightMap141 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice71 : Residual1Cache.slice leftMap141 rightMap141 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice72 : Residual1Cache.slice leftMap141 rightMap141 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice73 : Residual1Cache.slice leftMap141 rightMap141 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice74 : Residual1Cache.slice leftMap141 rightMap141 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice75 : Residual1Cache.slice leftMap141 rightMap141 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice76 : Residual1Cache.slice leftMap141 rightMap141 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice77 : Residual1Cache.slice leftMap141 rightMap141 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice78 : Residual1Cache.slice leftMap141 rightMap141 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice79 : Residual1Cache.slice leftMap141 rightMap141 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice80 : Residual1Cache.slice leftMap141 rightMap141 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice81 : Residual1Cache.slice leftMap141 rightMap141 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice82 : Residual1Cache.slice leftMap141 rightMap141 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice83 : Residual1Cache.slice leftMap141 rightMap141 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice84 : Residual1Cache.slice leftMap141 rightMap141 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice85 : Residual1Cache.slice leftMap141 rightMap141 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice86 : Residual1Cache.slice leftMap141 rightMap141 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice87 : Residual1Cache.slice leftMap141 rightMap141 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice88 : Residual1Cache.slice leftMap141 rightMap141 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice89 : Residual1Cache.slice leftMap141 rightMap141 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice90 : Residual1Cache.slice leftMap141 rightMap141 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice91 : Residual1Cache.slice leftMap141 rightMap141 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice92 : Residual1Cache.slice leftMap141 rightMap141 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice93 : Residual1Cache.slice leftMap141 rightMap141 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice94 : Residual1Cache.slice leftMap141 rightMap141 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice95 : Residual1Cache.slice leftMap141 rightMap141 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice96 : Residual1Cache.slice leftMap141 rightMap141 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice97 : Residual1Cache.slice leftMap141 rightMap141 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice98 : Residual1Cache.slice leftMap141 rightMap141 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice99 : Residual1Cache.slice leftMap141 rightMap141 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice100 : Residual1Cache.slice leftMap141 rightMap141 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice101 : Residual1Cache.slice leftMap141 rightMap141 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice102 : Residual1Cache.slice leftMap141 rightMap141 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice103 : Residual1Cache.slice leftMap141 rightMap141 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice104 : Residual1Cache.slice leftMap141 rightMap141 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice105 : Residual1Cache.slice leftMap141 rightMap141 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice106 : Residual1Cache.slice leftMap141 rightMap141 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice107 : Residual1Cache.slice leftMap141 rightMap141 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice108 : Residual1Cache.slice leftMap141 rightMap141 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice109 : Residual1Cache.slice leftMap141 rightMap141 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice110 : Residual1Cache.slice leftMap141 rightMap141 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice111 : Residual1Cache.slice leftMap141 rightMap141 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice112 : Residual1Cache.slice leftMap141 rightMap141 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice113 : Residual1Cache.slice leftMap141 rightMap141 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice114 : Residual1Cache.slice leftMap141 rightMap141 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice115 : Residual1Cache.slice leftMap141 rightMap141 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice116 : Residual1Cache.slice leftMap141 rightMap141 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice117 : Residual1Cache.slice leftMap141 rightMap141 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice118 : Residual1Cache.slice leftMap141 rightMap141 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice119 : Residual1Cache.slice leftMap141 rightMap141 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice120 : Residual1Cache.slice leftMap141 rightMap141 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice121 : Residual1Cache.slice leftMap141 rightMap141 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice122 : Residual1Cache.slice leftMap141 rightMap141 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice123 : Residual1Cache.slice leftMap141 rightMap141 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice124 : Residual1Cache.slice leftMap141 rightMap141 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice125 : Residual1Cache.slice leftMap141 rightMap141 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice126 : Residual1Cache.slice leftMap141 rightMap141 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice127 : Residual1Cache.slice leftMap141 rightMap141 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice128 : Residual1Cache.slice leftMap141 rightMap141 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice129 : Residual1Cache.slice leftMap141 rightMap141 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice130 : Residual1Cache.slice leftMap141 rightMap141 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice131 : Residual1Cache.slice leftMap141 rightMap141 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice132 : Residual1Cache.slice leftMap141 rightMap141 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice133 : Residual1Cache.slice leftMap141 rightMap141 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice134 : Residual1Cache.slice leftMap141 rightMap141 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice135 : Residual1Cache.slice leftMap141 rightMap141 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice136 : Residual1Cache.slice leftMap141 rightMap141 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice137 : Residual1Cache.slice leftMap141 rightMap141 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice138 : Residual1Cache.slice leftMap141 rightMap141 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice139 : Residual1Cache.slice leftMap141 rightMap141 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice140 : Residual1Cache.slice leftMap141 rightMap141 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice141 : Residual1Cache.slice leftMap141 rightMap141 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice142 : Residual1Cache.slice leftMap141 rightMap141 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice143 : Residual1Cache.slice leftMap141 rightMap141 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice144 : Residual1Cache.slice leftMap141 rightMap141 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice145 : Residual1Cache.slice leftMap141 rightMap141 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice146 : Residual1Cache.slice leftMap141 rightMap141 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice147 : Residual1Cache.slice leftMap141 rightMap141 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice148 : Residual1Cache.slice leftMap141 rightMap141 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice149 : Residual1Cache.slice leftMap141 rightMap141 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice150 : Residual1Cache.slice leftMap141 rightMap141 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice151 : Residual1Cache.slice leftMap141 rightMap141 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice152 : Residual1Cache.slice leftMap141 rightMap141 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice153 : Residual1Cache.slice leftMap141 rightMap141 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice154 : Residual1Cache.slice leftMap141 rightMap141 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice155 : Residual1Cache.slice leftMap141 rightMap141 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice156 : Residual1Cache.slice leftMap141 rightMap141 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice157 : Residual1Cache.slice leftMap141 rightMap141 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice158 : Residual1Cache.slice leftMap141 rightMap141 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice159 : Residual1Cache.slice leftMap141 rightMap141 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice160 : Residual1Cache.slice leftMap141 rightMap141 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice161 : Residual1Cache.slice leftMap141 rightMap141 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice162 : Residual1Cache.slice leftMap141 rightMap141 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice163 : Residual1Cache.slice leftMap141 rightMap141 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice164 : Residual1Cache.slice leftMap141 rightMap141 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice165 : Residual1Cache.slice leftMap141 rightMap141 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice166 : Residual1Cache.slice leftMap141 rightMap141 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice167 : Residual1Cache.slice leftMap141 rightMap141 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice168 : Residual1Cache.slice leftMap141 rightMap141 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice169 : Residual1Cache.slice leftMap141 rightMap141 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice170 : Residual1Cache.slice leftMap141 rightMap141 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice171 : Residual1Cache.slice leftMap141 rightMap141 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice172 : Residual1Cache.slice leftMap141 rightMap141 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice173 : Residual1Cache.slice leftMap141 rightMap141 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice174 : Residual1Cache.slice leftMap141 rightMap141 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice175 : Residual1Cache.slice leftMap141 rightMap141 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice176 : Residual1Cache.slice leftMap141 rightMap141 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice177 : Residual1Cache.slice leftMap141 rightMap141 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice178 : Residual1Cache.slice leftMap141 rightMap141 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice179 : Residual1Cache.slice leftMap141 rightMap141 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice180 : Residual1Cache.slice leftMap141 rightMap141 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice181 : Residual1Cache.slice leftMap141 rightMap141 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice182 : Residual1Cache.slice leftMap141 rightMap141 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice183 : Residual1Cache.slice leftMap141 rightMap141 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice184 : Residual1Cache.slice leftMap141 rightMap141 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice185 : Residual1Cache.slice leftMap141 rightMap141 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice186 : Residual1Cache.slice leftMap141 rightMap141 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice187 : Residual1Cache.slice leftMap141 rightMap141 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice188 : Residual1Cache.slice leftMap141 rightMap141 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice189 : Residual1Cache.slice leftMap141 rightMap141 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice190 : Residual1Cache.slice leftMap141 rightMap141 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice191 : Residual1Cache.slice leftMap141 rightMap141 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice192 : Residual1Cache.slice leftMap141 rightMap141 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice193 : Residual1Cache.slice leftMap141 rightMap141 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice194 : Residual1Cache.slice leftMap141 rightMap141 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice195 : Residual1Cache.slice leftMap141 rightMap141 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice196 : Residual1Cache.slice leftMap141 rightMap141 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice197 : Residual1Cache.slice leftMap141 rightMap141 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice198 : Residual1Cache.slice leftMap141 rightMap141 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice199 : Residual1Cache.slice leftMap141 rightMap141 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice200 : Residual1Cache.slice leftMap141 rightMap141 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice201 : Residual1Cache.slice leftMap141 rightMap141 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point141slice202 : Residual1Cache.slice leftMap141 rightMap141 202 = true := by
  decide +kernel

private theorem point141_slices : ∀ c, Residual1Cache.slice leftMap141 rightMap141 c = true := by
  intro c
  fin_cases c
  · exact point141slice0
  · exact point141slice1
  · exact point141slice2
  · exact point141slice3
  · exact point141slice4
  · exact point141slice5
  · exact point141slice6
  · exact point141slice7
  · exact point141slice8
  · exact point141slice9
  · exact point141slice10
  · exact point141slice11
  · exact point141slice12
  · exact point141slice13
  · exact point141slice14
  · exact point141slice15
  · exact point141slice16
  · exact point141slice17
  · exact point141slice18
  · exact point141slice19
  · exact point141slice20
  · exact point141slice21
  · exact point141slice22
  · exact point141slice23
  · exact point141slice24
  · exact point141slice25
  · exact point141slice26
  · exact point141slice27
  · exact point141slice28
  · exact point141slice29
  · exact point141slice30
  · exact point141slice31
  · exact point141slice32
  · exact point141slice33
  · exact point141slice34
  · exact point141slice35
  · exact point141slice36
  · exact point141slice37
  · exact point141slice38
  · exact point141slice39
  · exact point141slice40
  · exact point141slice41
  · exact point141slice42
  · exact point141slice43
  · exact point141slice44
  · exact point141slice45
  · exact point141slice46
  · exact point141slice47
  · exact point141slice48
  · exact point141slice49
  · exact point141slice50
  · exact point141slice51
  · exact point141slice52
  · exact point141slice53
  · exact point141slice54
  · exact point141slice55
  · exact point141slice56
  · exact point141slice57
  · exact point141slice58
  · exact point141slice59
  · exact point141slice60
  · exact point141slice61
  · exact point141slice62
  · exact point141slice63
  · exact point141slice64
  · exact point141slice65
  · exact point141slice66
  · exact point141slice67
  · exact point141slice68
  · exact point141slice69
  · exact point141slice70
  · exact point141slice71
  · exact point141slice72
  · exact point141slice73
  · exact point141slice74
  · exact point141slice75
  · exact point141slice76
  · exact point141slice77
  · exact point141slice78
  · exact point141slice79
  · exact point141slice80
  · exact point141slice81
  · exact point141slice82
  · exact point141slice83
  · exact point141slice84
  · exact point141slice85
  · exact point141slice86
  · exact point141slice87
  · exact point141slice88
  · exact point141slice89
  · exact point141slice90
  · exact point141slice91
  · exact point141slice92
  · exact point141slice93
  · exact point141slice94
  · exact point141slice95
  · exact point141slice96
  · exact point141slice97
  · exact point141slice98
  · exact point141slice99
  · exact point141slice100
  · exact point141slice101
  · exact point141slice102
  · exact point141slice103
  · exact point141slice104
  · exact point141slice105
  · exact point141slice106
  · exact point141slice107
  · exact point141slice108
  · exact point141slice109
  · exact point141slice110
  · exact point141slice111
  · exact point141slice112
  · exact point141slice113
  · exact point141slice114
  · exact point141slice115
  · exact point141slice116
  · exact point141slice117
  · exact point141slice118
  · exact point141slice119
  · exact point141slice120
  · exact point141slice121
  · exact point141slice122
  · exact point141slice123
  · exact point141slice124
  · exact point141slice125
  · exact point141slice126
  · exact point141slice127
  · exact point141slice128
  · exact point141slice129
  · exact point141slice130
  · exact point141slice131
  · exact point141slice132
  · exact point141slice133
  · exact point141slice134
  · exact point141slice135
  · exact point141slice136
  · exact point141slice137
  · exact point141slice138
  · exact point141slice139
  · exact point141slice140
  · exact point141slice141
  · exact point141slice142
  · exact point141slice143
  · exact point141slice144
  · exact point141slice145
  · exact point141slice146
  · exact point141slice147
  · exact point141slice148
  · exact point141slice149
  · exact point141slice150
  · exact point141slice151
  · exact point141slice152
  · exact point141slice153
  · exact point141slice154
  · exact point141slice155
  · exact point141slice156
  · exact point141slice157
  · exact point141slice158
  · exact point141slice159
  · exact point141slice160
  · exact point141slice161
  · exact point141slice162
  · exact point141slice163
  · exact point141slice164
  · exact point141slice165
  · exact point141slice166
  · exact point141slice167
  · exact point141slice168
  · exact point141slice169
  · exact point141slice170
  · exact point141slice171
  · exact point141slice172
  · exact point141slice173
  · exact point141slice174
  · exact point141slice175
  · exact point141slice176
  · exact point141slice177
  · exact point141slice178
  · exact point141slice179
  · exact point141slice180
  · exact point141slice181
  · exact point141slice182
  · exact point141slice183
  · exact point141slice184
  · exact point141slice185
  · exact point141slice186
  · exact point141slice187
  · exact point141slice188
  · exact point141slice189
  · exact point141slice190
  · exact point141slice191
  · exact point141slice192
  · exact point141slice193
  · exact point141slice194
  · exact point141slice195
  · exact point141slice196
  · exact point141slice197
  · exact point141slice198
  · exact point141slice199
  · exact point141slice200
  · exact point141slice201
  · exact point141slice202

set_option maxHeartbeats 1600000 in
public theorem point141 : stepCheck 0 2854 := by
  have hleft : L0Gen 0 * L0Rep 2854 = leftPerm141 := by
    change L0Gen 0 * evalWord L0Gen [3, 0, 3, 0, 1, 1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0] = leftPerm141
    simp only [leftPerm141, p150, p97, p50, p47, p27, p20, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2854) * evalWord L1Gen (L0Factor 0 2854) = rightPerm141 := by
    change evalWord L0Gen [3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1, 0] * evalWord L1Gen [0, 1, 0, 3, 0, 0, 3, 0, 1, 2, 1, 0, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3] = rightPerm141
    simp only [rightPerm141, p1039, p731, p431, p430, p183, p114, p96, p63, p59, p53, p46, p44, p43, p42, p39, p37, p36, p34, p33, p32, p29, p28, p25, p24, p23, p22, p21, p20, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2854) x =
    (L0Rep (L0Act 0 2854) * evalWord L1Gen (L0Factor 0 2854)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap141_eq, ← rightMap141_eq]
  exact Residual1Cache.ofSlices point141_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
