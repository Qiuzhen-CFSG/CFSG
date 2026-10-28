module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part1
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 135

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap135 (x : Nat) : Nat := force t141 (t990 x)
private def leftPerm135 : Equiv.Perm (Fin 4060) := p141 * (p990)
private theorem leftMap135_eq (x : Fin 4060) :
    leftMap135 x.val = (leftPerm135 x).val := (compose (t := fun x => force t141 (t990 x)) (a := t141) (b := fun x => t990 x) (fun _ => rfl) c141 c990) x

private def rightMap135 (x : Nat) : Nat := force t252 (force t11 (force t59 (force t4 (force t4 (force t773 (force t403 (force t405 (t33 x))))))))
private def rightPerm135 : Equiv.Perm (Fin 4060) := p252 * (p11 * (p59 * (p4 * (p4 * (p773 * (p403 * (p405 * (p33))))))))
private theorem rightMap135_eq (x : Fin 4060) :
    rightMap135 x.val = (rightPerm135 x).val := (compose (t := fun x => force t252 (force t11 (force t59 (force t4 (force t4 (force t773 (force t403 (force t405 (t33 x))))))))) (a := t252) (b := fun x => force t11 (force t59 (force t4 (force t4 (force t773 (force t403 (force t405 (t33 x)))))))) (fun _ => rfl) c252 (compose (t := fun x => force t11 (force t59 (force t4 (force t4 (force t773 (force t403 (force t405 (t33 x)))))))) (a := t11) (b := fun x => force t59 (force t4 (force t4 (force t773 (force t403 (force t405 (t33 x))))))) (fun _ => rfl) c11 (compose (t := fun x => force t59 (force t4 (force t4 (force t773 (force t403 (force t405 (t33 x))))))) (a := t59) (b := fun x => force t4 (force t4 (force t773 (force t403 (force t405 (t33 x)))))) (fun _ => rfl) c59 (compose (t := fun x => force t4 (force t4 (force t773 (force t403 (force t405 (t33 x)))))) (a := t4) (b := fun x => force t4 (force t773 (force t403 (force t405 (t33 x))))) (fun _ => rfl) c4 (compose (t := fun x => force t4 (force t773 (force t403 (force t405 (t33 x))))) (a := t4) (b := fun x => force t773 (force t403 (force t405 (t33 x)))) (fun _ => rfl) c4 (compose (t := fun x => force t773 (force t403 (force t405 (t33 x)))) (a := t773) (b := fun x => force t403 (force t405 (t33 x))) (fun _ => rfl) c773 (compose (t := fun x => force t403 (force t405 (t33 x))) (a := t403) (b := fun x => force t405 (t33 x)) (fun _ => rfl) c403 (compose (t := fun x => force t405 (t33 x)) (a := t405) (b := fun x => t33 x) (fun _ => rfl) c405 c33)))))))) x

set_option maxHeartbeats 1600000 in
private theorem point135slice0 : Residual1Cache.slice leftMap135 rightMap135 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice1 : Residual1Cache.slice leftMap135 rightMap135 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice2 : Residual1Cache.slice leftMap135 rightMap135 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice3 : Residual1Cache.slice leftMap135 rightMap135 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice4 : Residual1Cache.slice leftMap135 rightMap135 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice5 : Residual1Cache.slice leftMap135 rightMap135 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice6 : Residual1Cache.slice leftMap135 rightMap135 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice7 : Residual1Cache.slice leftMap135 rightMap135 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice8 : Residual1Cache.slice leftMap135 rightMap135 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice9 : Residual1Cache.slice leftMap135 rightMap135 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice10 : Residual1Cache.slice leftMap135 rightMap135 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice11 : Residual1Cache.slice leftMap135 rightMap135 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice12 : Residual1Cache.slice leftMap135 rightMap135 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice13 : Residual1Cache.slice leftMap135 rightMap135 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice14 : Residual1Cache.slice leftMap135 rightMap135 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice15 : Residual1Cache.slice leftMap135 rightMap135 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice16 : Residual1Cache.slice leftMap135 rightMap135 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice17 : Residual1Cache.slice leftMap135 rightMap135 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice18 : Residual1Cache.slice leftMap135 rightMap135 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice19 : Residual1Cache.slice leftMap135 rightMap135 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice20 : Residual1Cache.slice leftMap135 rightMap135 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice21 : Residual1Cache.slice leftMap135 rightMap135 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice22 : Residual1Cache.slice leftMap135 rightMap135 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice23 : Residual1Cache.slice leftMap135 rightMap135 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice24 : Residual1Cache.slice leftMap135 rightMap135 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice25 : Residual1Cache.slice leftMap135 rightMap135 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice26 : Residual1Cache.slice leftMap135 rightMap135 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice27 : Residual1Cache.slice leftMap135 rightMap135 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice28 : Residual1Cache.slice leftMap135 rightMap135 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice29 : Residual1Cache.slice leftMap135 rightMap135 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice30 : Residual1Cache.slice leftMap135 rightMap135 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice31 : Residual1Cache.slice leftMap135 rightMap135 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice32 : Residual1Cache.slice leftMap135 rightMap135 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice33 : Residual1Cache.slice leftMap135 rightMap135 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice34 : Residual1Cache.slice leftMap135 rightMap135 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice35 : Residual1Cache.slice leftMap135 rightMap135 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice36 : Residual1Cache.slice leftMap135 rightMap135 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice37 : Residual1Cache.slice leftMap135 rightMap135 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice38 : Residual1Cache.slice leftMap135 rightMap135 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice39 : Residual1Cache.slice leftMap135 rightMap135 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice40 : Residual1Cache.slice leftMap135 rightMap135 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice41 : Residual1Cache.slice leftMap135 rightMap135 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice42 : Residual1Cache.slice leftMap135 rightMap135 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice43 : Residual1Cache.slice leftMap135 rightMap135 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice44 : Residual1Cache.slice leftMap135 rightMap135 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice45 : Residual1Cache.slice leftMap135 rightMap135 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice46 : Residual1Cache.slice leftMap135 rightMap135 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice47 : Residual1Cache.slice leftMap135 rightMap135 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice48 : Residual1Cache.slice leftMap135 rightMap135 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice49 : Residual1Cache.slice leftMap135 rightMap135 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice50 : Residual1Cache.slice leftMap135 rightMap135 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice51 : Residual1Cache.slice leftMap135 rightMap135 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice52 : Residual1Cache.slice leftMap135 rightMap135 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice53 : Residual1Cache.slice leftMap135 rightMap135 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice54 : Residual1Cache.slice leftMap135 rightMap135 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice55 : Residual1Cache.slice leftMap135 rightMap135 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice56 : Residual1Cache.slice leftMap135 rightMap135 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice57 : Residual1Cache.slice leftMap135 rightMap135 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice58 : Residual1Cache.slice leftMap135 rightMap135 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice59 : Residual1Cache.slice leftMap135 rightMap135 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice60 : Residual1Cache.slice leftMap135 rightMap135 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice61 : Residual1Cache.slice leftMap135 rightMap135 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice62 : Residual1Cache.slice leftMap135 rightMap135 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice63 : Residual1Cache.slice leftMap135 rightMap135 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice64 : Residual1Cache.slice leftMap135 rightMap135 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice65 : Residual1Cache.slice leftMap135 rightMap135 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice66 : Residual1Cache.slice leftMap135 rightMap135 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice67 : Residual1Cache.slice leftMap135 rightMap135 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice68 : Residual1Cache.slice leftMap135 rightMap135 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice69 : Residual1Cache.slice leftMap135 rightMap135 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice70 : Residual1Cache.slice leftMap135 rightMap135 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice71 : Residual1Cache.slice leftMap135 rightMap135 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice72 : Residual1Cache.slice leftMap135 rightMap135 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice73 : Residual1Cache.slice leftMap135 rightMap135 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice74 : Residual1Cache.slice leftMap135 rightMap135 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice75 : Residual1Cache.slice leftMap135 rightMap135 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice76 : Residual1Cache.slice leftMap135 rightMap135 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice77 : Residual1Cache.slice leftMap135 rightMap135 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice78 : Residual1Cache.slice leftMap135 rightMap135 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice79 : Residual1Cache.slice leftMap135 rightMap135 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice80 : Residual1Cache.slice leftMap135 rightMap135 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice81 : Residual1Cache.slice leftMap135 rightMap135 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice82 : Residual1Cache.slice leftMap135 rightMap135 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice83 : Residual1Cache.slice leftMap135 rightMap135 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice84 : Residual1Cache.slice leftMap135 rightMap135 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice85 : Residual1Cache.slice leftMap135 rightMap135 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice86 : Residual1Cache.slice leftMap135 rightMap135 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice87 : Residual1Cache.slice leftMap135 rightMap135 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice88 : Residual1Cache.slice leftMap135 rightMap135 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice89 : Residual1Cache.slice leftMap135 rightMap135 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice90 : Residual1Cache.slice leftMap135 rightMap135 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice91 : Residual1Cache.slice leftMap135 rightMap135 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice92 : Residual1Cache.slice leftMap135 rightMap135 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice93 : Residual1Cache.slice leftMap135 rightMap135 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice94 : Residual1Cache.slice leftMap135 rightMap135 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice95 : Residual1Cache.slice leftMap135 rightMap135 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice96 : Residual1Cache.slice leftMap135 rightMap135 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice97 : Residual1Cache.slice leftMap135 rightMap135 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice98 : Residual1Cache.slice leftMap135 rightMap135 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice99 : Residual1Cache.slice leftMap135 rightMap135 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice100 : Residual1Cache.slice leftMap135 rightMap135 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice101 : Residual1Cache.slice leftMap135 rightMap135 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice102 : Residual1Cache.slice leftMap135 rightMap135 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice103 : Residual1Cache.slice leftMap135 rightMap135 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice104 : Residual1Cache.slice leftMap135 rightMap135 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice105 : Residual1Cache.slice leftMap135 rightMap135 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice106 : Residual1Cache.slice leftMap135 rightMap135 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice107 : Residual1Cache.slice leftMap135 rightMap135 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice108 : Residual1Cache.slice leftMap135 rightMap135 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice109 : Residual1Cache.slice leftMap135 rightMap135 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice110 : Residual1Cache.slice leftMap135 rightMap135 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice111 : Residual1Cache.slice leftMap135 rightMap135 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice112 : Residual1Cache.slice leftMap135 rightMap135 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice113 : Residual1Cache.slice leftMap135 rightMap135 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice114 : Residual1Cache.slice leftMap135 rightMap135 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice115 : Residual1Cache.slice leftMap135 rightMap135 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice116 : Residual1Cache.slice leftMap135 rightMap135 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice117 : Residual1Cache.slice leftMap135 rightMap135 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice118 : Residual1Cache.slice leftMap135 rightMap135 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice119 : Residual1Cache.slice leftMap135 rightMap135 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice120 : Residual1Cache.slice leftMap135 rightMap135 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice121 : Residual1Cache.slice leftMap135 rightMap135 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice122 : Residual1Cache.slice leftMap135 rightMap135 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice123 : Residual1Cache.slice leftMap135 rightMap135 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice124 : Residual1Cache.slice leftMap135 rightMap135 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice125 : Residual1Cache.slice leftMap135 rightMap135 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice126 : Residual1Cache.slice leftMap135 rightMap135 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice127 : Residual1Cache.slice leftMap135 rightMap135 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice128 : Residual1Cache.slice leftMap135 rightMap135 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice129 : Residual1Cache.slice leftMap135 rightMap135 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice130 : Residual1Cache.slice leftMap135 rightMap135 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice131 : Residual1Cache.slice leftMap135 rightMap135 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice132 : Residual1Cache.slice leftMap135 rightMap135 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice133 : Residual1Cache.slice leftMap135 rightMap135 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice134 : Residual1Cache.slice leftMap135 rightMap135 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice135 : Residual1Cache.slice leftMap135 rightMap135 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice136 : Residual1Cache.slice leftMap135 rightMap135 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice137 : Residual1Cache.slice leftMap135 rightMap135 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice138 : Residual1Cache.slice leftMap135 rightMap135 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice139 : Residual1Cache.slice leftMap135 rightMap135 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice140 : Residual1Cache.slice leftMap135 rightMap135 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice141 : Residual1Cache.slice leftMap135 rightMap135 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice142 : Residual1Cache.slice leftMap135 rightMap135 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice143 : Residual1Cache.slice leftMap135 rightMap135 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice144 : Residual1Cache.slice leftMap135 rightMap135 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice145 : Residual1Cache.slice leftMap135 rightMap135 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice146 : Residual1Cache.slice leftMap135 rightMap135 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice147 : Residual1Cache.slice leftMap135 rightMap135 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice148 : Residual1Cache.slice leftMap135 rightMap135 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice149 : Residual1Cache.slice leftMap135 rightMap135 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice150 : Residual1Cache.slice leftMap135 rightMap135 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice151 : Residual1Cache.slice leftMap135 rightMap135 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice152 : Residual1Cache.slice leftMap135 rightMap135 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice153 : Residual1Cache.slice leftMap135 rightMap135 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice154 : Residual1Cache.slice leftMap135 rightMap135 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice155 : Residual1Cache.slice leftMap135 rightMap135 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice156 : Residual1Cache.slice leftMap135 rightMap135 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice157 : Residual1Cache.slice leftMap135 rightMap135 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice158 : Residual1Cache.slice leftMap135 rightMap135 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice159 : Residual1Cache.slice leftMap135 rightMap135 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice160 : Residual1Cache.slice leftMap135 rightMap135 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice161 : Residual1Cache.slice leftMap135 rightMap135 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice162 : Residual1Cache.slice leftMap135 rightMap135 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice163 : Residual1Cache.slice leftMap135 rightMap135 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice164 : Residual1Cache.slice leftMap135 rightMap135 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice165 : Residual1Cache.slice leftMap135 rightMap135 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice166 : Residual1Cache.slice leftMap135 rightMap135 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice167 : Residual1Cache.slice leftMap135 rightMap135 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice168 : Residual1Cache.slice leftMap135 rightMap135 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice169 : Residual1Cache.slice leftMap135 rightMap135 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice170 : Residual1Cache.slice leftMap135 rightMap135 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice171 : Residual1Cache.slice leftMap135 rightMap135 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice172 : Residual1Cache.slice leftMap135 rightMap135 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice173 : Residual1Cache.slice leftMap135 rightMap135 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice174 : Residual1Cache.slice leftMap135 rightMap135 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice175 : Residual1Cache.slice leftMap135 rightMap135 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice176 : Residual1Cache.slice leftMap135 rightMap135 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice177 : Residual1Cache.slice leftMap135 rightMap135 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice178 : Residual1Cache.slice leftMap135 rightMap135 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice179 : Residual1Cache.slice leftMap135 rightMap135 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice180 : Residual1Cache.slice leftMap135 rightMap135 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice181 : Residual1Cache.slice leftMap135 rightMap135 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice182 : Residual1Cache.slice leftMap135 rightMap135 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice183 : Residual1Cache.slice leftMap135 rightMap135 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice184 : Residual1Cache.slice leftMap135 rightMap135 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice185 : Residual1Cache.slice leftMap135 rightMap135 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice186 : Residual1Cache.slice leftMap135 rightMap135 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice187 : Residual1Cache.slice leftMap135 rightMap135 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice188 : Residual1Cache.slice leftMap135 rightMap135 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice189 : Residual1Cache.slice leftMap135 rightMap135 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice190 : Residual1Cache.slice leftMap135 rightMap135 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice191 : Residual1Cache.slice leftMap135 rightMap135 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice192 : Residual1Cache.slice leftMap135 rightMap135 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice193 : Residual1Cache.slice leftMap135 rightMap135 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice194 : Residual1Cache.slice leftMap135 rightMap135 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice195 : Residual1Cache.slice leftMap135 rightMap135 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice196 : Residual1Cache.slice leftMap135 rightMap135 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice197 : Residual1Cache.slice leftMap135 rightMap135 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice198 : Residual1Cache.slice leftMap135 rightMap135 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice199 : Residual1Cache.slice leftMap135 rightMap135 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice200 : Residual1Cache.slice leftMap135 rightMap135 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice201 : Residual1Cache.slice leftMap135 rightMap135 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point135slice202 : Residual1Cache.slice leftMap135 rightMap135 202 = true := by
  decide +kernel

private theorem point135_slices : ∀ c, Residual1Cache.slice leftMap135 rightMap135 c = true := by
  intro c
  fin_cases c
  · exact point135slice0
  · exact point135slice1
  · exact point135slice2
  · exact point135slice3
  · exact point135slice4
  · exact point135slice5
  · exact point135slice6
  · exact point135slice7
  · exact point135slice8
  · exact point135slice9
  · exact point135slice10
  · exact point135slice11
  · exact point135slice12
  · exact point135slice13
  · exact point135slice14
  · exact point135slice15
  · exact point135slice16
  · exact point135slice17
  · exact point135slice18
  · exact point135slice19
  · exact point135slice20
  · exact point135slice21
  · exact point135slice22
  · exact point135slice23
  · exact point135slice24
  · exact point135slice25
  · exact point135slice26
  · exact point135slice27
  · exact point135slice28
  · exact point135slice29
  · exact point135slice30
  · exact point135slice31
  · exact point135slice32
  · exact point135slice33
  · exact point135slice34
  · exact point135slice35
  · exact point135slice36
  · exact point135slice37
  · exact point135slice38
  · exact point135slice39
  · exact point135slice40
  · exact point135slice41
  · exact point135slice42
  · exact point135slice43
  · exact point135slice44
  · exact point135slice45
  · exact point135slice46
  · exact point135slice47
  · exact point135slice48
  · exact point135slice49
  · exact point135slice50
  · exact point135slice51
  · exact point135slice52
  · exact point135slice53
  · exact point135slice54
  · exact point135slice55
  · exact point135slice56
  · exact point135slice57
  · exact point135slice58
  · exact point135slice59
  · exact point135slice60
  · exact point135slice61
  · exact point135slice62
  · exact point135slice63
  · exact point135slice64
  · exact point135slice65
  · exact point135slice66
  · exact point135slice67
  · exact point135slice68
  · exact point135slice69
  · exact point135slice70
  · exact point135slice71
  · exact point135slice72
  · exact point135slice73
  · exact point135slice74
  · exact point135slice75
  · exact point135slice76
  · exact point135slice77
  · exact point135slice78
  · exact point135slice79
  · exact point135slice80
  · exact point135slice81
  · exact point135slice82
  · exact point135slice83
  · exact point135slice84
  · exact point135slice85
  · exact point135slice86
  · exact point135slice87
  · exact point135slice88
  · exact point135slice89
  · exact point135slice90
  · exact point135slice91
  · exact point135slice92
  · exact point135slice93
  · exact point135slice94
  · exact point135slice95
  · exact point135slice96
  · exact point135slice97
  · exact point135slice98
  · exact point135slice99
  · exact point135slice100
  · exact point135slice101
  · exact point135slice102
  · exact point135slice103
  · exact point135slice104
  · exact point135slice105
  · exact point135slice106
  · exact point135slice107
  · exact point135slice108
  · exact point135slice109
  · exact point135slice110
  · exact point135slice111
  · exact point135slice112
  · exact point135slice113
  · exact point135slice114
  · exact point135slice115
  · exact point135slice116
  · exact point135slice117
  · exact point135slice118
  · exact point135slice119
  · exact point135slice120
  · exact point135slice121
  · exact point135slice122
  · exact point135slice123
  · exact point135slice124
  · exact point135slice125
  · exact point135slice126
  · exact point135slice127
  · exact point135slice128
  · exact point135slice129
  · exact point135slice130
  · exact point135slice131
  · exact point135slice132
  · exact point135slice133
  · exact point135slice134
  · exact point135slice135
  · exact point135slice136
  · exact point135slice137
  · exact point135slice138
  · exact point135slice139
  · exact point135slice140
  · exact point135slice141
  · exact point135slice142
  · exact point135slice143
  · exact point135slice144
  · exact point135slice145
  · exact point135slice146
  · exact point135slice147
  · exact point135slice148
  · exact point135slice149
  · exact point135slice150
  · exact point135slice151
  · exact point135slice152
  · exact point135slice153
  · exact point135slice154
  · exact point135slice155
  · exact point135slice156
  · exact point135slice157
  · exact point135slice158
  · exact point135slice159
  · exact point135slice160
  · exact point135slice161
  · exact point135slice162
  · exact point135slice163
  · exact point135slice164
  · exact point135slice165
  · exact point135slice166
  · exact point135slice167
  · exact point135slice168
  · exact point135slice169
  · exact point135slice170
  · exact point135slice171
  · exact point135slice172
  · exact point135slice173
  · exact point135slice174
  · exact point135slice175
  · exact point135slice176
  · exact point135slice177
  · exact point135slice178
  · exact point135slice179
  · exact point135slice180
  · exact point135slice181
  · exact point135slice182
  · exact point135slice183
  · exact point135slice184
  · exact point135slice185
  · exact point135slice186
  · exact point135slice187
  · exact point135slice188
  · exact point135slice189
  · exact point135slice190
  · exact point135slice191
  · exact point135slice192
  · exact point135slice193
  · exact point135slice194
  · exact point135slice195
  · exact point135slice196
  · exact point135slice197
  · exact point135slice198
  · exact point135slice199
  · exact point135slice200
  · exact point135slice201
  · exact point135slice202

set_option maxHeartbeats 1600000 in
public theorem point135 : stepCheck 1 2712 := by
  have hleft : L0Gen 1 * L0Rep 2712 = leftPerm135 := by
    change L0Gen 1 * evalWord L0Gen [0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3] = leftPerm135
    simp only [leftPerm135, p990, p153, p141, p53, p47, p20, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2712) * evalWord L1Gen (L0Factor 1 2712) = rightPerm135 := by
    change evalWord L0Gen [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 1, 0] * evalWord L1Gen [0, 0, 1, 1, 2, 1, 1, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1] = rightPerm135
    simp only [rightPerm135, p773, p405, p403, p252, p109, p90, p62, p59, p58, p40, p33, p30, p29, p28, p26, p25, p24, p23, p20, p18, p17, p16, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2712) x =
    (L0Rep (L0Act 1 2712) * evalWord L1Gen (L0Factor 1 2712)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap135_eq, ← rightMap135_eq]
  exact Residual1Cache.ofSlices point135_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
