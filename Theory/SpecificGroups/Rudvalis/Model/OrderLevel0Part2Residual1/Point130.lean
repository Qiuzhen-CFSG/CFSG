module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part1
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 130

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap130 (x : Nat) : Nat := force t67 (force t59 (t990 x))
private def leftPerm130 : Equiv.Perm (Fin 4060) := p67 * (p59 * (p990))
private theorem leftMap130_eq (x : Fin 4060) :
    leftMap130 x.val = (leftPerm130 x).val := (compose (t := fun x => force t67 (force t59 (t990 x))) (a := t67) (b := fun x => force t59 (t990 x)) (fun _ => rfl) c67 (compose (t := fun x => force t59 (t990 x)) (a := t59) (b := fun x => t990 x) (fun _ => rfl) c59 c990)) x

private def rightMap130 (x : Nat) : Nat := force t100 (force t53 (force t4 (force t4 (force t773 (force t403 (force t405 (t33 x)))))))
private def rightPerm130 : Equiv.Perm (Fin 4060) := p100 * (p53 * (p4 * (p4 * (p773 * (p403 * (p405 * (p33)))))))
private theorem rightMap130_eq (x : Fin 4060) :
    rightMap130 x.val = (rightPerm130 x).val := (compose (t := fun x => force t100 (force t53 (force t4 (force t4 (force t773 (force t403 (force t405 (t33 x)))))))) (a := t100) (b := fun x => force t53 (force t4 (force t4 (force t773 (force t403 (force t405 (t33 x))))))) (fun _ => rfl) c100 (compose (t := fun x => force t53 (force t4 (force t4 (force t773 (force t403 (force t405 (t33 x))))))) (a := t53) (b := fun x => force t4 (force t4 (force t773 (force t403 (force t405 (t33 x)))))) (fun _ => rfl) c53 (compose (t := fun x => force t4 (force t4 (force t773 (force t403 (force t405 (t33 x)))))) (a := t4) (b := fun x => force t4 (force t773 (force t403 (force t405 (t33 x))))) (fun _ => rfl) c4 (compose (t := fun x => force t4 (force t773 (force t403 (force t405 (t33 x))))) (a := t4) (b := fun x => force t773 (force t403 (force t405 (t33 x)))) (fun _ => rfl) c4 (compose (t := fun x => force t773 (force t403 (force t405 (t33 x)))) (a := t773) (b := fun x => force t403 (force t405 (t33 x))) (fun _ => rfl) c773 (compose (t := fun x => force t403 (force t405 (t33 x))) (a := t403) (b := fun x => force t405 (t33 x)) (fun _ => rfl) c403 (compose (t := fun x => force t405 (t33 x)) (a := t405) (b := fun x => t33 x) (fun _ => rfl) c405 c33))))))) x

set_option maxHeartbeats 1600000 in
private theorem point130slice0 : Residual1Cache.slice leftMap130 rightMap130 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice1 : Residual1Cache.slice leftMap130 rightMap130 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice2 : Residual1Cache.slice leftMap130 rightMap130 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice3 : Residual1Cache.slice leftMap130 rightMap130 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice4 : Residual1Cache.slice leftMap130 rightMap130 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice5 : Residual1Cache.slice leftMap130 rightMap130 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice6 : Residual1Cache.slice leftMap130 rightMap130 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice7 : Residual1Cache.slice leftMap130 rightMap130 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice8 : Residual1Cache.slice leftMap130 rightMap130 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice9 : Residual1Cache.slice leftMap130 rightMap130 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice10 : Residual1Cache.slice leftMap130 rightMap130 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice11 : Residual1Cache.slice leftMap130 rightMap130 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice12 : Residual1Cache.slice leftMap130 rightMap130 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice13 : Residual1Cache.slice leftMap130 rightMap130 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice14 : Residual1Cache.slice leftMap130 rightMap130 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice15 : Residual1Cache.slice leftMap130 rightMap130 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice16 : Residual1Cache.slice leftMap130 rightMap130 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice17 : Residual1Cache.slice leftMap130 rightMap130 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice18 : Residual1Cache.slice leftMap130 rightMap130 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice19 : Residual1Cache.slice leftMap130 rightMap130 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice20 : Residual1Cache.slice leftMap130 rightMap130 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice21 : Residual1Cache.slice leftMap130 rightMap130 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice22 : Residual1Cache.slice leftMap130 rightMap130 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice23 : Residual1Cache.slice leftMap130 rightMap130 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice24 : Residual1Cache.slice leftMap130 rightMap130 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice25 : Residual1Cache.slice leftMap130 rightMap130 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice26 : Residual1Cache.slice leftMap130 rightMap130 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice27 : Residual1Cache.slice leftMap130 rightMap130 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice28 : Residual1Cache.slice leftMap130 rightMap130 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice29 : Residual1Cache.slice leftMap130 rightMap130 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice30 : Residual1Cache.slice leftMap130 rightMap130 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice31 : Residual1Cache.slice leftMap130 rightMap130 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice32 : Residual1Cache.slice leftMap130 rightMap130 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice33 : Residual1Cache.slice leftMap130 rightMap130 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice34 : Residual1Cache.slice leftMap130 rightMap130 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice35 : Residual1Cache.slice leftMap130 rightMap130 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice36 : Residual1Cache.slice leftMap130 rightMap130 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice37 : Residual1Cache.slice leftMap130 rightMap130 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice38 : Residual1Cache.slice leftMap130 rightMap130 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice39 : Residual1Cache.slice leftMap130 rightMap130 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice40 : Residual1Cache.slice leftMap130 rightMap130 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice41 : Residual1Cache.slice leftMap130 rightMap130 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice42 : Residual1Cache.slice leftMap130 rightMap130 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice43 : Residual1Cache.slice leftMap130 rightMap130 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice44 : Residual1Cache.slice leftMap130 rightMap130 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice45 : Residual1Cache.slice leftMap130 rightMap130 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice46 : Residual1Cache.slice leftMap130 rightMap130 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice47 : Residual1Cache.slice leftMap130 rightMap130 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice48 : Residual1Cache.slice leftMap130 rightMap130 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice49 : Residual1Cache.slice leftMap130 rightMap130 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice50 : Residual1Cache.slice leftMap130 rightMap130 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice51 : Residual1Cache.slice leftMap130 rightMap130 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice52 : Residual1Cache.slice leftMap130 rightMap130 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice53 : Residual1Cache.slice leftMap130 rightMap130 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice54 : Residual1Cache.slice leftMap130 rightMap130 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice55 : Residual1Cache.slice leftMap130 rightMap130 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice56 : Residual1Cache.slice leftMap130 rightMap130 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice57 : Residual1Cache.slice leftMap130 rightMap130 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice58 : Residual1Cache.slice leftMap130 rightMap130 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice59 : Residual1Cache.slice leftMap130 rightMap130 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice60 : Residual1Cache.slice leftMap130 rightMap130 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice61 : Residual1Cache.slice leftMap130 rightMap130 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice62 : Residual1Cache.slice leftMap130 rightMap130 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice63 : Residual1Cache.slice leftMap130 rightMap130 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice64 : Residual1Cache.slice leftMap130 rightMap130 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice65 : Residual1Cache.slice leftMap130 rightMap130 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice66 : Residual1Cache.slice leftMap130 rightMap130 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice67 : Residual1Cache.slice leftMap130 rightMap130 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice68 : Residual1Cache.slice leftMap130 rightMap130 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice69 : Residual1Cache.slice leftMap130 rightMap130 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice70 : Residual1Cache.slice leftMap130 rightMap130 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice71 : Residual1Cache.slice leftMap130 rightMap130 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice72 : Residual1Cache.slice leftMap130 rightMap130 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice73 : Residual1Cache.slice leftMap130 rightMap130 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice74 : Residual1Cache.slice leftMap130 rightMap130 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice75 : Residual1Cache.slice leftMap130 rightMap130 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice76 : Residual1Cache.slice leftMap130 rightMap130 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice77 : Residual1Cache.slice leftMap130 rightMap130 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice78 : Residual1Cache.slice leftMap130 rightMap130 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice79 : Residual1Cache.slice leftMap130 rightMap130 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice80 : Residual1Cache.slice leftMap130 rightMap130 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice81 : Residual1Cache.slice leftMap130 rightMap130 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice82 : Residual1Cache.slice leftMap130 rightMap130 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice83 : Residual1Cache.slice leftMap130 rightMap130 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice84 : Residual1Cache.slice leftMap130 rightMap130 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice85 : Residual1Cache.slice leftMap130 rightMap130 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice86 : Residual1Cache.slice leftMap130 rightMap130 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice87 : Residual1Cache.slice leftMap130 rightMap130 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice88 : Residual1Cache.slice leftMap130 rightMap130 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice89 : Residual1Cache.slice leftMap130 rightMap130 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice90 : Residual1Cache.slice leftMap130 rightMap130 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice91 : Residual1Cache.slice leftMap130 rightMap130 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice92 : Residual1Cache.slice leftMap130 rightMap130 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice93 : Residual1Cache.slice leftMap130 rightMap130 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice94 : Residual1Cache.slice leftMap130 rightMap130 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice95 : Residual1Cache.slice leftMap130 rightMap130 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice96 : Residual1Cache.slice leftMap130 rightMap130 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice97 : Residual1Cache.slice leftMap130 rightMap130 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice98 : Residual1Cache.slice leftMap130 rightMap130 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice99 : Residual1Cache.slice leftMap130 rightMap130 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice100 : Residual1Cache.slice leftMap130 rightMap130 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice101 : Residual1Cache.slice leftMap130 rightMap130 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice102 : Residual1Cache.slice leftMap130 rightMap130 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice103 : Residual1Cache.slice leftMap130 rightMap130 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice104 : Residual1Cache.slice leftMap130 rightMap130 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice105 : Residual1Cache.slice leftMap130 rightMap130 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice106 : Residual1Cache.slice leftMap130 rightMap130 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice107 : Residual1Cache.slice leftMap130 rightMap130 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice108 : Residual1Cache.slice leftMap130 rightMap130 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice109 : Residual1Cache.slice leftMap130 rightMap130 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice110 : Residual1Cache.slice leftMap130 rightMap130 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice111 : Residual1Cache.slice leftMap130 rightMap130 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice112 : Residual1Cache.slice leftMap130 rightMap130 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice113 : Residual1Cache.slice leftMap130 rightMap130 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice114 : Residual1Cache.slice leftMap130 rightMap130 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice115 : Residual1Cache.slice leftMap130 rightMap130 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice116 : Residual1Cache.slice leftMap130 rightMap130 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice117 : Residual1Cache.slice leftMap130 rightMap130 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice118 : Residual1Cache.slice leftMap130 rightMap130 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice119 : Residual1Cache.slice leftMap130 rightMap130 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice120 : Residual1Cache.slice leftMap130 rightMap130 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice121 : Residual1Cache.slice leftMap130 rightMap130 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice122 : Residual1Cache.slice leftMap130 rightMap130 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice123 : Residual1Cache.slice leftMap130 rightMap130 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice124 : Residual1Cache.slice leftMap130 rightMap130 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice125 : Residual1Cache.slice leftMap130 rightMap130 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice126 : Residual1Cache.slice leftMap130 rightMap130 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice127 : Residual1Cache.slice leftMap130 rightMap130 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice128 : Residual1Cache.slice leftMap130 rightMap130 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice129 : Residual1Cache.slice leftMap130 rightMap130 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice130 : Residual1Cache.slice leftMap130 rightMap130 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice131 : Residual1Cache.slice leftMap130 rightMap130 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice132 : Residual1Cache.slice leftMap130 rightMap130 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice133 : Residual1Cache.slice leftMap130 rightMap130 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice134 : Residual1Cache.slice leftMap130 rightMap130 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice135 : Residual1Cache.slice leftMap130 rightMap130 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice136 : Residual1Cache.slice leftMap130 rightMap130 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice137 : Residual1Cache.slice leftMap130 rightMap130 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice138 : Residual1Cache.slice leftMap130 rightMap130 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice139 : Residual1Cache.slice leftMap130 rightMap130 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice140 : Residual1Cache.slice leftMap130 rightMap130 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice141 : Residual1Cache.slice leftMap130 rightMap130 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice142 : Residual1Cache.slice leftMap130 rightMap130 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice143 : Residual1Cache.slice leftMap130 rightMap130 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice144 : Residual1Cache.slice leftMap130 rightMap130 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice145 : Residual1Cache.slice leftMap130 rightMap130 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice146 : Residual1Cache.slice leftMap130 rightMap130 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice147 : Residual1Cache.slice leftMap130 rightMap130 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice148 : Residual1Cache.slice leftMap130 rightMap130 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice149 : Residual1Cache.slice leftMap130 rightMap130 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice150 : Residual1Cache.slice leftMap130 rightMap130 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice151 : Residual1Cache.slice leftMap130 rightMap130 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice152 : Residual1Cache.slice leftMap130 rightMap130 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice153 : Residual1Cache.slice leftMap130 rightMap130 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice154 : Residual1Cache.slice leftMap130 rightMap130 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice155 : Residual1Cache.slice leftMap130 rightMap130 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice156 : Residual1Cache.slice leftMap130 rightMap130 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice157 : Residual1Cache.slice leftMap130 rightMap130 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice158 : Residual1Cache.slice leftMap130 rightMap130 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice159 : Residual1Cache.slice leftMap130 rightMap130 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice160 : Residual1Cache.slice leftMap130 rightMap130 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice161 : Residual1Cache.slice leftMap130 rightMap130 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice162 : Residual1Cache.slice leftMap130 rightMap130 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice163 : Residual1Cache.slice leftMap130 rightMap130 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice164 : Residual1Cache.slice leftMap130 rightMap130 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice165 : Residual1Cache.slice leftMap130 rightMap130 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice166 : Residual1Cache.slice leftMap130 rightMap130 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice167 : Residual1Cache.slice leftMap130 rightMap130 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice168 : Residual1Cache.slice leftMap130 rightMap130 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice169 : Residual1Cache.slice leftMap130 rightMap130 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice170 : Residual1Cache.slice leftMap130 rightMap130 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice171 : Residual1Cache.slice leftMap130 rightMap130 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice172 : Residual1Cache.slice leftMap130 rightMap130 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice173 : Residual1Cache.slice leftMap130 rightMap130 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice174 : Residual1Cache.slice leftMap130 rightMap130 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice175 : Residual1Cache.slice leftMap130 rightMap130 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice176 : Residual1Cache.slice leftMap130 rightMap130 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice177 : Residual1Cache.slice leftMap130 rightMap130 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice178 : Residual1Cache.slice leftMap130 rightMap130 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice179 : Residual1Cache.slice leftMap130 rightMap130 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice180 : Residual1Cache.slice leftMap130 rightMap130 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice181 : Residual1Cache.slice leftMap130 rightMap130 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice182 : Residual1Cache.slice leftMap130 rightMap130 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice183 : Residual1Cache.slice leftMap130 rightMap130 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice184 : Residual1Cache.slice leftMap130 rightMap130 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice185 : Residual1Cache.slice leftMap130 rightMap130 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice186 : Residual1Cache.slice leftMap130 rightMap130 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice187 : Residual1Cache.slice leftMap130 rightMap130 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice188 : Residual1Cache.slice leftMap130 rightMap130 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice189 : Residual1Cache.slice leftMap130 rightMap130 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice190 : Residual1Cache.slice leftMap130 rightMap130 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice191 : Residual1Cache.slice leftMap130 rightMap130 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice192 : Residual1Cache.slice leftMap130 rightMap130 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice193 : Residual1Cache.slice leftMap130 rightMap130 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice194 : Residual1Cache.slice leftMap130 rightMap130 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice195 : Residual1Cache.slice leftMap130 rightMap130 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice196 : Residual1Cache.slice leftMap130 rightMap130 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice197 : Residual1Cache.slice leftMap130 rightMap130 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice198 : Residual1Cache.slice leftMap130 rightMap130 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice199 : Residual1Cache.slice leftMap130 rightMap130 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice200 : Residual1Cache.slice leftMap130 rightMap130 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice201 : Residual1Cache.slice leftMap130 rightMap130 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point130slice202 : Residual1Cache.slice leftMap130 rightMap130 202 = true := by
  decide +kernel

private theorem point130_slices : ∀ c, Residual1Cache.slice leftMap130 rightMap130 c = true := by
  intro c
  fin_cases c
  · exact point130slice0
  · exact point130slice1
  · exact point130slice2
  · exact point130slice3
  · exact point130slice4
  · exact point130slice5
  · exact point130slice6
  · exact point130slice7
  · exact point130slice8
  · exact point130slice9
  · exact point130slice10
  · exact point130slice11
  · exact point130slice12
  · exact point130slice13
  · exact point130slice14
  · exact point130slice15
  · exact point130slice16
  · exact point130slice17
  · exact point130slice18
  · exact point130slice19
  · exact point130slice20
  · exact point130slice21
  · exact point130slice22
  · exact point130slice23
  · exact point130slice24
  · exact point130slice25
  · exact point130slice26
  · exact point130slice27
  · exact point130slice28
  · exact point130slice29
  · exact point130slice30
  · exact point130slice31
  · exact point130slice32
  · exact point130slice33
  · exact point130slice34
  · exact point130slice35
  · exact point130slice36
  · exact point130slice37
  · exact point130slice38
  · exact point130slice39
  · exact point130slice40
  · exact point130slice41
  · exact point130slice42
  · exact point130slice43
  · exact point130slice44
  · exact point130slice45
  · exact point130slice46
  · exact point130slice47
  · exact point130slice48
  · exact point130slice49
  · exact point130slice50
  · exact point130slice51
  · exact point130slice52
  · exact point130slice53
  · exact point130slice54
  · exact point130slice55
  · exact point130slice56
  · exact point130slice57
  · exact point130slice58
  · exact point130slice59
  · exact point130slice60
  · exact point130slice61
  · exact point130slice62
  · exact point130slice63
  · exact point130slice64
  · exact point130slice65
  · exact point130slice66
  · exact point130slice67
  · exact point130slice68
  · exact point130slice69
  · exact point130slice70
  · exact point130slice71
  · exact point130slice72
  · exact point130slice73
  · exact point130slice74
  · exact point130slice75
  · exact point130slice76
  · exact point130slice77
  · exact point130slice78
  · exact point130slice79
  · exact point130slice80
  · exact point130slice81
  · exact point130slice82
  · exact point130slice83
  · exact point130slice84
  · exact point130slice85
  · exact point130slice86
  · exact point130slice87
  · exact point130slice88
  · exact point130slice89
  · exact point130slice90
  · exact point130slice91
  · exact point130slice92
  · exact point130slice93
  · exact point130slice94
  · exact point130slice95
  · exact point130slice96
  · exact point130slice97
  · exact point130slice98
  · exact point130slice99
  · exact point130slice100
  · exact point130slice101
  · exact point130slice102
  · exact point130slice103
  · exact point130slice104
  · exact point130slice105
  · exact point130slice106
  · exact point130slice107
  · exact point130slice108
  · exact point130slice109
  · exact point130slice110
  · exact point130slice111
  · exact point130slice112
  · exact point130slice113
  · exact point130slice114
  · exact point130slice115
  · exact point130slice116
  · exact point130slice117
  · exact point130slice118
  · exact point130slice119
  · exact point130slice120
  · exact point130slice121
  · exact point130slice122
  · exact point130slice123
  · exact point130slice124
  · exact point130slice125
  · exact point130slice126
  · exact point130slice127
  · exact point130slice128
  · exact point130slice129
  · exact point130slice130
  · exact point130slice131
  · exact point130slice132
  · exact point130slice133
  · exact point130slice134
  · exact point130slice135
  · exact point130slice136
  · exact point130slice137
  · exact point130slice138
  · exact point130slice139
  · exact point130slice140
  · exact point130slice141
  · exact point130slice142
  · exact point130slice143
  · exact point130slice144
  · exact point130slice145
  · exact point130slice146
  · exact point130slice147
  · exact point130slice148
  · exact point130slice149
  · exact point130slice150
  · exact point130slice151
  · exact point130slice152
  · exact point130slice153
  · exact point130slice154
  · exact point130slice155
  · exact point130slice156
  · exact point130slice157
  · exact point130slice158
  · exact point130slice159
  · exact point130slice160
  · exact point130slice161
  · exact point130slice162
  · exact point130slice163
  · exact point130slice164
  · exact point130slice165
  · exact point130slice166
  · exact point130slice167
  · exact point130slice168
  · exact point130slice169
  · exact point130slice170
  · exact point130slice171
  · exact point130slice172
  · exact point130slice173
  · exact point130slice174
  · exact point130slice175
  · exact point130slice176
  · exact point130slice177
  · exact point130slice178
  · exact point130slice179
  · exact point130slice180
  · exact point130slice181
  · exact point130slice182
  · exact point130slice183
  · exact point130slice184
  · exact point130slice185
  · exact point130slice186
  · exact point130slice187
  · exact point130slice188
  · exact point130slice189
  · exact point130slice190
  · exact point130slice191
  · exact point130slice192
  · exact point130slice193
  · exact point130slice194
  · exact point130slice195
  · exact point130slice196
  · exact point130slice197
  · exact point130slice198
  · exact point130slice199
  · exact point130slice200
  · exact point130slice201
  · exact point130slice202

set_option maxHeartbeats 1600000 in
public theorem point130 : stepCheck 0 2714 := by
  have hleft : L0Gen 0 * L0Rep 2714 = leftPerm130 := by
    change L0Gen 0 * evalWord L0Gen [1, 0, 3, 0, 1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3] = leftPerm130
    simp only [leftPerm130, p990, p153, p67, p59, p47, p20, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2714) * evalWord L1Gen (L0Factor 0 2714) = rightPerm130 := by
    change evalWord L0Gen [3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0] * evalWord L1Gen [0, 0, 1, 1, 2, 1, 1, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3, 0, 1] = rightPerm130
    simp only [rightPerm130, p773, p405, p403, p109, p100, p90, p58, p53, p40, p33, p30, p29, p28, p27, p26, p25, p24, p23, p18, p17, p16, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2714) x =
    (L0Rep (L0Act 0 2714) * evalWord L1Gen (L0Factor 0 2714)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap130_eq, ← rightMap130_eq]
  exact Residual1Cache.ofSlices point130_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
