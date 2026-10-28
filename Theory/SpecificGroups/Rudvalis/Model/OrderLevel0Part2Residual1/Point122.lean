module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level08Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 122

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap122 (x : Nat) : Nat := force t11 (force t59 (force t140 (force t0 (t48 x))))
private def leftPerm122 : Equiv.Perm (Fin 4060) := p11 * (p59 * (p140 * (p0 * (p48))))
private theorem leftMap122_eq (x : Fin 4060) :
    leftMap122 x.val = (leftPerm122 x).val := (compose (t := fun x => force t11 (force t59 (force t140 (force t0 (t48 x))))) (a := t11) (b := fun x => force t59 (force t140 (force t0 (t48 x)))) (fun _ => rfl) c11 (compose (t := fun x => force t59 (force t140 (force t0 (t48 x)))) (a := t59) (b := fun x => force t140 (force t0 (t48 x))) (fun _ => rfl) c59 (compose (t := fun x => force t140 (force t0 (t48 x))) (a := t140) (b := fun x => force t0 (t48 x)) (fun _ => rfl) c140 (compose (t := fun x => force t0 (t48 x)) (a := t0) (b := fun x => t48 x) (fun _ => rfl) c0 c48)))) x

private def rightMap122 (x : Nat) : Nat := force t175 (force t50 (force t732 (force t4 (force t171 (force t13 (force t105 (force t32 (t648 x))))))))
private def rightPerm122 : Equiv.Perm (Fin 4060) := p175 * (p50 * (p732 * (p4 * (p171 * (p13 * (p105 * (p32 * (p648))))))))
private theorem rightMap122_eq (x : Fin 4060) :
    rightMap122 x.val = (rightPerm122 x).val := (compose (t := fun x => force t175 (force t50 (force t732 (force t4 (force t171 (force t13 (force t105 (force t32 (t648 x))))))))) (a := t175) (b := fun x => force t50 (force t732 (force t4 (force t171 (force t13 (force t105 (force t32 (t648 x)))))))) (fun _ => rfl) c175 (compose (t := fun x => force t50 (force t732 (force t4 (force t171 (force t13 (force t105 (force t32 (t648 x)))))))) (a := t50) (b := fun x => force t732 (force t4 (force t171 (force t13 (force t105 (force t32 (t648 x))))))) (fun _ => rfl) c50 (compose (t := fun x => force t732 (force t4 (force t171 (force t13 (force t105 (force t32 (t648 x))))))) (a := t732) (b := fun x => force t4 (force t171 (force t13 (force t105 (force t32 (t648 x)))))) (fun _ => rfl) c732 (compose (t := fun x => force t4 (force t171 (force t13 (force t105 (force t32 (t648 x)))))) (a := t4) (b := fun x => force t171 (force t13 (force t105 (force t32 (t648 x))))) (fun _ => rfl) c4 (compose (t := fun x => force t171 (force t13 (force t105 (force t32 (t648 x))))) (a := t171) (b := fun x => force t13 (force t105 (force t32 (t648 x)))) (fun _ => rfl) c171 (compose (t := fun x => force t13 (force t105 (force t32 (t648 x)))) (a := t13) (b := fun x => force t105 (force t32 (t648 x))) (fun _ => rfl) c13 (compose (t := fun x => force t105 (force t32 (t648 x))) (a := t105) (b := fun x => force t32 (t648 x)) (fun _ => rfl) c105 (compose (t := fun x => force t32 (t648 x)) (a := t32) (b := fun x => t648 x) (fun _ => rfl) c32 c648)))))))) x

set_option maxHeartbeats 1600000 in
private theorem point122slice0 : Residual1Cache.slice leftMap122 rightMap122 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice1 : Residual1Cache.slice leftMap122 rightMap122 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice2 : Residual1Cache.slice leftMap122 rightMap122 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice3 : Residual1Cache.slice leftMap122 rightMap122 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice4 : Residual1Cache.slice leftMap122 rightMap122 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice5 : Residual1Cache.slice leftMap122 rightMap122 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice6 : Residual1Cache.slice leftMap122 rightMap122 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice7 : Residual1Cache.slice leftMap122 rightMap122 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice8 : Residual1Cache.slice leftMap122 rightMap122 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice9 : Residual1Cache.slice leftMap122 rightMap122 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice10 : Residual1Cache.slice leftMap122 rightMap122 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice11 : Residual1Cache.slice leftMap122 rightMap122 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice12 : Residual1Cache.slice leftMap122 rightMap122 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice13 : Residual1Cache.slice leftMap122 rightMap122 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice14 : Residual1Cache.slice leftMap122 rightMap122 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice15 : Residual1Cache.slice leftMap122 rightMap122 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice16 : Residual1Cache.slice leftMap122 rightMap122 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice17 : Residual1Cache.slice leftMap122 rightMap122 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice18 : Residual1Cache.slice leftMap122 rightMap122 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice19 : Residual1Cache.slice leftMap122 rightMap122 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice20 : Residual1Cache.slice leftMap122 rightMap122 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice21 : Residual1Cache.slice leftMap122 rightMap122 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice22 : Residual1Cache.slice leftMap122 rightMap122 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice23 : Residual1Cache.slice leftMap122 rightMap122 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice24 : Residual1Cache.slice leftMap122 rightMap122 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice25 : Residual1Cache.slice leftMap122 rightMap122 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice26 : Residual1Cache.slice leftMap122 rightMap122 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice27 : Residual1Cache.slice leftMap122 rightMap122 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice28 : Residual1Cache.slice leftMap122 rightMap122 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice29 : Residual1Cache.slice leftMap122 rightMap122 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice30 : Residual1Cache.slice leftMap122 rightMap122 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice31 : Residual1Cache.slice leftMap122 rightMap122 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice32 : Residual1Cache.slice leftMap122 rightMap122 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice33 : Residual1Cache.slice leftMap122 rightMap122 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice34 : Residual1Cache.slice leftMap122 rightMap122 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice35 : Residual1Cache.slice leftMap122 rightMap122 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice36 : Residual1Cache.slice leftMap122 rightMap122 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice37 : Residual1Cache.slice leftMap122 rightMap122 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice38 : Residual1Cache.slice leftMap122 rightMap122 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice39 : Residual1Cache.slice leftMap122 rightMap122 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice40 : Residual1Cache.slice leftMap122 rightMap122 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice41 : Residual1Cache.slice leftMap122 rightMap122 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice42 : Residual1Cache.slice leftMap122 rightMap122 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice43 : Residual1Cache.slice leftMap122 rightMap122 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice44 : Residual1Cache.slice leftMap122 rightMap122 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice45 : Residual1Cache.slice leftMap122 rightMap122 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice46 : Residual1Cache.slice leftMap122 rightMap122 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice47 : Residual1Cache.slice leftMap122 rightMap122 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice48 : Residual1Cache.slice leftMap122 rightMap122 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice49 : Residual1Cache.slice leftMap122 rightMap122 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice50 : Residual1Cache.slice leftMap122 rightMap122 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice51 : Residual1Cache.slice leftMap122 rightMap122 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice52 : Residual1Cache.slice leftMap122 rightMap122 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice53 : Residual1Cache.slice leftMap122 rightMap122 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice54 : Residual1Cache.slice leftMap122 rightMap122 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice55 : Residual1Cache.slice leftMap122 rightMap122 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice56 : Residual1Cache.slice leftMap122 rightMap122 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice57 : Residual1Cache.slice leftMap122 rightMap122 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice58 : Residual1Cache.slice leftMap122 rightMap122 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice59 : Residual1Cache.slice leftMap122 rightMap122 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice60 : Residual1Cache.slice leftMap122 rightMap122 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice61 : Residual1Cache.slice leftMap122 rightMap122 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice62 : Residual1Cache.slice leftMap122 rightMap122 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice63 : Residual1Cache.slice leftMap122 rightMap122 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice64 : Residual1Cache.slice leftMap122 rightMap122 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice65 : Residual1Cache.slice leftMap122 rightMap122 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice66 : Residual1Cache.slice leftMap122 rightMap122 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice67 : Residual1Cache.slice leftMap122 rightMap122 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice68 : Residual1Cache.slice leftMap122 rightMap122 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice69 : Residual1Cache.slice leftMap122 rightMap122 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice70 : Residual1Cache.slice leftMap122 rightMap122 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice71 : Residual1Cache.slice leftMap122 rightMap122 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice72 : Residual1Cache.slice leftMap122 rightMap122 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice73 : Residual1Cache.slice leftMap122 rightMap122 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice74 : Residual1Cache.slice leftMap122 rightMap122 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice75 : Residual1Cache.slice leftMap122 rightMap122 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice76 : Residual1Cache.slice leftMap122 rightMap122 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice77 : Residual1Cache.slice leftMap122 rightMap122 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice78 : Residual1Cache.slice leftMap122 rightMap122 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice79 : Residual1Cache.slice leftMap122 rightMap122 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice80 : Residual1Cache.slice leftMap122 rightMap122 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice81 : Residual1Cache.slice leftMap122 rightMap122 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice82 : Residual1Cache.slice leftMap122 rightMap122 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice83 : Residual1Cache.slice leftMap122 rightMap122 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice84 : Residual1Cache.slice leftMap122 rightMap122 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice85 : Residual1Cache.slice leftMap122 rightMap122 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice86 : Residual1Cache.slice leftMap122 rightMap122 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice87 : Residual1Cache.slice leftMap122 rightMap122 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice88 : Residual1Cache.slice leftMap122 rightMap122 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice89 : Residual1Cache.slice leftMap122 rightMap122 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice90 : Residual1Cache.slice leftMap122 rightMap122 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice91 : Residual1Cache.slice leftMap122 rightMap122 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice92 : Residual1Cache.slice leftMap122 rightMap122 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice93 : Residual1Cache.slice leftMap122 rightMap122 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice94 : Residual1Cache.slice leftMap122 rightMap122 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice95 : Residual1Cache.slice leftMap122 rightMap122 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice96 : Residual1Cache.slice leftMap122 rightMap122 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice97 : Residual1Cache.slice leftMap122 rightMap122 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice98 : Residual1Cache.slice leftMap122 rightMap122 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice99 : Residual1Cache.slice leftMap122 rightMap122 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice100 : Residual1Cache.slice leftMap122 rightMap122 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice101 : Residual1Cache.slice leftMap122 rightMap122 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice102 : Residual1Cache.slice leftMap122 rightMap122 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice103 : Residual1Cache.slice leftMap122 rightMap122 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice104 : Residual1Cache.slice leftMap122 rightMap122 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice105 : Residual1Cache.slice leftMap122 rightMap122 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice106 : Residual1Cache.slice leftMap122 rightMap122 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice107 : Residual1Cache.slice leftMap122 rightMap122 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice108 : Residual1Cache.slice leftMap122 rightMap122 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice109 : Residual1Cache.slice leftMap122 rightMap122 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice110 : Residual1Cache.slice leftMap122 rightMap122 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice111 : Residual1Cache.slice leftMap122 rightMap122 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice112 : Residual1Cache.slice leftMap122 rightMap122 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice113 : Residual1Cache.slice leftMap122 rightMap122 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice114 : Residual1Cache.slice leftMap122 rightMap122 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice115 : Residual1Cache.slice leftMap122 rightMap122 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice116 : Residual1Cache.slice leftMap122 rightMap122 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice117 : Residual1Cache.slice leftMap122 rightMap122 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice118 : Residual1Cache.slice leftMap122 rightMap122 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice119 : Residual1Cache.slice leftMap122 rightMap122 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice120 : Residual1Cache.slice leftMap122 rightMap122 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice121 : Residual1Cache.slice leftMap122 rightMap122 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice122 : Residual1Cache.slice leftMap122 rightMap122 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice123 : Residual1Cache.slice leftMap122 rightMap122 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice124 : Residual1Cache.slice leftMap122 rightMap122 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice125 : Residual1Cache.slice leftMap122 rightMap122 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice126 : Residual1Cache.slice leftMap122 rightMap122 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice127 : Residual1Cache.slice leftMap122 rightMap122 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice128 : Residual1Cache.slice leftMap122 rightMap122 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice129 : Residual1Cache.slice leftMap122 rightMap122 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice130 : Residual1Cache.slice leftMap122 rightMap122 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice131 : Residual1Cache.slice leftMap122 rightMap122 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice132 : Residual1Cache.slice leftMap122 rightMap122 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice133 : Residual1Cache.slice leftMap122 rightMap122 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice134 : Residual1Cache.slice leftMap122 rightMap122 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice135 : Residual1Cache.slice leftMap122 rightMap122 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice136 : Residual1Cache.slice leftMap122 rightMap122 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice137 : Residual1Cache.slice leftMap122 rightMap122 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice138 : Residual1Cache.slice leftMap122 rightMap122 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice139 : Residual1Cache.slice leftMap122 rightMap122 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice140 : Residual1Cache.slice leftMap122 rightMap122 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice141 : Residual1Cache.slice leftMap122 rightMap122 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice142 : Residual1Cache.slice leftMap122 rightMap122 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice143 : Residual1Cache.slice leftMap122 rightMap122 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice144 : Residual1Cache.slice leftMap122 rightMap122 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice145 : Residual1Cache.slice leftMap122 rightMap122 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice146 : Residual1Cache.slice leftMap122 rightMap122 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice147 : Residual1Cache.slice leftMap122 rightMap122 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice148 : Residual1Cache.slice leftMap122 rightMap122 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice149 : Residual1Cache.slice leftMap122 rightMap122 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice150 : Residual1Cache.slice leftMap122 rightMap122 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice151 : Residual1Cache.slice leftMap122 rightMap122 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice152 : Residual1Cache.slice leftMap122 rightMap122 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice153 : Residual1Cache.slice leftMap122 rightMap122 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice154 : Residual1Cache.slice leftMap122 rightMap122 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice155 : Residual1Cache.slice leftMap122 rightMap122 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice156 : Residual1Cache.slice leftMap122 rightMap122 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice157 : Residual1Cache.slice leftMap122 rightMap122 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice158 : Residual1Cache.slice leftMap122 rightMap122 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice159 : Residual1Cache.slice leftMap122 rightMap122 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice160 : Residual1Cache.slice leftMap122 rightMap122 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice161 : Residual1Cache.slice leftMap122 rightMap122 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice162 : Residual1Cache.slice leftMap122 rightMap122 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice163 : Residual1Cache.slice leftMap122 rightMap122 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice164 : Residual1Cache.slice leftMap122 rightMap122 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice165 : Residual1Cache.slice leftMap122 rightMap122 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice166 : Residual1Cache.slice leftMap122 rightMap122 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice167 : Residual1Cache.slice leftMap122 rightMap122 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice168 : Residual1Cache.slice leftMap122 rightMap122 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice169 : Residual1Cache.slice leftMap122 rightMap122 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice170 : Residual1Cache.slice leftMap122 rightMap122 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice171 : Residual1Cache.slice leftMap122 rightMap122 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice172 : Residual1Cache.slice leftMap122 rightMap122 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice173 : Residual1Cache.slice leftMap122 rightMap122 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice174 : Residual1Cache.slice leftMap122 rightMap122 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice175 : Residual1Cache.slice leftMap122 rightMap122 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice176 : Residual1Cache.slice leftMap122 rightMap122 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice177 : Residual1Cache.slice leftMap122 rightMap122 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice178 : Residual1Cache.slice leftMap122 rightMap122 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice179 : Residual1Cache.slice leftMap122 rightMap122 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice180 : Residual1Cache.slice leftMap122 rightMap122 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice181 : Residual1Cache.slice leftMap122 rightMap122 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice182 : Residual1Cache.slice leftMap122 rightMap122 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice183 : Residual1Cache.slice leftMap122 rightMap122 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice184 : Residual1Cache.slice leftMap122 rightMap122 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice185 : Residual1Cache.slice leftMap122 rightMap122 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice186 : Residual1Cache.slice leftMap122 rightMap122 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice187 : Residual1Cache.slice leftMap122 rightMap122 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice188 : Residual1Cache.slice leftMap122 rightMap122 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice189 : Residual1Cache.slice leftMap122 rightMap122 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice190 : Residual1Cache.slice leftMap122 rightMap122 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice191 : Residual1Cache.slice leftMap122 rightMap122 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice192 : Residual1Cache.slice leftMap122 rightMap122 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice193 : Residual1Cache.slice leftMap122 rightMap122 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice194 : Residual1Cache.slice leftMap122 rightMap122 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice195 : Residual1Cache.slice leftMap122 rightMap122 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice196 : Residual1Cache.slice leftMap122 rightMap122 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice197 : Residual1Cache.slice leftMap122 rightMap122 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice198 : Residual1Cache.slice leftMap122 rightMap122 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice199 : Residual1Cache.slice leftMap122 rightMap122 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice200 : Residual1Cache.slice leftMap122 rightMap122 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice201 : Residual1Cache.slice leftMap122 rightMap122 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point122slice202 : Residual1Cache.slice leftMap122 rightMap122 202 = true := by
  decide +kernel

private theorem point122_slices : ∀ c, Residual1Cache.slice leftMap122 rightMap122 c = true := by
  intro c
  fin_cases c
  · exact point122slice0
  · exact point122slice1
  · exact point122slice2
  · exact point122slice3
  · exact point122slice4
  · exact point122slice5
  · exact point122slice6
  · exact point122slice7
  · exact point122slice8
  · exact point122slice9
  · exact point122slice10
  · exact point122slice11
  · exact point122slice12
  · exact point122slice13
  · exact point122slice14
  · exact point122slice15
  · exact point122slice16
  · exact point122slice17
  · exact point122slice18
  · exact point122slice19
  · exact point122slice20
  · exact point122slice21
  · exact point122slice22
  · exact point122slice23
  · exact point122slice24
  · exact point122slice25
  · exact point122slice26
  · exact point122slice27
  · exact point122slice28
  · exact point122slice29
  · exact point122slice30
  · exact point122slice31
  · exact point122slice32
  · exact point122slice33
  · exact point122slice34
  · exact point122slice35
  · exact point122slice36
  · exact point122slice37
  · exact point122slice38
  · exact point122slice39
  · exact point122slice40
  · exact point122slice41
  · exact point122slice42
  · exact point122slice43
  · exact point122slice44
  · exact point122slice45
  · exact point122slice46
  · exact point122slice47
  · exact point122slice48
  · exact point122slice49
  · exact point122slice50
  · exact point122slice51
  · exact point122slice52
  · exact point122slice53
  · exact point122slice54
  · exact point122slice55
  · exact point122slice56
  · exact point122slice57
  · exact point122slice58
  · exact point122slice59
  · exact point122slice60
  · exact point122slice61
  · exact point122slice62
  · exact point122slice63
  · exact point122slice64
  · exact point122slice65
  · exact point122slice66
  · exact point122slice67
  · exact point122slice68
  · exact point122slice69
  · exact point122slice70
  · exact point122slice71
  · exact point122slice72
  · exact point122slice73
  · exact point122slice74
  · exact point122slice75
  · exact point122slice76
  · exact point122slice77
  · exact point122slice78
  · exact point122slice79
  · exact point122slice80
  · exact point122slice81
  · exact point122slice82
  · exact point122slice83
  · exact point122slice84
  · exact point122slice85
  · exact point122slice86
  · exact point122slice87
  · exact point122slice88
  · exact point122slice89
  · exact point122slice90
  · exact point122slice91
  · exact point122slice92
  · exact point122slice93
  · exact point122slice94
  · exact point122slice95
  · exact point122slice96
  · exact point122slice97
  · exact point122slice98
  · exact point122slice99
  · exact point122slice100
  · exact point122slice101
  · exact point122slice102
  · exact point122slice103
  · exact point122slice104
  · exact point122slice105
  · exact point122slice106
  · exact point122slice107
  · exact point122slice108
  · exact point122slice109
  · exact point122slice110
  · exact point122slice111
  · exact point122slice112
  · exact point122slice113
  · exact point122slice114
  · exact point122slice115
  · exact point122slice116
  · exact point122slice117
  · exact point122slice118
  · exact point122slice119
  · exact point122slice120
  · exact point122slice121
  · exact point122slice122
  · exact point122slice123
  · exact point122slice124
  · exact point122slice125
  · exact point122slice126
  · exact point122slice127
  · exact point122slice128
  · exact point122slice129
  · exact point122slice130
  · exact point122slice131
  · exact point122slice132
  · exact point122slice133
  · exact point122slice134
  · exact point122slice135
  · exact point122slice136
  · exact point122slice137
  · exact point122slice138
  · exact point122slice139
  · exact point122slice140
  · exact point122slice141
  · exact point122slice142
  · exact point122slice143
  · exact point122slice144
  · exact point122slice145
  · exact point122slice146
  · exact point122slice147
  · exact point122slice148
  · exact point122slice149
  · exact point122slice150
  · exact point122slice151
  · exact point122slice152
  · exact point122slice153
  · exact point122slice154
  · exact point122slice155
  · exact point122slice156
  · exact point122slice157
  · exact point122slice158
  · exact point122slice159
  · exact point122slice160
  · exact point122slice161
  · exact point122slice162
  · exact point122slice163
  · exact point122slice164
  · exact point122slice165
  · exact point122slice166
  · exact point122slice167
  · exact point122slice168
  · exact point122slice169
  · exact point122slice170
  · exact point122slice171
  · exact point122slice172
  · exact point122slice173
  · exact point122slice174
  · exact point122slice175
  · exact point122slice176
  · exact point122slice177
  · exact point122slice178
  · exact point122slice179
  · exact point122slice180
  · exact point122slice181
  · exact point122slice182
  · exact point122slice183
  · exact point122slice184
  · exact point122slice185
  · exact point122slice186
  · exact point122slice187
  · exact point122slice188
  · exact point122slice189
  · exact point122slice190
  · exact point122slice191
  · exact point122slice192
  · exact point122slice193
  · exact point122slice194
  · exact point122slice195
  · exact point122slice196
  · exact point122slice197
  · exact point122slice198
  · exact point122slice199
  · exact point122slice200
  · exact point122slice201
  · exact point122slice202

set_option maxHeartbeats 1600000 in
public theorem point122 : stepCheck 1 2573 := by
  have hleft : L0Gen 1 * L0Rep 2573 = leftPerm122 := by
    change L0Gen 1 * evalWord L0Gen [0, 3, 0, 1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 1, 1] = leftPerm122
    simp only [leftPerm122, p140, p59, p48, p47, p20, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2573) * evalWord L1Gen (L0Factor 1 2573) = rightPerm122 := by
    change evalWord L0Gen [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] * evalWord L1Gen [0, 0, 1, 0, 0, 3, 0, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm122
    simp only [rightPerm122, p732, p731, p648, p175, p171, p105, p73, p69, p50, p45, p41, p35, p34, p32, p31, p26, p23, p22, p21, p20, p19, p18, p17, p16, p15, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2573) x =
    (L0Rep (L0Act 1 2573) * evalWord L1Gen (L0Factor 1 2573)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap122_eq, ← rightMap122_eq]
  exact Residual1Cache.ofSlices point122_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
