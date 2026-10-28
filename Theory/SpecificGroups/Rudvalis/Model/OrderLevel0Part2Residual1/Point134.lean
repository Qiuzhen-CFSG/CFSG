module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level12Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level14Part2
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 134

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap134 (x : Nat) : Nat := force t797 (t153 x)
private def leftPerm134 : Equiv.Perm (Fin 4060) := p797 * (p153)
private theorem leftMap134_eq (x : Fin 4060) :
    leftMap134 x.val = (leftPerm134 x).val := (compose (t := fun x => force t797 (t153 x)) (a := t797) (b := fun x => t153 x) (fun _ => rfl) c797 c153) x

private def rightMap134 (x : Nat) : Nat := force t67 (force t53 (force t50 (force t4 (force t211 (force t4 (force t303 (force t108 (force t793 (t56 x)))))))))
private def rightPerm134 : Equiv.Perm (Fin 4060) := p67 * (p53 * (p50 * (p4 * (p211 * (p4 * (p303 * (p108 * (p793 * (p56)))))))))
private theorem rightMap134_eq (x : Fin 4060) :
    rightMap134 x.val = (rightPerm134 x).val := (compose (t := fun x => force t67 (force t53 (force t50 (force t4 (force t211 (force t4 (force t303 (force t108 (force t793 (t56 x)))))))))) (a := t67) (b := fun x => force t53 (force t50 (force t4 (force t211 (force t4 (force t303 (force t108 (force t793 (t56 x))))))))) (fun _ => rfl) c67 (compose (t := fun x => force t53 (force t50 (force t4 (force t211 (force t4 (force t303 (force t108 (force t793 (t56 x))))))))) (a := t53) (b := fun x => force t50 (force t4 (force t211 (force t4 (force t303 (force t108 (force t793 (t56 x)))))))) (fun _ => rfl) c53 (compose (t := fun x => force t50 (force t4 (force t211 (force t4 (force t303 (force t108 (force t793 (t56 x)))))))) (a := t50) (b := fun x => force t4 (force t211 (force t4 (force t303 (force t108 (force t793 (t56 x))))))) (fun _ => rfl) c50 (compose (t := fun x => force t4 (force t211 (force t4 (force t303 (force t108 (force t793 (t56 x))))))) (a := t4) (b := fun x => force t211 (force t4 (force t303 (force t108 (force t793 (t56 x)))))) (fun _ => rfl) c4 (compose (t := fun x => force t211 (force t4 (force t303 (force t108 (force t793 (t56 x)))))) (a := t211) (b := fun x => force t4 (force t303 (force t108 (force t793 (t56 x))))) (fun _ => rfl) c211 (compose (t := fun x => force t4 (force t303 (force t108 (force t793 (t56 x))))) (a := t4) (b := fun x => force t303 (force t108 (force t793 (t56 x)))) (fun _ => rfl) c4 (compose (t := fun x => force t303 (force t108 (force t793 (t56 x)))) (a := t303) (b := fun x => force t108 (force t793 (t56 x))) (fun _ => rfl) c303 (compose (t := fun x => force t108 (force t793 (t56 x))) (a := t108) (b := fun x => force t793 (t56 x)) (fun _ => rfl) c108 (compose (t := fun x => force t793 (t56 x)) (a := t793) (b := fun x => t56 x) (fun _ => rfl) c793 c56))))))))) x

set_option maxHeartbeats 1600000 in
private theorem point134slice0 : Residual1Cache.slice leftMap134 rightMap134 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice1 : Residual1Cache.slice leftMap134 rightMap134 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice2 : Residual1Cache.slice leftMap134 rightMap134 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice3 : Residual1Cache.slice leftMap134 rightMap134 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice4 : Residual1Cache.slice leftMap134 rightMap134 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice5 : Residual1Cache.slice leftMap134 rightMap134 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice6 : Residual1Cache.slice leftMap134 rightMap134 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice7 : Residual1Cache.slice leftMap134 rightMap134 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice8 : Residual1Cache.slice leftMap134 rightMap134 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice9 : Residual1Cache.slice leftMap134 rightMap134 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice10 : Residual1Cache.slice leftMap134 rightMap134 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice11 : Residual1Cache.slice leftMap134 rightMap134 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice12 : Residual1Cache.slice leftMap134 rightMap134 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice13 : Residual1Cache.slice leftMap134 rightMap134 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice14 : Residual1Cache.slice leftMap134 rightMap134 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice15 : Residual1Cache.slice leftMap134 rightMap134 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice16 : Residual1Cache.slice leftMap134 rightMap134 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice17 : Residual1Cache.slice leftMap134 rightMap134 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice18 : Residual1Cache.slice leftMap134 rightMap134 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice19 : Residual1Cache.slice leftMap134 rightMap134 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice20 : Residual1Cache.slice leftMap134 rightMap134 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice21 : Residual1Cache.slice leftMap134 rightMap134 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice22 : Residual1Cache.slice leftMap134 rightMap134 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice23 : Residual1Cache.slice leftMap134 rightMap134 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice24 : Residual1Cache.slice leftMap134 rightMap134 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice25 : Residual1Cache.slice leftMap134 rightMap134 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice26 : Residual1Cache.slice leftMap134 rightMap134 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice27 : Residual1Cache.slice leftMap134 rightMap134 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice28 : Residual1Cache.slice leftMap134 rightMap134 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice29 : Residual1Cache.slice leftMap134 rightMap134 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice30 : Residual1Cache.slice leftMap134 rightMap134 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice31 : Residual1Cache.slice leftMap134 rightMap134 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice32 : Residual1Cache.slice leftMap134 rightMap134 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice33 : Residual1Cache.slice leftMap134 rightMap134 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice34 : Residual1Cache.slice leftMap134 rightMap134 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice35 : Residual1Cache.slice leftMap134 rightMap134 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice36 : Residual1Cache.slice leftMap134 rightMap134 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice37 : Residual1Cache.slice leftMap134 rightMap134 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice38 : Residual1Cache.slice leftMap134 rightMap134 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice39 : Residual1Cache.slice leftMap134 rightMap134 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice40 : Residual1Cache.slice leftMap134 rightMap134 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice41 : Residual1Cache.slice leftMap134 rightMap134 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice42 : Residual1Cache.slice leftMap134 rightMap134 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice43 : Residual1Cache.slice leftMap134 rightMap134 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice44 : Residual1Cache.slice leftMap134 rightMap134 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice45 : Residual1Cache.slice leftMap134 rightMap134 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice46 : Residual1Cache.slice leftMap134 rightMap134 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice47 : Residual1Cache.slice leftMap134 rightMap134 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice48 : Residual1Cache.slice leftMap134 rightMap134 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice49 : Residual1Cache.slice leftMap134 rightMap134 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice50 : Residual1Cache.slice leftMap134 rightMap134 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice51 : Residual1Cache.slice leftMap134 rightMap134 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice52 : Residual1Cache.slice leftMap134 rightMap134 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice53 : Residual1Cache.slice leftMap134 rightMap134 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice54 : Residual1Cache.slice leftMap134 rightMap134 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice55 : Residual1Cache.slice leftMap134 rightMap134 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice56 : Residual1Cache.slice leftMap134 rightMap134 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice57 : Residual1Cache.slice leftMap134 rightMap134 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice58 : Residual1Cache.slice leftMap134 rightMap134 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice59 : Residual1Cache.slice leftMap134 rightMap134 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice60 : Residual1Cache.slice leftMap134 rightMap134 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice61 : Residual1Cache.slice leftMap134 rightMap134 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice62 : Residual1Cache.slice leftMap134 rightMap134 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice63 : Residual1Cache.slice leftMap134 rightMap134 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice64 : Residual1Cache.slice leftMap134 rightMap134 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice65 : Residual1Cache.slice leftMap134 rightMap134 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice66 : Residual1Cache.slice leftMap134 rightMap134 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice67 : Residual1Cache.slice leftMap134 rightMap134 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice68 : Residual1Cache.slice leftMap134 rightMap134 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice69 : Residual1Cache.slice leftMap134 rightMap134 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice70 : Residual1Cache.slice leftMap134 rightMap134 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice71 : Residual1Cache.slice leftMap134 rightMap134 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice72 : Residual1Cache.slice leftMap134 rightMap134 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice73 : Residual1Cache.slice leftMap134 rightMap134 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice74 : Residual1Cache.slice leftMap134 rightMap134 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice75 : Residual1Cache.slice leftMap134 rightMap134 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice76 : Residual1Cache.slice leftMap134 rightMap134 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice77 : Residual1Cache.slice leftMap134 rightMap134 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice78 : Residual1Cache.slice leftMap134 rightMap134 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice79 : Residual1Cache.slice leftMap134 rightMap134 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice80 : Residual1Cache.slice leftMap134 rightMap134 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice81 : Residual1Cache.slice leftMap134 rightMap134 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice82 : Residual1Cache.slice leftMap134 rightMap134 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice83 : Residual1Cache.slice leftMap134 rightMap134 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice84 : Residual1Cache.slice leftMap134 rightMap134 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice85 : Residual1Cache.slice leftMap134 rightMap134 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice86 : Residual1Cache.slice leftMap134 rightMap134 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice87 : Residual1Cache.slice leftMap134 rightMap134 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice88 : Residual1Cache.slice leftMap134 rightMap134 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice89 : Residual1Cache.slice leftMap134 rightMap134 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice90 : Residual1Cache.slice leftMap134 rightMap134 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice91 : Residual1Cache.slice leftMap134 rightMap134 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice92 : Residual1Cache.slice leftMap134 rightMap134 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice93 : Residual1Cache.slice leftMap134 rightMap134 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice94 : Residual1Cache.slice leftMap134 rightMap134 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice95 : Residual1Cache.slice leftMap134 rightMap134 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice96 : Residual1Cache.slice leftMap134 rightMap134 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice97 : Residual1Cache.slice leftMap134 rightMap134 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice98 : Residual1Cache.slice leftMap134 rightMap134 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice99 : Residual1Cache.slice leftMap134 rightMap134 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice100 : Residual1Cache.slice leftMap134 rightMap134 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice101 : Residual1Cache.slice leftMap134 rightMap134 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice102 : Residual1Cache.slice leftMap134 rightMap134 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice103 : Residual1Cache.slice leftMap134 rightMap134 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice104 : Residual1Cache.slice leftMap134 rightMap134 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice105 : Residual1Cache.slice leftMap134 rightMap134 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice106 : Residual1Cache.slice leftMap134 rightMap134 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice107 : Residual1Cache.slice leftMap134 rightMap134 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice108 : Residual1Cache.slice leftMap134 rightMap134 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice109 : Residual1Cache.slice leftMap134 rightMap134 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice110 : Residual1Cache.slice leftMap134 rightMap134 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice111 : Residual1Cache.slice leftMap134 rightMap134 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice112 : Residual1Cache.slice leftMap134 rightMap134 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice113 : Residual1Cache.slice leftMap134 rightMap134 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice114 : Residual1Cache.slice leftMap134 rightMap134 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice115 : Residual1Cache.slice leftMap134 rightMap134 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice116 : Residual1Cache.slice leftMap134 rightMap134 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice117 : Residual1Cache.slice leftMap134 rightMap134 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice118 : Residual1Cache.slice leftMap134 rightMap134 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice119 : Residual1Cache.slice leftMap134 rightMap134 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice120 : Residual1Cache.slice leftMap134 rightMap134 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice121 : Residual1Cache.slice leftMap134 rightMap134 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice122 : Residual1Cache.slice leftMap134 rightMap134 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice123 : Residual1Cache.slice leftMap134 rightMap134 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice124 : Residual1Cache.slice leftMap134 rightMap134 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice125 : Residual1Cache.slice leftMap134 rightMap134 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice126 : Residual1Cache.slice leftMap134 rightMap134 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice127 : Residual1Cache.slice leftMap134 rightMap134 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice128 : Residual1Cache.slice leftMap134 rightMap134 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice129 : Residual1Cache.slice leftMap134 rightMap134 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice130 : Residual1Cache.slice leftMap134 rightMap134 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice131 : Residual1Cache.slice leftMap134 rightMap134 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice132 : Residual1Cache.slice leftMap134 rightMap134 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice133 : Residual1Cache.slice leftMap134 rightMap134 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice134 : Residual1Cache.slice leftMap134 rightMap134 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice135 : Residual1Cache.slice leftMap134 rightMap134 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice136 : Residual1Cache.slice leftMap134 rightMap134 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice137 : Residual1Cache.slice leftMap134 rightMap134 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice138 : Residual1Cache.slice leftMap134 rightMap134 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice139 : Residual1Cache.slice leftMap134 rightMap134 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice140 : Residual1Cache.slice leftMap134 rightMap134 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice141 : Residual1Cache.slice leftMap134 rightMap134 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice142 : Residual1Cache.slice leftMap134 rightMap134 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice143 : Residual1Cache.slice leftMap134 rightMap134 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice144 : Residual1Cache.slice leftMap134 rightMap134 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice145 : Residual1Cache.slice leftMap134 rightMap134 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice146 : Residual1Cache.slice leftMap134 rightMap134 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice147 : Residual1Cache.slice leftMap134 rightMap134 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice148 : Residual1Cache.slice leftMap134 rightMap134 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice149 : Residual1Cache.slice leftMap134 rightMap134 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice150 : Residual1Cache.slice leftMap134 rightMap134 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice151 : Residual1Cache.slice leftMap134 rightMap134 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice152 : Residual1Cache.slice leftMap134 rightMap134 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice153 : Residual1Cache.slice leftMap134 rightMap134 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice154 : Residual1Cache.slice leftMap134 rightMap134 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice155 : Residual1Cache.slice leftMap134 rightMap134 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice156 : Residual1Cache.slice leftMap134 rightMap134 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice157 : Residual1Cache.slice leftMap134 rightMap134 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice158 : Residual1Cache.slice leftMap134 rightMap134 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice159 : Residual1Cache.slice leftMap134 rightMap134 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice160 : Residual1Cache.slice leftMap134 rightMap134 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice161 : Residual1Cache.slice leftMap134 rightMap134 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice162 : Residual1Cache.slice leftMap134 rightMap134 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice163 : Residual1Cache.slice leftMap134 rightMap134 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice164 : Residual1Cache.slice leftMap134 rightMap134 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice165 : Residual1Cache.slice leftMap134 rightMap134 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice166 : Residual1Cache.slice leftMap134 rightMap134 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice167 : Residual1Cache.slice leftMap134 rightMap134 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice168 : Residual1Cache.slice leftMap134 rightMap134 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice169 : Residual1Cache.slice leftMap134 rightMap134 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice170 : Residual1Cache.slice leftMap134 rightMap134 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice171 : Residual1Cache.slice leftMap134 rightMap134 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice172 : Residual1Cache.slice leftMap134 rightMap134 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice173 : Residual1Cache.slice leftMap134 rightMap134 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice174 : Residual1Cache.slice leftMap134 rightMap134 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice175 : Residual1Cache.slice leftMap134 rightMap134 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice176 : Residual1Cache.slice leftMap134 rightMap134 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice177 : Residual1Cache.slice leftMap134 rightMap134 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice178 : Residual1Cache.slice leftMap134 rightMap134 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice179 : Residual1Cache.slice leftMap134 rightMap134 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice180 : Residual1Cache.slice leftMap134 rightMap134 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice181 : Residual1Cache.slice leftMap134 rightMap134 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice182 : Residual1Cache.slice leftMap134 rightMap134 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice183 : Residual1Cache.slice leftMap134 rightMap134 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice184 : Residual1Cache.slice leftMap134 rightMap134 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice185 : Residual1Cache.slice leftMap134 rightMap134 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice186 : Residual1Cache.slice leftMap134 rightMap134 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice187 : Residual1Cache.slice leftMap134 rightMap134 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice188 : Residual1Cache.slice leftMap134 rightMap134 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice189 : Residual1Cache.slice leftMap134 rightMap134 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice190 : Residual1Cache.slice leftMap134 rightMap134 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice191 : Residual1Cache.slice leftMap134 rightMap134 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice192 : Residual1Cache.slice leftMap134 rightMap134 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice193 : Residual1Cache.slice leftMap134 rightMap134 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice194 : Residual1Cache.slice leftMap134 rightMap134 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice195 : Residual1Cache.slice leftMap134 rightMap134 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice196 : Residual1Cache.slice leftMap134 rightMap134 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice197 : Residual1Cache.slice leftMap134 rightMap134 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice198 : Residual1Cache.slice leftMap134 rightMap134 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice199 : Residual1Cache.slice leftMap134 rightMap134 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice200 : Residual1Cache.slice leftMap134 rightMap134 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice201 : Residual1Cache.slice leftMap134 rightMap134 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point134slice202 : Residual1Cache.slice leftMap134 rightMap134 202 = true := by
  decide +kernel

private theorem point134_slices : ∀ c, Residual1Cache.slice leftMap134 rightMap134 c = true := by
  intro c
  fin_cases c
  · exact point134slice0
  · exact point134slice1
  · exact point134slice2
  · exact point134slice3
  · exact point134slice4
  · exact point134slice5
  · exact point134slice6
  · exact point134slice7
  · exact point134slice8
  · exact point134slice9
  · exact point134slice10
  · exact point134slice11
  · exact point134slice12
  · exact point134slice13
  · exact point134slice14
  · exact point134slice15
  · exact point134slice16
  · exact point134slice17
  · exact point134slice18
  · exact point134slice19
  · exact point134slice20
  · exact point134slice21
  · exact point134slice22
  · exact point134slice23
  · exact point134slice24
  · exact point134slice25
  · exact point134slice26
  · exact point134slice27
  · exact point134slice28
  · exact point134slice29
  · exact point134slice30
  · exact point134slice31
  · exact point134slice32
  · exact point134slice33
  · exact point134slice34
  · exact point134slice35
  · exact point134slice36
  · exact point134slice37
  · exact point134slice38
  · exact point134slice39
  · exact point134slice40
  · exact point134slice41
  · exact point134slice42
  · exact point134slice43
  · exact point134slice44
  · exact point134slice45
  · exact point134slice46
  · exact point134slice47
  · exact point134slice48
  · exact point134slice49
  · exact point134slice50
  · exact point134slice51
  · exact point134slice52
  · exact point134slice53
  · exact point134slice54
  · exact point134slice55
  · exact point134slice56
  · exact point134slice57
  · exact point134slice58
  · exact point134slice59
  · exact point134slice60
  · exact point134slice61
  · exact point134slice62
  · exact point134slice63
  · exact point134slice64
  · exact point134slice65
  · exact point134slice66
  · exact point134slice67
  · exact point134slice68
  · exact point134slice69
  · exact point134slice70
  · exact point134slice71
  · exact point134slice72
  · exact point134slice73
  · exact point134slice74
  · exact point134slice75
  · exact point134slice76
  · exact point134slice77
  · exact point134slice78
  · exact point134slice79
  · exact point134slice80
  · exact point134slice81
  · exact point134slice82
  · exact point134slice83
  · exact point134slice84
  · exact point134slice85
  · exact point134slice86
  · exact point134slice87
  · exact point134slice88
  · exact point134slice89
  · exact point134slice90
  · exact point134slice91
  · exact point134slice92
  · exact point134slice93
  · exact point134slice94
  · exact point134slice95
  · exact point134slice96
  · exact point134slice97
  · exact point134slice98
  · exact point134slice99
  · exact point134slice100
  · exact point134slice101
  · exact point134slice102
  · exact point134slice103
  · exact point134slice104
  · exact point134slice105
  · exact point134slice106
  · exact point134slice107
  · exact point134slice108
  · exact point134slice109
  · exact point134slice110
  · exact point134slice111
  · exact point134slice112
  · exact point134slice113
  · exact point134slice114
  · exact point134slice115
  · exact point134slice116
  · exact point134slice117
  · exact point134slice118
  · exact point134slice119
  · exact point134slice120
  · exact point134slice121
  · exact point134slice122
  · exact point134slice123
  · exact point134slice124
  · exact point134slice125
  · exact point134slice126
  · exact point134slice127
  · exact point134slice128
  · exact point134slice129
  · exact point134slice130
  · exact point134slice131
  · exact point134slice132
  · exact point134slice133
  · exact point134slice134
  · exact point134slice135
  · exact point134slice136
  · exact point134slice137
  · exact point134slice138
  · exact point134slice139
  · exact point134slice140
  · exact point134slice141
  · exact point134slice142
  · exact point134slice143
  · exact point134slice144
  · exact point134slice145
  · exact point134slice146
  · exact point134slice147
  · exact point134slice148
  · exact point134slice149
  · exact point134slice150
  · exact point134slice151
  · exact point134slice152
  · exact point134slice153
  · exact point134slice154
  · exact point134slice155
  · exact point134slice156
  · exact point134slice157
  · exact point134slice158
  · exact point134slice159
  · exact point134slice160
  · exact point134slice161
  · exact point134slice162
  · exact point134slice163
  · exact point134slice164
  · exact point134slice165
  · exact point134slice166
  · exact point134slice167
  · exact point134slice168
  · exact point134slice169
  · exact point134slice170
  · exact point134slice171
  · exact point134slice172
  · exact point134slice173
  · exact point134slice174
  · exact point134slice175
  · exact point134slice176
  · exact point134slice177
  · exact point134slice178
  · exact point134slice179
  · exact point134slice180
  · exact point134slice181
  · exact point134slice182
  · exact point134slice183
  · exact point134slice184
  · exact point134slice185
  · exact point134slice186
  · exact point134slice187
  · exact point134slice188
  · exact point134slice189
  · exact point134slice190
  · exact point134slice191
  · exact point134slice192
  · exact point134slice193
  · exact point134slice194
  · exact point134slice195
  · exact point134slice196
  · exact point134slice197
  · exact point134slice198
  · exact point134slice199
  · exact point134slice200
  · exact point134slice201
  · exact point134slice202

set_option maxHeartbeats 1600000 in
public theorem point134 : stepCheck 1 2701 := by
  have hleft : L0Gen 1 * L0Rep 2701 = leftPerm134 := by
    change L0Gen 1 * evalWord L0Gen [0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 3] = leftPerm134
    simp only [leftPerm134, p797, p153, p122, p27, p20, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2701) * evalWord L1Gen (L0Factor 1 2701) = rightPerm134 := by
    change evalWord L0Gen [0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] * evalWord L1Gen [0, 3, 0, 3, 0, 0, 3, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm134
    simp only [rightPerm134, p793, p303, p211, p109, p108, p89, p70, p67, p56, p53, p51, p50, p49, p46, p45, p44, p43, p42, p41, p40, p39, p37, p36, p35, p34, p33, p32, p31, p29, p28, p26, p24, p23, p22, p21, p20, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2701) x =
    (L0Rep (L0Act 1 2701) * evalWord L1Gen (L0Factor 1 2701)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap134_eq, ← rightMap134_eq]
  exact Residual1Cache.ofSlices point134_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
