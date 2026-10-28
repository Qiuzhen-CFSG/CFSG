module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 136

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap136 (x : Nat) : Nat := force t1000 (force t123 (t153 x))
private def leftPerm136 : Equiv.Perm (Fin 4060) := p1000 * (p123 * (p153))
private theorem leftMap136_eq (x : Fin 4060) :
    leftMap136 x.val = (leftPerm136 x).val := (compose (t := fun x => force t1000 (force t123 (t153 x))) (a := t1000) (b := fun x => force t123 (t153 x)) (fun _ => rfl) c1000 (compose (t := fun x => force t123 (t153 x)) (a := t123) (b := fun x => t153 x) (fun _ => rfl) c123 c153)) x

private def rightMap136 (x : Nat) : Nat := force t157 (force t374 (force t815 (force t8 (force t28 (force t28 (force t18 (force t21 (t58 x))))))))
private def rightPerm136 : Equiv.Perm (Fin 4060) := p157 * (p374 * (p815 * (p8 * (p28 * (p37 * (p18 * (p21 * (p58))))))))
private theorem rightMap136_eq (x : Fin 4060) :
    rightMap136 x.val = (rightPerm136 x).val := (compose (t := fun x => force t157 (force t374 (force t815 (force t8 (force t28 (force t28 (force t18 (force t21 (t58 x))))))))) (a := t157) (b := fun x => force t374 (force t815 (force t8 (force t28 (force t28 (force t18 (force t21 (t58 x)))))))) (fun _ => rfl) c157 (compose (t := fun x => force t374 (force t815 (force t8 (force t28 (force t28 (force t18 (force t21 (t58 x)))))))) (a := t374) (b := fun x => force t815 (force t8 (force t28 (force t28 (force t18 (force t21 (t58 x))))))) (fun _ => rfl) c374 (compose (t := fun x => force t815 (force t8 (force t28 (force t28 (force t18 (force t21 (t58 x))))))) (a := t815) (b := fun x => force t8 (force t28 (force t28 (force t18 (force t21 (t58 x)))))) (fun _ => rfl) c815 (compose (t := fun x => force t8 (force t28 (force t28 (force t18 (force t21 (t58 x)))))) (a := t8) (b := fun x => force t28 (force t28 (force t18 (force t21 (t58 x))))) (fun _ => rfl) c8 (compose (t := fun x => force t28 (force t28 (force t18 (force t21 (t58 x))))) (a := t28) (b := fun x => force t28 (force t18 (force t21 (t58 x)))) (fun _ => rfl) c28 (compose (t := fun x => force t28 (force t18 (force t21 (t58 x)))) (a := t28) (b := fun x => force t18 (force t21 (t58 x))) (fun _ => rfl) c37 (compose (t := fun x => force t18 (force t21 (t58 x))) (a := t18) (b := fun x => force t21 (t58 x)) (fun _ => rfl) c18 (compose (t := fun x => force t21 (t58 x)) (a := t21) (b := fun x => t58 x) (fun _ => rfl) c21 c58)))))))) x

set_option maxHeartbeats 1600000 in
private theorem point136slice0 : Residual1Cache.slice leftMap136 rightMap136 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice1 : Residual1Cache.slice leftMap136 rightMap136 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice2 : Residual1Cache.slice leftMap136 rightMap136 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice3 : Residual1Cache.slice leftMap136 rightMap136 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice4 : Residual1Cache.slice leftMap136 rightMap136 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice5 : Residual1Cache.slice leftMap136 rightMap136 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice6 : Residual1Cache.slice leftMap136 rightMap136 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice7 : Residual1Cache.slice leftMap136 rightMap136 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice8 : Residual1Cache.slice leftMap136 rightMap136 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice9 : Residual1Cache.slice leftMap136 rightMap136 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice10 : Residual1Cache.slice leftMap136 rightMap136 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice11 : Residual1Cache.slice leftMap136 rightMap136 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice12 : Residual1Cache.slice leftMap136 rightMap136 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice13 : Residual1Cache.slice leftMap136 rightMap136 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice14 : Residual1Cache.slice leftMap136 rightMap136 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice15 : Residual1Cache.slice leftMap136 rightMap136 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice16 : Residual1Cache.slice leftMap136 rightMap136 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice17 : Residual1Cache.slice leftMap136 rightMap136 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice18 : Residual1Cache.slice leftMap136 rightMap136 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice19 : Residual1Cache.slice leftMap136 rightMap136 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice20 : Residual1Cache.slice leftMap136 rightMap136 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice21 : Residual1Cache.slice leftMap136 rightMap136 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice22 : Residual1Cache.slice leftMap136 rightMap136 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice23 : Residual1Cache.slice leftMap136 rightMap136 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice24 : Residual1Cache.slice leftMap136 rightMap136 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice25 : Residual1Cache.slice leftMap136 rightMap136 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice26 : Residual1Cache.slice leftMap136 rightMap136 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice27 : Residual1Cache.slice leftMap136 rightMap136 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice28 : Residual1Cache.slice leftMap136 rightMap136 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice29 : Residual1Cache.slice leftMap136 rightMap136 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice30 : Residual1Cache.slice leftMap136 rightMap136 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice31 : Residual1Cache.slice leftMap136 rightMap136 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice32 : Residual1Cache.slice leftMap136 rightMap136 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice33 : Residual1Cache.slice leftMap136 rightMap136 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice34 : Residual1Cache.slice leftMap136 rightMap136 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice35 : Residual1Cache.slice leftMap136 rightMap136 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice36 : Residual1Cache.slice leftMap136 rightMap136 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice37 : Residual1Cache.slice leftMap136 rightMap136 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice38 : Residual1Cache.slice leftMap136 rightMap136 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice39 : Residual1Cache.slice leftMap136 rightMap136 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice40 : Residual1Cache.slice leftMap136 rightMap136 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice41 : Residual1Cache.slice leftMap136 rightMap136 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice42 : Residual1Cache.slice leftMap136 rightMap136 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice43 : Residual1Cache.slice leftMap136 rightMap136 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice44 : Residual1Cache.slice leftMap136 rightMap136 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice45 : Residual1Cache.slice leftMap136 rightMap136 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice46 : Residual1Cache.slice leftMap136 rightMap136 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice47 : Residual1Cache.slice leftMap136 rightMap136 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice48 : Residual1Cache.slice leftMap136 rightMap136 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice49 : Residual1Cache.slice leftMap136 rightMap136 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice50 : Residual1Cache.slice leftMap136 rightMap136 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice51 : Residual1Cache.slice leftMap136 rightMap136 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice52 : Residual1Cache.slice leftMap136 rightMap136 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice53 : Residual1Cache.slice leftMap136 rightMap136 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice54 : Residual1Cache.slice leftMap136 rightMap136 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice55 : Residual1Cache.slice leftMap136 rightMap136 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice56 : Residual1Cache.slice leftMap136 rightMap136 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice57 : Residual1Cache.slice leftMap136 rightMap136 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice58 : Residual1Cache.slice leftMap136 rightMap136 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice59 : Residual1Cache.slice leftMap136 rightMap136 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice60 : Residual1Cache.slice leftMap136 rightMap136 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice61 : Residual1Cache.slice leftMap136 rightMap136 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice62 : Residual1Cache.slice leftMap136 rightMap136 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice63 : Residual1Cache.slice leftMap136 rightMap136 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice64 : Residual1Cache.slice leftMap136 rightMap136 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice65 : Residual1Cache.slice leftMap136 rightMap136 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice66 : Residual1Cache.slice leftMap136 rightMap136 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice67 : Residual1Cache.slice leftMap136 rightMap136 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice68 : Residual1Cache.slice leftMap136 rightMap136 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice69 : Residual1Cache.slice leftMap136 rightMap136 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice70 : Residual1Cache.slice leftMap136 rightMap136 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice71 : Residual1Cache.slice leftMap136 rightMap136 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice72 : Residual1Cache.slice leftMap136 rightMap136 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice73 : Residual1Cache.slice leftMap136 rightMap136 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice74 : Residual1Cache.slice leftMap136 rightMap136 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice75 : Residual1Cache.slice leftMap136 rightMap136 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice76 : Residual1Cache.slice leftMap136 rightMap136 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice77 : Residual1Cache.slice leftMap136 rightMap136 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice78 : Residual1Cache.slice leftMap136 rightMap136 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice79 : Residual1Cache.slice leftMap136 rightMap136 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice80 : Residual1Cache.slice leftMap136 rightMap136 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice81 : Residual1Cache.slice leftMap136 rightMap136 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice82 : Residual1Cache.slice leftMap136 rightMap136 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice83 : Residual1Cache.slice leftMap136 rightMap136 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice84 : Residual1Cache.slice leftMap136 rightMap136 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice85 : Residual1Cache.slice leftMap136 rightMap136 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice86 : Residual1Cache.slice leftMap136 rightMap136 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice87 : Residual1Cache.slice leftMap136 rightMap136 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice88 : Residual1Cache.slice leftMap136 rightMap136 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice89 : Residual1Cache.slice leftMap136 rightMap136 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice90 : Residual1Cache.slice leftMap136 rightMap136 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice91 : Residual1Cache.slice leftMap136 rightMap136 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice92 : Residual1Cache.slice leftMap136 rightMap136 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice93 : Residual1Cache.slice leftMap136 rightMap136 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice94 : Residual1Cache.slice leftMap136 rightMap136 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice95 : Residual1Cache.slice leftMap136 rightMap136 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice96 : Residual1Cache.slice leftMap136 rightMap136 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice97 : Residual1Cache.slice leftMap136 rightMap136 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice98 : Residual1Cache.slice leftMap136 rightMap136 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice99 : Residual1Cache.slice leftMap136 rightMap136 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice100 : Residual1Cache.slice leftMap136 rightMap136 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice101 : Residual1Cache.slice leftMap136 rightMap136 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice102 : Residual1Cache.slice leftMap136 rightMap136 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice103 : Residual1Cache.slice leftMap136 rightMap136 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice104 : Residual1Cache.slice leftMap136 rightMap136 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice105 : Residual1Cache.slice leftMap136 rightMap136 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice106 : Residual1Cache.slice leftMap136 rightMap136 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice107 : Residual1Cache.slice leftMap136 rightMap136 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice108 : Residual1Cache.slice leftMap136 rightMap136 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice109 : Residual1Cache.slice leftMap136 rightMap136 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice110 : Residual1Cache.slice leftMap136 rightMap136 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice111 : Residual1Cache.slice leftMap136 rightMap136 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice112 : Residual1Cache.slice leftMap136 rightMap136 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice113 : Residual1Cache.slice leftMap136 rightMap136 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice114 : Residual1Cache.slice leftMap136 rightMap136 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice115 : Residual1Cache.slice leftMap136 rightMap136 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice116 : Residual1Cache.slice leftMap136 rightMap136 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice117 : Residual1Cache.slice leftMap136 rightMap136 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice118 : Residual1Cache.slice leftMap136 rightMap136 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice119 : Residual1Cache.slice leftMap136 rightMap136 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice120 : Residual1Cache.slice leftMap136 rightMap136 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice121 : Residual1Cache.slice leftMap136 rightMap136 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice122 : Residual1Cache.slice leftMap136 rightMap136 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice123 : Residual1Cache.slice leftMap136 rightMap136 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice124 : Residual1Cache.slice leftMap136 rightMap136 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice125 : Residual1Cache.slice leftMap136 rightMap136 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice126 : Residual1Cache.slice leftMap136 rightMap136 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice127 : Residual1Cache.slice leftMap136 rightMap136 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice128 : Residual1Cache.slice leftMap136 rightMap136 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice129 : Residual1Cache.slice leftMap136 rightMap136 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice130 : Residual1Cache.slice leftMap136 rightMap136 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice131 : Residual1Cache.slice leftMap136 rightMap136 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice132 : Residual1Cache.slice leftMap136 rightMap136 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice133 : Residual1Cache.slice leftMap136 rightMap136 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice134 : Residual1Cache.slice leftMap136 rightMap136 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice135 : Residual1Cache.slice leftMap136 rightMap136 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice136 : Residual1Cache.slice leftMap136 rightMap136 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice137 : Residual1Cache.slice leftMap136 rightMap136 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice138 : Residual1Cache.slice leftMap136 rightMap136 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice139 : Residual1Cache.slice leftMap136 rightMap136 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice140 : Residual1Cache.slice leftMap136 rightMap136 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice141 : Residual1Cache.slice leftMap136 rightMap136 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice142 : Residual1Cache.slice leftMap136 rightMap136 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice143 : Residual1Cache.slice leftMap136 rightMap136 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice144 : Residual1Cache.slice leftMap136 rightMap136 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice145 : Residual1Cache.slice leftMap136 rightMap136 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice146 : Residual1Cache.slice leftMap136 rightMap136 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice147 : Residual1Cache.slice leftMap136 rightMap136 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice148 : Residual1Cache.slice leftMap136 rightMap136 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice149 : Residual1Cache.slice leftMap136 rightMap136 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice150 : Residual1Cache.slice leftMap136 rightMap136 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice151 : Residual1Cache.slice leftMap136 rightMap136 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice152 : Residual1Cache.slice leftMap136 rightMap136 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice153 : Residual1Cache.slice leftMap136 rightMap136 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice154 : Residual1Cache.slice leftMap136 rightMap136 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice155 : Residual1Cache.slice leftMap136 rightMap136 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice156 : Residual1Cache.slice leftMap136 rightMap136 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice157 : Residual1Cache.slice leftMap136 rightMap136 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice158 : Residual1Cache.slice leftMap136 rightMap136 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice159 : Residual1Cache.slice leftMap136 rightMap136 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice160 : Residual1Cache.slice leftMap136 rightMap136 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice161 : Residual1Cache.slice leftMap136 rightMap136 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice162 : Residual1Cache.slice leftMap136 rightMap136 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice163 : Residual1Cache.slice leftMap136 rightMap136 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice164 : Residual1Cache.slice leftMap136 rightMap136 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice165 : Residual1Cache.slice leftMap136 rightMap136 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice166 : Residual1Cache.slice leftMap136 rightMap136 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice167 : Residual1Cache.slice leftMap136 rightMap136 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice168 : Residual1Cache.slice leftMap136 rightMap136 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice169 : Residual1Cache.slice leftMap136 rightMap136 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice170 : Residual1Cache.slice leftMap136 rightMap136 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice171 : Residual1Cache.slice leftMap136 rightMap136 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice172 : Residual1Cache.slice leftMap136 rightMap136 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice173 : Residual1Cache.slice leftMap136 rightMap136 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice174 : Residual1Cache.slice leftMap136 rightMap136 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice175 : Residual1Cache.slice leftMap136 rightMap136 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice176 : Residual1Cache.slice leftMap136 rightMap136 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice177 : Residual1Cache.slice leftMap136 rightMap136 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice178 : Residual1Cache.slice leftMap136 rightMap136 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice179 : Residual1Cache.slice leftMap136 rightMap136 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice180 : Residual1Cache.slice leftMap136 rightMap136 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice181 : Residual1Cache.slice leftMap136 rightMap136 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice182 : Residual1Cache.slice leftMap136 rightMap136 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice183 : Residual1Cache.slice leftMap136 rightMap136 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice184 : Residual1Cache.slice leftMap136 rightMap136 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice185 : Residual1Cache.slice leftMap136 rightMap136 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice186 : Residual1Cache.slice leftMap136 rightMap136 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice187 : Residual1Cache.slice leftMap136 rightMap136 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice188 : Residual1Cache.slice leftMap136 rightMap136 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice189 : Residual1Cache.slice leftMap136 rightMap136 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice190 : Residual1Cache.slice leftMap136 rightMap136 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice191 : Residual1Cache.slice leftMap136 rightMap136 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice192 : Residual1Cache.slice leftMap136 rightMap136 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice193 : Residual1Cache.slice leftMap136 rightMap136 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice194 : Residual1Cache.slice leftMap136 rightMap136 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice195 : Residual1Cache.slice leftMap136 rightMap136 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice196 : Residual1Cache.slice leftMap136 rightMap136 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice197 : Residual1Cache.slice leftMap136 rightMap136 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice198 : Residual1Cache.slice leftMap136 rightMap136 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice199 : Residual1Cache.slice leftMap136 rightMap136 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice200 : Residual1Cache.slice leftMap136 rightMap136 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice201 : Residual1Cache.slice leftMap136 rightMap136 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point136slice202 : Residual1Cache.slice leftMap136 rightMap136 202 = true := by
  decide +kernel

private theorem point136_slices : ∀ c, Residual1Cache.slice leftMap136 rightMap136 c = true := by
  intro c
  fin_cases c
  · exact point136slice0
  · exact point136slice1
  · exact point136slice2
  · exact point136slice3
  · exact point136slice4
  · exact point136slice5
  · exact point136slice6
  · exact point136slice7
  · exact point136slice8
  · exact point136slice9
  · exact point136slice10
  · exact point136slice11
  · exact point136slice12
  · exact point136slice13
  · exact point136slice14
  · exact point136slice15
  · exact point136slice16
  · exact point136slice17
  · exact point136slice18
  · exact point136slice19
  · exact point136slice20
  · exact point136slice21
  · exact point136slice22
  · exact point136slice23
  · exact point136slice24
  · exact point136slice25
  · exact point136slice26
  · exact point136slice27
  · exact point136slice28
  · exact point136slice29
  · exact point136slice30
  · exact point136slice31
  · exact point136slice32
  · exact point136slice33
  · exact point136slice34
  · exact point136slice35
  · exact point136slice36
  · exact point136slice37
  · exact point136slice38
  · exact point136slice39
  · exact point136slice40
  · exact point136slice41
  · exact point136slice42
  · exact point136slice43
  · exact point136slice44
  · exact point136slice45
  · exact point136slice46
  · exact point136slice47
  · exact point136slice48
  · exact point136slice49
  · exact point136slice50
  · exact point136slice51
  · exact point136slice52
  · exact point136slice53
  · exact point136slice54
  · exact point136slice55
  · exact point136slice56
  · exact point136slice57
  · exact point136slice58
  · exact point136slice59
  · exact point136slice60
  · exact point136slice61
  · exact point136slice62
  · exact point136slice63
  · exact point136slice64
  · exact point136slice65
  · exact point136slice66
  · exact point136slice67
  · exact point136slice68
  · exact point136slice69
  · exact point136slice70
  · exact point136slice71
  · exact point136slice72
  · exact point136slice73
  · exact point136slice74
  · exact point136slice75
  · exact point136slice76
  · exact point136slice77
  · exact point136slice78
  · exact point136slice79
  · exact point136slice80
  · exact point136slice81
  · exact point136slice82
  · exact point136slice83
  · exact point136slice84
  · exact point136slice85
  · exact point136slice86
  · exact point136slice87
  · exact point136slice88
  · exact point136slice89
  · exact point136slice90
  · exact point136slice91
  · exact point136slice92
  · exact point136slice93
  · exact point136slice94
  · exact point136slice95
  · exact point136slice96
  · exact point136slice97
  · exact point136slice98
  · exact point136slice99
  · exact point136slice100
  · exact point136slice101
  · exact point136slice102
  · exact point136slice103
  · exact point136slice104
  · exact point136slice105
  · exact point136slice106
  · exact point136slice107
  · exact point136slice108
  · exact point136slice109
  · exact point136slice110
  · exact point136slice111
  · exact point136slice112
  · exact point136slice113
  · exact point136slice114
  · exact point136slice115
  · exact point136slice116
  · exact point136slice117
  · exact point136slice118
  · exact point136slice119
  · exact point136slice120
  · exact point136slice121
  · exact point136slice122
  · exact point136slice123
  · exact point136slice124
  · exact point136slice125
  · exact point136slice126
  · exact point136slice127
  · exact point136slice128
  · exact point136slice129
  · exact point136slice130
  · exact point136slice131
  · exact point136slice132
  · exact point136slice133
  · exact point136slice134
  · exact point136slice135
  · exact point136slice136
  · exact point136slice137
  · exact point136slice138
  · exact point136slice139
  · exact point136slice140
  · exact point136slice141
  · exact point136slice142
  · exact point136slice143
  · exact point136slice144
  · exact point136slice145
  · exact point136slice146
  · exact point136slice147
  · exact point136slice148
  · exact point136slice149
  · exact point136slice150
  · exact point136slice151
  · exact point136slice152
  · exact point136slice153
  · exact point136slice154
  · exact point136slice155
  · exact point136slice156
  · exact point136slice157
  · exact point136slice158
  · exact point136slice159
  · exact point136slice160
  · exact point136slice161
  · exact point136slice162
  · exact point136slice163
  · exact point136slice164
  · exact point136slice165
  · exact point136slice166
  · exact point136slice167
  · exact point136slice168
  · exact point136slice169
  · exact point136slice170
  · exact point136slice171
  · exact point136slice172
  · exact point136slice173
  · exact point136slice174
  · exact point136slice175
  · exact point136slice176
  · exact point136slice177
  · exact point136slice178
  · exact point136slice179
  · exact point136slice180
  · exact point136slice181
  · exact point136slice182
  · exact point136slice183
  · exact point136slice184
  · exact point136slice185
  · exact point136slice186
  · exact point136slice187
  · exact point136slice188
  · exact point136slice189
  · exact point136slice190
  · exact point136slice191
  · exact point136slice192
  · exact point136slice193
  · exact point136slice194
  · exact point136slice195
  · exact point136slice196
  · exact point136slice197
  · exact point136slice198
  · exact point136slice199
  · exact point136slice200
  · exact point136slice201
  · exact point136slice202

set_option maxHeartbeats 1600000 in
public theorem point136 : stepCheck 1 2719 := by
  have hleft : L0Gen 1 * L0Rep 2719 = leftPerm136 := by
    change L0Gen 1 * evalWord L0Gen [1, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 1, 0, 3] = leftPerm136
    simp only [leftPerm136, p1000, p153, p123, p50, p47, p20, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2719) * evalWord L1Gen (L0Factor 1 2719) = rightPerm136 := by
    change evalWord L0Gen [0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 1, 0, 3] * evalWord L1Gen [0, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0] = rightPerm136
    simp only [rightPerm136, p815, p374, p276, p157, p86, p75, p58, p37, p28, p27, p26, p25, p23, p21, p20, p18, p16, p14, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2719) x =
    (L0Rep (L0Act 1 2719) * evalWord L1Gen (L0Factor 1 2719)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap136_eq, ← rightMap136_eq]
  exact Residual1Cache.ofSlices point136_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
