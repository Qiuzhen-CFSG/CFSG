module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level07Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 119

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap119 (x : Nat) : Nat := force t686 (t80 x)
private def leftPerm119 : Equiv.Perm (Fin 4060) := p686 * (p80)
private theorem leftMap119_eq (x : Fin 4060) :
    leftMap119 x.val = (leftPerm119 x).val := (compose (t := fun x => force t686 (t80 x)) (a := t686) (b := fun x => t80 x) (fun _ => rfl) c686 c80) x

private def rightMap119 (x : Nat) : Nat := force t275 (force t68 (force t993 (force t196 (force t254 (force t849 (t64 x))))))
private def rightPerm119 : Equiv.Perm (Fin 4060) := p275 * (p68 * (p993 * (p196 * (p254 * (p849 * (p64))))))
private theorem rightMap119_eq (x : Fin 4060) :
    rightMap119 x.val = (rightPerm119 x).val := (compose (t := fun x => force t275 (force t68 (force t993 (force t196 (force t254 (force t849 (t64 x))))))) (a := t275) (b := fun x => force t68 (force t993 (force t196 (force t254 (force t849 (t64 x)))))) (fun _ => rfl) c275 (compose (t := fun x => force t68 (force t993 (force t196 (force t254 (force t849 (t64 x)))))) (a := t68) (b := fun x => force t993 (force t196 (force t254 (force t849 (t64 x))))) (fun _ => rfl) c68 (compose (t := fun x => force t993 (force t196 (force t254 (force t849 (t64 x))))) (a := t993) (b := fun x => force t196 (force t254 (force t849 (t64 x)))) (fun _ => rfl) c993 (compose (t := fun x => force t196 (force t254 (force t849 (t64 x)))) (a := t196) (b := fun x => force t254 (force t849 (t64 x))) (fun _ => rfl) c196 (compose (t := fun x => force t254 (force t849 (t64 x))) (a := t254) (b := fun x => force t849 (t64 x)) (fun _ => rfl) c254 (compose (t := fun x => force t849 (t64 x)) (a := t849) (b := fun x => t64 x) (fun _ => rfl) c849 c64)))))) x

set_option maxHeartbeats 1600000 in
private theorem point119slice0 : Residual1Cache.slice leftMap119 rightMap119 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice1 : Residual1Cache.slice leftMap119 rightMap119 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice2 : Residual1Cache.slice leftMap119 rightMap119 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice3 : Residual1Cache.slice leftMap119 rightMap119 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice4 : Residual1Cache.slice leftMap119 rightMap119 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice5 : Residual1Cache.slice leftMap119 rightMap119 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice6 : Residual1Cache.slice leftMap119 rightMap119 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice7 : Residual1Cache.slice leftMap119 rightMap119 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice8 : Residual1Cache.slice leftMap119 rightMap119 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice9 : Residual1Cache.slice leftMap119 rightMap119 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice10 : Residual1Cache.slice leftMap119 rightMap119 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice11 : Residual1Cache.slice leftMap119 rightMap119 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice12 : Residual1Cache.slice leftMap119 rightMap119 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice13 : Residual1Cache.slice leftMap119 rightMap119 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice14 : Residual1Cache.slice leftMap119 rightMap119 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice15 : Residual1Cache.slice leftMap119 rightMap119 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice16 : Residual1Cache.slice leftMap119 rightMap119 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice17 : Residual1Cache.slice leftMap119 rightMap119 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice18 : Residual1Cache.slice leftMap119 rightMap119 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice19 : Residual1Cache.slice leftMap119 rightMap119 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice20 : Residual1Cache.slice leftMap119 rightMap119 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice21 : Residual1Cache.slice leftMap119 rightMap119 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice22 : Residual1Cache.slice leftMap119 rightMap119 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice23 : Residual1Cache.slice leftMap119 rightMap119 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice24 : Residual1Cache.slice leftMap119 rightMap119 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice25 : Residual1Cache.slice leftMap119 rightMap119 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice26 : Residual1Cache.slice leftMap119 rightMap119 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice27 : Residual1Cache.slice leftMap119 rightMap119 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice28 : Residual1Cache.slice leftMap119 rightMap119 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice29 : Residual1Cache.slice leftMap119 rightMap119 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice30 : Residual1Cache.slice leftMap119 rightMap119 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice31 : Residual1Cache.slice leftMap119 rightMap119 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice32 : Residual1Cache.slice leftMap119 rightMap119 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice33 : Residual1Cache.slice leftMap119 rightMap119 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice34 : Residual1Cache.slice leftMap119 rightMap119 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice35 : Residual1Cache.slice leftMap119 rightMap119 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice36 : Residual1Cache.slice leftMap119 rightMap119 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice37 : Residual1Cache.slice leftMap119 rightMap119 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice38 : Residual1Cache.slice leftMap119 rightMap119 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice39 : Residual1Cache.slice leftMap119 rightMap119 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice40 : Residual1Cache.slice leftMap119 rightMap119 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice41 : Residual1Cache.slice leftMap119 rightMap119 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice42 : Residual1Cache.slice leftMap119 rightMap119 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice43 : Residual1Cache.slice leftMap119 rightMap119 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice44 : Residual1Cache.slice leftMap119 rightMap119 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice45 : Residual1Cache.slice leftMap119 rightMap119 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice46 : Residual1Cache.slice leftMap119 rightMap119 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice47 : Residual1Cache.slice leftMap119 rightMap119 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice48 : Residual1Cache.slice leftMap119 rightMap119 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice49 : Residual1Cache.slice leftMap119 rightMap119 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice50 : Residual1Cache.slice leftMap119 rightMap119 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice51 : Residual1Cache.slice leftMap119 rightMap119 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice52 : Residual1Cache.slice leftMap119 rightMap119 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice53 : Residual1Cache.slice leftMap119 rightMap119 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice54 : Residual1Cache.slice leftMap119 rightMap119 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice55 : Residual1Cache.slice leftMap119 rightMap119 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice56 : Residual1Cache.slice leftMap119 rightMap119 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice57 : Residual1Cache.slice leftMap119 rightMap119 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice58 : Residual1Cache.slice leftMap119 rightMap119 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice59 : Residual1Cache.slice leftMap119 rightMap119 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice60 : Residual1Cache.slice leftMap119 rightMap119 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice61 : Residual1Cache.slice leftMap119 rightMap119 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice62 : Residual1Cache.slice leftMap119 rightMap119 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice63 : Residual1Cache.slice leftMap119 rightMap119 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice64 : Residual1Cache.slice leftMap119 rightMap119 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice65 : Residual1Cache.slice leftMap119 rightMap119 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice66 : Residual1Cache.slice leftMap119 rightMap119 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice67 : Residual1Cache.slice leftMap119 rightMap119 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice68 : Residual1Cache.slice leftMap119 rightMap119 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice69 : Residual1Cache.slice leftMap119 rightMap119 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice70 : Residual1Cache.slice leftMap119 rightMap119 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice71 : Residual1Cache.slice leftMap119 rightMap119 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice72 : Residual1Cache.slice leftMap119 rightMap119 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice73 : Residual1Cache.slice leftMap119 rightMap119 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice74 : Residual1Cache.slice leftMap119 rightMap119 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice75 : Residual1Cache.slice leftMap119 rightMap119 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice76 : Residual1Cache.slice leftMap119 rightMap119 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice77 : Residual1Cache.slice leftMap119 rightMap119 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice78 : Residual1Cache.slice leftMap119 rightMap119 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice79 : Residual1Cache.slice leftMap119 rightMap119 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice80 : Residual1Cache.slice leftMap119 rightMap119 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice81 : Residual1Cache.slice leftMap119 rightMap119 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice82 : Residual1Cache.slice leftMap119 rightMap119 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice83 : Residual1Cache.slice leftMap119 rightMap119 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice84 : Residual1Cache.slice leftMap119 rightMap119 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice85 : Residual1Cache.slice leftMap119 rightMap119 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice86 : Residual1Cache.slice leftMap119 rightMap119 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice87 : Residual1Cache.slice leftMap119 rightMap119 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice88 : Residual1Cache.slice leftMap119 rightMap119 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice89 : Residual1Cache.slice leftMap119 rightMap119 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice90 : Residual1Cache.slice leftMap119 rightMap119 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice91 : Residual1Cache.slice leftMap119 rightMap119 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice92 : Residual1Cache.slice leftMap119 rightMap119 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice93 : Residual1Cache.slice leftMap119 rightMap119 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice94 : Residual1Cache.slice leftMap119 rightMap119 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice95 : Residual1Cache.slice leftMap119 rightMap119 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice96 : Residual1Cache.slice leftMap119 rightMap119 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice97 : Residual1Cache.slice leftMap119 rightMap119 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice98 : Residual1Cache.slice leftMap119 rightMap119 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice99 : Residual1Cache.slice leftMap119 rightMap119 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice100 : Residual1Cache.slice leftMap119 rightMap119 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice101 : Residual1Cache.slice leftMap119 rightMap119 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice102 : Residual1Cache.slice leftMap119 rightMap119 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice103 : Residual1Cache.slice leftMap119 rightMap119 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice104 : Residual1Cache.slice leftMap119 rightMap119 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice105 : Residual1Cache.slice leftMap119 rightMap119 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice106 : Residual1Cache.slice leftMap119 rightMap119 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice107 : Residual1Cache.slice leftMap119 rightMap119 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice108 : Residual1Cache.slice leftMap119 rightMap119 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice109 : Residual1Cache.slice leftMap119 rightMap119 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice110 : Residual1Cache.slice leftMap119 rightMap119 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice111 : Residual1Cache.slice leftMap119 rightMap119 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice112 : Residual1Cache.slice leftMap119 rightMap119 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice113 : Residual1Cache.slice leftMap119 rightMap119 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice114 : Residual1Cache.slice leftMap119 rightMap119 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice115 : Residual1Cache.slice leftMap119 rightMap119 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice116 : Residual1Cache.slice leftMap119 rightMap119 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice117 : Residual1Cache.slice leftMap119 rightMap119 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice118 : Residual1Cache.slice leftMap119 rightMap119 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice119 : Residual1Cache.slice leftMap119 rightMap119 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice120 : Residual1Cache.slice leftMap119 rightMap119 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice121 : Residual1Cache.slice leftMap119 rightMap119 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice122 : Residual1Cache.slice leftMap119 rightMap119 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice123 : Residual1Cache.slice leftMap119 rightMap119 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice124 : Residual1Cache.slice leftMap119 rightMap119 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice125 : Residual1Cache.slice leftMap119 rightMap119 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice126 : Residual1Cache.slice leftMap119 rightMap119 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice127 : Residual1Cache.slice leftMap119 rightMap119 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice128 : Residual1Cache.slice leftMap119 rightMap119 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice129 : Residual1Cache.slice leftMap119 rightMap119 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice130 : Residual1Cache.slice leftMap119 rightMap119 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice131 : Residual1Cache.slice leftMap119 rightMap119 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice132 : Residual1Cache.slice leftMap119 rightMap119 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice133 : Residual1Cache.slice leftMap119 rightMap119 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice134 : Residual1Cache.slice leftMap119 rightMap119 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice135 : Residual1Cache.slice leftMap119 rightMap119 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice136 : Residual1Cache.slice leftMap119 rightMap119 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice137 : Residual1Cache.slice leftMap119 rightMap119 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice138 : Residual1Cache.slice leftMap119 rightMap119 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice139 : Residual1Cache.slice leftMap119 rightMap119 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice140 : Residual1Cache.slice leftMap119 rightMap119 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice141 : Residual1Cache.slice leftMap119 rightMap119 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice142 : Residual1Cache.slice leftMap119 rightMap119 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice143 : Residual1Cache.slice leftMap119 rightMap119 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice144 : Residual1Cache.slice leftMap119 rightMap119 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice145 : Residual1Cache.slice leftMap119 rightMap119 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice146 : Residual1Cache.slice leftMap119 rightMap119 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice147 : Residual1Cache.slice leftMap119 rightMap119 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice148 : Residual1Cache.slice leftMap119 rightMap119 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice149 : Residual1Cache.slice leftMap119 rightMap119 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice150 : Residual1Cache.slice leftMap119 rightMap119 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice151 : Residual1Cache.slice leftMap119 rightMap119 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice152 : Residual1Cache.slice leftMap119 rightMap119 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice153 : Residual1Cache.slice leftMap119 rightMap119 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice154 : Residual1Cache.slice leftMap119 rightMap119 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice155 : Residual1Cache.slice leftMap119 rightMap119 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice156 : Residual1Cache.slice leftMap119 rightMap119 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice157 : Residual1Cache.slice leftMap119 rightMap119 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice158 : Residual1Cache.slice leftMap119 rightMap119 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice159 : Residual1Cache.slice leftMap119 rightMap119 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice160 : Residual1Cache.slice leftMap119 rightMap119 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice161 : Residual1Cache.slice leftMap119 rightMap119 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice162 : Residual1Cache.slice leftMap119 rightMap119 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice163 : Residual1Cache.slice leftMap119 rightMap119 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice164 : Residual1Cache.slice leftMap119 rightMap119 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice165 : Residual1Cache.slice leftMap119 rightMap119 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice166 : Residual1Cache.slice leftMap119 rightMap119 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice167 : Residual1Cache.slice leftMap119 rightMap119 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice168 : Residual1Cache.slice leftMap119 rightMap119 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice169 : Residual1Cache.slice leftMap119 rightMap119 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice170 : Residual1Cache.slice leftMap119 rightMap119 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice171 : Residual1Cache.slice leftMap119 rightMap119 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice172 : Residual1Cache.slice leftMap119 rightMap119 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice173 : Residual1Cache.slice leftMap119 rightMap119 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice174 : Residual1Cache.slice leftMap119 rightMap119 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice175 : Residual1Cache.slice leftMap119 rightMap119 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice176 : Residual1Cache.slice leftMap119 rightMap119 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice177 : Residual1Cache.slice leftMap119 rightMap119 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice178 : Residual1Cache.slice leftMap119 rightMap119 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice179 : Residual1Cache.slice leftMap119 rightMap119 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice180 : Residual1Cache.slice leftMap119 rightMap119 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice181 : Residual1Cache.slice leftMap119 rightMap119 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice182 : Residual1Cache.slice leftMap119 rightMap119 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice183 : Residual1Cache.slice leftMap119 rightMap119 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice184 : Residual1Cache.slice leftMap119 rightMap119 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice185 : Residual1Cache.slice leftMap119 rightMap119 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice186 : Residual1Cache.slice leftMap119 rightMap119 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice187 : Residual1Cache.slice leftMap119 rightMap119 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice188 : Residual1Cache.slice leftMap119 rightMap119 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice189 : Residual1Cache.slice leftMap119 rightMap119 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice190 : Residual1Cache.slice leftMap119 rightMap119 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice191 : Residual1Cache.slice leftMap119 rightMap119 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice192 : Residual1Cache.slice leftMap119 rightMap119 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice193 : Residual1Cache.slice leftMap119 rightMap119 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice194 : Residual1Cache.slice leftMap119 rightMap119 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice195 : Residual1Cache.slice leftMap119 rightMap119 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice196 : Residual1Cache.slice leftMap119 rightMap119 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice197 : Residual1Cache.slice leftMap119 rightMap119 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice198 : Residual1Cache.slice leftMap119 rightMap119 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice199 : Residual1Cache.slice leftMap119 rightMap119 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice200 : Residual1Cache.slice leftMap119 rightMap119 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice201 : Residual1Cache.slice leftMap119 rightMap119 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point119slice202 : Residual1Cache.slice leftMap119 rightMap119 202 = true := by
  decide +kernel

private theorem point119_slices : ∀ c, Residual1Cache.slice leftMap119 rightMap119 c = true := by
  intro c
  fin_cases c
  · exact point119slice0
  · exact point119slice1
  · exact point119slice2
  · exact point119slice3
  · exact point119slice4
  · exact point119slice5
  · exact point119slice6
  · exact point119slice7
  · exact point119slice8
  · exact point119slice9
  · exact point119slice10
  · exact point119slice11
  · exact point119slice12
  · exact point119slice13
  · exact point119slice14
  · exact point119slice15
  · exact point119slice16
  · exact point119slice17
  · exact point119slice18
  · exact point119slice19
  · exact point119slice20
  · exact point119slice21
  · exact point119slice22
  · exact point119slice23
  · exact point119slice24
  · exact point119slice25
  · exact point119slice26
  · exact point119slice27
  · exact point119slice28
  · exact point119slice29
  · exact point119slice30
  · exact point119slice31
  · exact point119slice32
  · exact point119slice33
  · exact point119slice34
  · exact point119slice35
  · exact point119slice36
  · exact point119slice37
  · exact point119slice38
  · exact point119slice39
  · exact point119slice40
  · exact point119slice41
  · exact point119slice42
  · exact point119slice43
  · exact point119slice44
  · exact point119slice45
  · exact point119slice46
  · exact point119slice47
  · exact point119slice48
  · exact point119slice49
  · exact point119slice50
  · exact point119slice51
  · exact point119slice52
  · exact point119slice53
  · exact point119slice54
  · exact point119slice55
  · exact point119slice56
  · exact point119slice57
  · exact point119slice58
  · exact point119slice59
  · exact point119slice60
  · exact point119slice61
  · exact point119slice62
  · exact point119slice63
  · exact point119slice64
  · exact point119slice65
  · exact point119slice66
  · exact point119slice67
  · exact point119slice68
  · exact point119slice69
  · exact point119slice70
  · exact point119slice71
  · exact point119slice72
  · exact point119slice73
  · exact point119slice74
  · exact point119slice75
  · exact point119slice76
  · exact point119slice77
  · exact point119slice78
  · exact point119slice79
  · exact point119slice80
  · exact point119slice81
  · exact point119slice82
  · exact point119slice83
  · exact point119slice84
  · exact point119slice85
  · exact point119slice86
  · exact point119slice87
  · exact point119slice88
  · exact point119slice89
  · exact point119slice90
  · exact point119slice91
  · exact point119slice92
  · exact point119slice93
  · exact point119slice94
  · exact point119slice95
  · exact point119slice96
  · exact point119slice97
  · exact point119slice98
  · exact point119slice99
  · exact point119slice100
  · exact point119slice101
  · exact point119slice102
  · exact point119slice103
  · exact point119slice104
  · exact point119slice105
  · exact point119slice106
  · exact point119slice107
  · exact point119slice108
  · exact point119slice109
  · exact point119slice110
  · exact point119slice111
  · exact point119slice112
  · exact point119slice113
  · exact point119slice114
  · exact point119slice115
  · exact point119slice116
  · exact point119slice117
  · exact point119slice118
  · exact point119slice119
  · exact point119slice120
  · exact point119slice121
  · exact point119slice122
  · exact point119slice123
  · exact point119slice124
  · exact point119slice125
  · exact point119slice126
  · exact point119slice127
  · exact point119slice128
  · exact point119slice129
  · exact point119slice130
  · exact point119slice131
  · exact point119slice132
  · exact point119slice133
  · exact point119slice134
  · exact point119slice135
  · exact point119slice136
  · exact point119slice137
  · exact point119slice138
  · exact point119slice139
  · exact point119slice140
  · exact point119slice141
  · exact point119slice142
  · exact point119slice143
  · exact point119slice144
  · exact point119slice145
  · exact point119slice146
  · exact point119slice147
  · exact point119slice148
  · exact point119slice149
  · exact point119slice150
  · exact point119slice151
  · exact point119slice152
  · exact point119slice153
  · exact point119slice154
  · exact point119slice155
  · exact point119slice156
  · exact point119slice157
  · exact point119slice158
  · exact point119slice159
  · exact point119slice160
  · exact point119slice161
  · exact point119slice162
  · exact point119slice163
  · exact point119slice164
  · exact point119slice165
  · exact point119slice166
  · exact point119slice167
  · exact point119slice168
  · exact point119slice169
  · exact point119slice170
  · exact point119slice171
  · exact point119slice172
  · exact point119slice173
  · exact point119slice174
  · exact point119slice175
  · exact point119slice176
  · exact point119slice177
  · exact point119slice178
  · exact point119slice179
  · exact point119slice180
  · exact point119slice181
  · exact point119slice182
  · exact point119slice183
  · exact point119slice184
  · exact point119slice185
  · exact point119slice186
  · exact point119slice187
  · exact point119slice188
  · exact point119slice189
  · exact point119slice190
  · exact point119slice191
  · exact point119slice192
  · exact point119slice193
  · exact point119slice194
  · exact point119slice195
  · exact point119slice196
  · exact point119slice197
  · exact point119slice198
  · exact point119slice199
  · exact point119slice200
  · exact point119slice201
  · exact point119slice202

set_option maxHeartbeats 1600000 in
public theorem point119 : stepCheck 1 2566 := by
  have hleft : L0Gen 1 * L0Rep 2566 = leftPerm119 := by
    change L0Gen 1 * evalWord L0Gen [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1] = leftPerm119
    simp only [leftPerm119, p686, p80, p62, p48, p30, p20, p17, p11, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2566) * evalWord L1Gen (L0Factor 1 2566) = rightPerm119 := by
    change evalWord L0Gen [0, 1, 0, 3, 0, 3, 0, 1, 1, 0, 1, 1, 0, 1, 0] * evalWord L1Gen [0, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3] = rightPerm119
    simp only [rightPerm119, p993, p849, p276, p275, p254, p196, p68, p67, p64, p63, p61, p58, p55, p40, p38, p33, p30, p29, p28, p27, p26, p25, p24, p23, p21, p20, p18, p17, p16, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2566) x =
    (L0Rep (L0Act 1 2566) * evalWord L1Gen (L0Factor 1 2566)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap119_eq, ← rightMap119_eq]
  exact Residual1Cache.ofSlices point119_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
