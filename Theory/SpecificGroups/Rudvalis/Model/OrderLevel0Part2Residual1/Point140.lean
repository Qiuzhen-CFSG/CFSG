module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level07Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level12Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 140

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap140 (x : Nat) : Nat := force t252 (t93 x)
private def leftPerm140 : Equiv.Perm (Fin 4060) := p252 * (p93)
private theorem leftMap140_eq (x : Fin 4060) :
    leftMap140 x.val = (leftPerm140 x).val := (compose (t := fun x => force t252 (t93 x)) (a := t252) (b := fun x => t93 x) (fun _ => rfl) c252 c93) x

private def rightMap140 (x : Nat) : Nat := force t115 (force t908 (force t135 (force t72 (force t577 (force t69 (force t431 (force t630 (t810 x))))))))
private def rightPerm140 : Equiv.Perm (Fin 4060) := p115 * (p908 * (p135 * (p72 * (p577 * (p69 * (p431 * (p630 * (p810))))))))
private theorem rightMap140_eq (x : Fin 4060) :
    rightMap140 x.val = (rightPerm140 x).val := (compose (t := fun x => force t115 (force t908 (force t135 (force t72 (force t577 (force t69 (force t431 (force t630 (t810 x))))))))) (a := t115) (b := fun x => force t908 (force t135 (force t72 (force t577 (force t69 (force t431 (force t630 (t810 x)))))))) (fun _ => rfl) c115 (compose (t := fun x => force t908 (force t135 (force t72 (force t577 (force t69 (force t431 (force t630 (t810 x)))))))) (a := t908) (b := fun x => force t135 (force t72 (force t577 (force t69 (force t431 (force t630 (t810 x))))))) (fun _ => rfl) c908 (compose (t := fun x => force t135 (force t72 (force t577 (force t69 (force t431 (force t630 (t810 x))))))) (a := t135) (b := fun x => force t72 (force t577 (force t69 (force t431 (force t630 (t810 x)))))) (fun _ => rfl) c135 (compose (t := fun x => force t72 (force t577 (force t69 (force t431 (force t630 (t810 x)))))) (a := t72) (b := fun x => force t577 (force t69 (force t431 (force t630 (t810 x))))) (fun _ => rfl) c72 (compose (t := fun x => force t577 (force t69 (force t431 (force t630 (t810 x))))) (a := t577) (b := fun x => force t69 (force t431 (force t630 (t810 x)))) (fun _ => rfl) c577 (compose (t := fun x => force t69 (force t431 (force t630 (t810 x)))) (a := t69) (b := fun x => force t431 (force t630 (t810 x))) (fun _ => rfl) c69 (compose (t := fun x => force t431 (force t630 (t810 x))) (a := t431) (b := fun x => force t630 (t810 x)) (fun _ => rfl) c431 (compose (t := fun x => force t630 (t810 x)) (a := t630) (b := fun x => t810 x) (fun _ => rfl) c630 c810)))))))) x

set_option maxHeartbeats 1600000 in
private theorem point140slice0 : Residual1Cache.slice leftMap140 rightMap140 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice1 : Residual1Cache.slice leftMap140 rightMap140 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice2 : Residual1Cache.slice leftMap140 rightMap140 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice3 : Residual1Cache.slice leftMap140 rightMap140 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice4 : Residual1Cache.slice leftMap140 rightMap140 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice5 : Residual1Cache.slice leftMap140 rightMap140 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice6 : Residual1Cache.slice leftMap140 rightMap140 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice7 : Residual1Cache.slice leftMap140 rightMap140 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice8 : Residual1Cache.slice leftMap140 rightMap140 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice9 : Residual1Cache.slice leftMap140 rightMap140 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice10 : Residual1Cache.slice leftMap140 rightMap140 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice11 : Residual1Cache.slice leftMap140 rightMap140 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice12 : Residual1Cache.slice leftMap140 rightMap140 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice13 : Residual1Cache.slice leftMap140 rightMap140 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice14 : Residual1Cache.slice leftMap140 rightMap140 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice15 : Residual1Cache.slice leftMap140 rightMap140 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice16 : Residual1Cache.slice leftMap140 rightMap140 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice17 : Residual1Cache.slice leftMap140 rightMap140 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice18 : Residual1Cache.slice leftMap140 rightMap140 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice19 : Residual1Cache.slice leftMap140 rightMap140 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice20 : Residual1Cache.slice leftMap140 rightMap140 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice21 : Residual1Cache.slice leftMap140 rightMap140 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice22 : Residual1Cache.slice leftMap140 rightMap140 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice23 : Residual1Cache.slice leftMap140 rightMap140 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice24 : Residual1Cache.slice leftMap140 rightMap140 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice25 : Residual1Cache.slice leftMap140 rightMap140 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice26 : Residual1Cache.slice leftMap140 rightMap140 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice27 : Residual1Cache.slice leftMap140 rightMap140 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice28 : Residual1Cache.slice leftMap140 rightMap140 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice29 : Residual1Cache.slice leftMap140 rightMap140 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice30 : Residual1Cache.slice leftMap140 rightMap140 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice31 : Residual1Cache.slice leftMap140 rightMap140 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice32 : Residual1Cache.slice leftMap140 rightMap140 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice33 : Residual1Cache.slice leftMap140 rightMap140 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice34 : Residual1Cache.slice leftMap140 rightMap140 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice35 : Residual1Cache.slice leftMap140 rightMap140 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice36 : Residual1Cache.slice leftMap140 rightMap140 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice37 : Residual1Cache.slice leftMap140 rightMap140 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice38 : Residual1Cache.slice leftMap140 rightMap140 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice39 : Residual1Cache.slice leftMap140 rightMap140 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice40 : Residual1Cache.slice leftMap140 rightMap140 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice41 : Residual1Cache.slice leftMap140 rightMap140 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice42 : Residual1Cache.slice leftMap140 rightMap140 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice43 : Residual1Cache.slice leftMap140 rightMap140 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice44 : Residual1Cache.slice leftMap140 rightMap140 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice45 : Residual1Cache.slice leftMap140 rightMap140 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice46 : Residual1Cache.slice leftMap140 rightMap140 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice47 : Residual1Cache.slice leftMap140 rightMap140 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice48 : Residual1Cache.slice leftMap140 rightMap140 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice49 : Residual1Cache.slice leftMap140 rightMap140 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice50 : Residual1Cache.slice leftMap140 rightMap140 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice51 : Residual1Cache.slice leftMap140 rightMap140 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice52 : Residual1Cache.slice leftMap140 rightMap140 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice53 : Residual1Cache.slice leftMap140 rightMap140 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice54 : Residual1Cache.slice leftMap140 rightMap140 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice55 : Residual1Cache.slice leftMap140 rightMap140 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice56 : Residual1Cache.slice leftMap140 rightMap140 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice57 : Residual1Cache.slice leftMap140 rightMap140 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice58 : Residual1Cache.slice leftMap140 rightMap140 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice59 : Residual1Cache.slice leftMap140 rightMap140 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice60 : Residual1Cache.slice leftMap140 rightMap140 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice61 : Residual1Cache.slice leftMap140 rightMap140 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice62 : Residual1Cache.slice leftMap140 rightMap140 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice63 : Residual1Cache.slice leftMap140 rightMap140 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice64 : Residual1Cache.slice leftMap140 rightMap140 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice65 : Residual1Cache.slice leftMap140 rightMap140 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice66 : Residual1Cache.slice leftMap140 rightMap140 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice67 : Residual1Cache.slice leftMap140 rightMap140 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice68 : Residual1Cache.slice leftMap140 rightMap140 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice69 : Residual1Cache.slice leftMap140 rightMap140 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice70 : Residual1Cache.slice leftMap140 rightMap140 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice71 : Residual1Cache.slice leftMap140 rightMap140 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice72 : Residual1Cache.slice leftMap140 rightMap140 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice73 : Residual1Cache.slice leftMap140 rightMap140 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice74 : Residual1Cache.slice leftMap140 rightMap140 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice75 : Residual1Cache.slice leftMap140 rightMap140 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice76 : Residual1Cache.slice leftMap140 rightMap140 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice77 : Residual1Cache.slice leftMap140 rightMap140 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice78 : Residual1Cache.slice leftMap140 rightMap140 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice79 : Residual1Cache.slice leftMap140 rightMap140 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice80 : Residual1Cache.slice leftMap140 rightMap140 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice81 : Residual1Cache.slice leftMap140 rightMap140 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice82 : Residual1Cache.slice leftMap140 rightMap140 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice83 : Residual1Cache.slice leftMap140 rightMap140 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice84 : Residual1Cache.slice leftMap140 rightMap140 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice85 : Residual1Cache.slice leftMap140 rightMap140 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice86 : Residual1Cache.slice leftMap140 rightMap140 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice87 : Residual1Cache.slice leftMap140 rightMap140 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice88 : Residual1Cache.slice leftMap140 rightMap140 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice89 : Residual1Cache.slice leftMap140 rightMap140 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice90 : Residual1Cache.slice leftMap140 rightMap140 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice91 : Residual1Cache.slice leftMap140 rightMap140 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice92 : Residual1Cache.slice leftMap140 rightMap140 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice93 : Residual1Cache.slice leftMap140 rightMap140 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice94 : Residual1Cache.slice leftMap140 rightMap140 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice95 : Residual1Cache.slice leftMap140 rightMap140 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice96 : Residual1Cache.slice leftMap140 rightMap140 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice97 : Residual1Cache.slice leftMap140 rightMap140 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice98 : Residual1Cache.slice leftMap140 rightMap140 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice99 : Residual1Cache.slice leftMap140 rightMap140 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice100 : Residual1Cache.slice leftMap140 rightMap140 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice101 : Residual1Cache.slice leftMap140 rightMap140 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice102 : Residual1Cache.slice leftMap140 rightMap140 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice103 : Residual1Cache.slice leftMap140 rightMap140 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice104 : Residual1Cache.slice leftMap140 rightMap140 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice105 : Residual1Cache.slice leftMap140 rightMap140 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice106 : Residual1Cache.slice leftMap140 rightMap140 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice107 : Residual1Cache.slice leftMap140 rightMap140 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice108 : Residual1Cache.slice leftMap140 rightMap140 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice109 : Residual1Cache.slice leftMap140 rightMap140 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice110 : Residual1Cache.slice leftMap140 rightMap140 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice111 : Residual1Cache.slice leftMap140 rightMap140 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice112 : Residual1Cache.slice leftMap140 rightMap140 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice113 : Residual1Cache.slice leftMap140 rightMap140 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice114 : Residual1Cache.slice leftMap140 rightMap140 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice115 : Residual1Cache.slice leftMap140 rightMap140 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice116 : Residual1Cache.slice leftMap140 rightMap140 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice117 : Residual1Cache.slice leftMap140 rightMap140 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice118 : Residual1Cache.slice leftMap140 rightMap140 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice119 : Residual1Cache.slice leftMap140 rightMap140 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice120 : Residual1Cache.slice leftMap140 rightMap140 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice121 : Residual1Cache.slice leftMap140 rightMap140 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice122 : Residual1Cache.slice leftMap140 rightMap140 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice123 : Residual1Cache.slice leftMap140 rightMap140 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice124 : Residual1Cache.slice leftMap140 rightMap140 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice125 : Residual1Cache.slice leftMap140 rightMap140 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice126 : Residual1Cache.slice leftMap140 rightMap140 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice127 : Residual1Cache.slice leftMap140 rightMap140 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice128 : Residual1Cache.slice leftMap140 rightMap140 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice129 : Residual1Cache.slice leftMap140 rightMap140 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice130 : Residual1Cache.slice leftMap140 rightMap140 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice131 : Residual1Cache.slice leftMap140 rightMap140 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice132 : Residual1Cache.slice leftMap140 rightMap140 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice133 : Residual1Cache.slice leftMap140 rightMap140 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice134 : Residual1Cache.slice leftMap140 rightMap140 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice135 : Residual1Cache.slice leftMap140 rightMap140 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice136 : Residual1Cache.slice leftMap140 rightMap140 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice137 : Residual1Cache.slice leftMap140 rightMap140 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice138 : Residual1Cache.slice leftMap140 rightMap140 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice139 : Residual1Cache.slice leftMap140 rightMap140 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice140 : Residual1Cache.slice leftMap140 rightMap140 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice141 : Residual1Cache.slice leftMap140 rightMap140 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice142 : Residual1Cache.slice leftMap140 rightMap140 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice143 : Residual1Cache.slice leftMap140 rightMap140 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice144 : Residual1Cache.slice leftMap140 rightMap140 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice145 : Residual1Cache.slice leftMap140 rightMap140 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice146 : Residual1Cache.slice leftMap140 rightMap140 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice147 : Residual1Cache.slice leftMap140 rightMap140 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice148 : Residual1Cache.slice leftMap140 rightMap140 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice149 : Residual1Cache.slice leftMap140 rightMap140 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice150 : Residual1Cache.slice leftMap140 rightMap140 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice151 : Residual1Cache.slice leftMap140 rightMap140 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice152 : Residual1Cache.slice leftMap140 rightMap140 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice153 : Residual1Cache.slice leftMap140 rightMap140 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice154 : Residual1Cache.slice leftMap140 rightMap140 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice155 : Residual1Cache.slice leftMap140 rightMap140 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice156 : Residual1Cache.slice leftMap140 rightMap140 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice157 : Residual1Cache.slice leftMap140 rightMap140 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice158 : Residual1Cache.slice leftMap140 rightMap140 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice159 : Residual1Cache.slice leftMap140 rightMap140 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice160 : Residual1Cache.slice leftMap140 rightMap140 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice161 : Residual1Cache.slice leftMap140 rightMap140 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice162 : Residual1Cache.slice leftMap140 rightMap140 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice163 : Residual1Cache.slice leftMap140 rightMap140 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice164 : Residual1Cache.slice leftMap140 rightMap140 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice165 : Residual1Cache.slice leftMap140 rightMap140 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice166 : Residual1Cache.slice leftMap140 rightMap140 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice167 : Residual1Cache.slice leftMap140 rightMap140 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice168 : Residual1Cache.slice leftMap140 rightMap140 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice169 : Residual1Cache.slice leftMap140 rightMap140 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice170 : Residual1Cache.slice leftMap140 rightMap140 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice171 : Residual1Cache.slice leftMap140 rightMap140 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice172 : Residual1Cache.slice leftMap140 rightMap140 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice173 : Residual1Cache.slice leftMap140 rightMap140 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice174 : Residual1Cache.slice leftMap140 rightMap140 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice175 : Residual1Cache.slice leftMap140 rightMap140 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice176 : Residual1Cache.slice leftMap140 rightMap140 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice177 : Residual1Cache.slice leftMap140 rightMap140 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice178 : Residual1Cache.slice leftMap140 rightMap140 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice179 : Residual1Cache.slice leftMap140 rightMap140 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice180 : Residual1Cache.slice leftMap140 rightMap140 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice181 : Residual1Cache.slice leftMap140 rightMap140 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice182 : Residual1Cache.slice leftMap140 rightMap140 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice183 : Residual1Cache.slice leftMap140 rightMap140 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice184 : Residual1Cache.slice leftMap140 rightMap140 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice185 : Residual1Cache.slice leftMap140 rightMap140 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice186 : Residual1Cache.slice leftMap140 rightMap140 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice187 : Residual1Cache.slice leftMap140 rightMap140 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice188 : Residual1Cache.slice leftMap140 rightMap140 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice189 : Residual1Cache.slice leftMap140 rightMap140 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice190 : Residual1Cache.slice leftMap140 rightMap140 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice191 : Residual1Cache.slice leftMap140 rightMap140 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice192 : Residual1Cache.slice leftMap140 rightMap140 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice193 : Residual1Cache.slice leftMap140 rightMap140 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice194 : Residual1Cache.slice leftMap140 rightMap140 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice195 : Residual1Cache.slice leftMap140 rightMap140 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice196 : Residual1Cache.slice leftMap140 rightMap140 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice197 : Residual1Cache.slice leftMap140 rightMap140 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice198 : Residual1Cache.slice leftMap140 rightMap140 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice199 : Residual1Cache.slice leftMap140 rightMap140 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice200 : Residual1Cache.slice leftMap140 rightMap140 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice201 : Residual1Cache.slice leftMap140 rightMap140 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point140slice202 : Residual1Cache.slice leftMap140 rightMap140 202 = true := by
  decide +kernel

private theorem point140_slices : ∀ c, Residual1Cache.slice leftMap140 rightMap140 c = true := by
  intro c
  fin_cases c
  · exact point140slice0
  · exact point140slice1
  · exact point140slice2
  · exact point140slice3
  · exact point140slice4
  · exact point140slice5
  · exact point140slice6
  · exact point140slice7
  · exact point140slice8
  · exact point140slice9
  · exact point140slice10
  · exact point140slice11
  · exact point140slice12
  · exact point140slice13
  · exact point140slice14
  · exact point140slice15
  · exact point140slice16
  · exact point140slice17
  · exact point140slice18
  · exact point140slice19
  · exact point140slice20
  · exact point140slice21
  · exact point140slice22
  · exact point140slice23
  · exact point140slice24
  · exact point140slice25
  · exact point140slice26
  · exact point140slice27
  · exact point140slice28
  · exact point140slice29
  · exact point140slice30
  · exact point140slice31
  · exact point140slice32
  · exact point140slice33
  · exact point140slice34
  · exact point140slice35
  · exact point140slice36
  · exact point140slice37
  · exact point140slice38
  · exact point140slice39
  · exact point140slice40
  · exact point140slice41
  · exact point140slice42
  · exact point140slice43
  · exact point140slice44
  · exact point140slice45
  · exact point140slice46
  · exact point140slice47
  · exact point140slice48
  · exact point140slice49
  · exact point140slice50
  · exact point140slice51
  · exact point140slice52
  · exact point140slice53
  · exact point140slice54
  · exact point140slice55
  · exact point140slice56
  · exact point140slice57
  · exact point140slice58
  · exact point140slice59
  · exact point140slice60
  · exact point140slice61
  · exact point140slice62
  · exact point140slice63
  · exact point140slice64
  · exact point140slice65
  · exact point140slice66
  · exact point140slice67
  · exact point140slice68
  · exact point140slice69
  · exact point140slice70
  · exact point140slice71
  · exact point140slice72
  · exact point140slice73
  · exact point140slice74
  · exact point140slice75
  · exact point140slice76
  · exact point140slice77
  · exact point140slice78
  · exact point140slice79
  · exact point140slice80
  · exact point140slice81
  · exact point140slice82
  · exact point140slice83
  · exact point140slice84
  · exact point140slice85
  · exact point140slice86
  · exact point140slice87
  · exact point140slice88
  · exact point140slice89
  · exact point140slice90
  · exact point140slice91
  · exact point140slice92
  · exact point140slice93
  · exact point140slice94
  · exact point140slice95
  · exact point140slice96
  · exact point140slice97
  · exact point140slice98
  · exact point140slice99
  · exact point140slice100
  · exact point140slice101
  · exact point140slice102
  · exact point140slice103
  · exact point140slice104
  · exact point140slice105
  · exact point140slice106
  · exact point140slice107
  · exact point140slice108
  · exact point140slice109
  · exact point140slice110
  · exact point140slice111
  · exact point140slice112
  · exact point140slice113
  · exact point140slice114
  · exact point140slice115
  · exact point140slice116
  · exact point140slice117
  · exact point140slice118
  · exact point140slice119
  · exact point140slice120
  · exact point140slice121
  · exact point140slice122
  · exact point140slice123
  · exact point140slice124
  · exact point140slice125
  · exact point140slice126
  · exact point140slice127
  · exact point140slice128
  · exact point140slice129
  · exact point140slice130
  · exact point140slice131
  · exact point140slice132
  · exact point140slice133
  · exact point140slice134
  · exact point140slice135
  · exact point140slice136
  · exact point140slice137
  · exact point140slice138
  · exact point140slice139
  · exact point140slice140
  · exact point140slice141
  · exact point140slice142
  · exact point140slice143
  · exact point140slice144
  · exact point140slice145
  · exact point140slice146
  · exact point140slice147
  · exact point140slice148
  · exact point140slice149
  · exact point140slice150
  · exact point140slice151
  · exact point140slice152
  · exact point140slice153
  · exact point140slice154
  · exact point140slice155
  · exact point140slice156
  · exact point140slice157
  · exact point140slice158
  · exact point140slice159
  · exact point140slice160
  · exact point140slice161
  · exact point140slice162
  · exact point140slice163
  · exact point140slice164
  · exact point140slice165
  · exact point140slice166
  · exact point140slice167
  · exact point140slice168
  · exact point140slice169
  · exact point140slice170
  · exact point140slice171
  · exact point140slice172
  · exact point140slice173
  · exact point140slice174
  · exact point140slice175
  · exact point140slice176
  · exact point140slice177
  · exact point140slice178
  · exact point140slice179
  · exact point140slice180
  · exact point140slice181
  · exact point140slice182
  · exact point140slice183
  · exact point140slice184
  · exact point140slice185
  · exact point140slice186
  · exact point140slice187
  · exact point140slice188
  · exact point140slice189
  · exact point140slice190
  · exact point140slice191
  · exact point140slice192
  · exact point140slice193
  · exact point140slice194
  · exact point140slice195
  · exact point140slice196
  · exact point140slice197
  · exact point140slice198
  · exact point140slice199
  · exact point140slice200
  · exact point140slice201
  · exact point140slice202

set_option maxHeartbeats 1600000 in
public theorem point140 : stepCheck 0 2849 := by
  have hleft : L0Gen 0 * L0Rep 2849 = leftPerm140 := by
    change L0Gen 0 * evalWord L0Gen [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0] = leftPerm140
    simp only [leftPerm140, p252, p93, p62, p53, p30, p20, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2849) * evalWord L1Gen (L0Factor 0 2849) = rightPerm140 := by
    change evalWord L0Gen [1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3] * evalWord L1Gen [3, 2, 1, 0, 1, 2, 1, 0, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm140
    simp only [rightPerm140, p908, p810, p630, p577, p431, p430, p259, p220, p135, p128, p115, p111, p96, p72, p69, p57, p52, p47, p46, p44, p43, p42, p39, p38, p37, p36, p35, p34, p32, p31, p29, p28, p27, p26, p25, p24, p23, p22, p21, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2849) x =
    (L0Rep (L0Act 0 2849) * evalWord L1Gen (L0Factor 0 2849)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap140_eq, ← rightMap140_eq]
  exact Residual1Cache.ofSlices point140_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
