module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level14Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 137

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap137 (x : Nat) : Nat := force t284 (t53 x)
private def leftPerm137 : Equiv.Perm (Fin 4060) := p284 * (p53)
private theorem leftMap137_eq (x : Fin 4060) :
    leftMap137 x.val = (leftPerm137 x).val := (compose (t := fun x => force t284 (t53 x)) (a := t284) (b := fun x => t53 x) (fun _ => rfl) c284 c53) x

private def rightMap137 (x : Nat) : Nat := force t115 (force t91 (force t89 (force t403 (t407 x))))
private def rightPerm137 : Equiv.Perm (Fin 4060) := p115 * (p91 * (p89 * (p403 * (p407))))
private theorem rightMap137_eq (x : Fin 4060) :
    rightMap137 x.val = (rightPerm137 x).val := (compose (t := fun x => force t115 (force t91 (force t89 (force t403 (t407 x))))) (a := t115) (b := fun x => force t91 (force t89 (force t403 (t407 x)))) (fun _ => rfl) c115 (compose (t := fun x => force t91 (force t89 (force t403 (t407 x)))) (a := t91) (b := fun x => force t89 (force t403 (t407 x))) (fun _ => rfl) c91 (compose (t := fun x => force t89 (force t403 (t407 x))) (a := t89) (b := fun x => force t403 (t407 x)) (fun _ => rfl) c89 (compose (t := fun x => force t403 (t407 x)) (a := t403) (b := fun x => t407 x) (fun _ => rfl) c403 c407)))) x

set_option maxHeartbeats 1600000 in
private theorem point137slice0 : Residual1Cache.slice leftMap137 rightMap137 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice1 : Residual1Cache.slice leftMap137 rightMap137 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice2 : Residual1Cache.slice leftMap137 rightMap137 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice3 : Residual1Cache.slice leftMap137 rightMap137 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice4 : Residual1Cache.slice leftMap137 rightMap137 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice5 : Residual1Cache.slice leftMap137 rightMap137 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice6 : Residual1Cache.slice leftMap137 rightMap137 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice7 : Residual1Cache.slice leftMap137 rightMap137 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice8 : Residual1Cache.slice leftMap137 rightMap137 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice9 : Residual1Cache.slice leftMap137 rightMap137 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice10 : Residual1Cache.slice leftMap137 rightMap137 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice11 : Residual1Cache.slice leftMap137 rightMap137 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice12 : Residual1Cache.slice leftMap137 rightMap137 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice13 : Residual1Cache.slice leftMap137 rightMap137 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice14 : Residual1Cache.slice leftMap137 rightMap137 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice15 : Residual1Cache.slice leftMap137 rightMap137 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice16 : Residual1Cache.slice leftMap137 rightMap137 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice17 : Residual1Cache.slice leftMap137 rightMap137 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice18 : Residual1Cache.slice leftMap137 rightMap137 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice19 : Residual1Cache.slice leftMap137 rightMap137 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice20 : Residual1Cache.slice leftMap137 rightMap137 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice21 : Residual1Cache.slice leftMap137 rightMap137 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice22 : Residual1Cache.slice leftMap137 rightMap137 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice23 : Residual1Cache.slice leftMap137 rightMap137 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice24 : Residual1Cache.slice leftMap137 rightMap137 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice25 : Residual1Cache.slice leftMap137 rightMap137 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice26 : Residual1Cache.slice leftMap137 rightMap137 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice27 : Residual1Cache.slice leftMap137 rightMap137 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice28 : Residual1Cache.slice leftMap137 rightMap137 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice29 : Residual1Cache.slice leftMap137 rightMap137 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice30 : Residual1Cache.slice leftMap137 rightMap137 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice31 : Residual1Cache.slice leftMap137 rightMap137 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice32 : Residual1Cache.slice leftMap137 rightMap137 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice33 : Residual1Cache.slice leftMap137 rightMap137 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice34 : Residual1Cache.slice leftMap137 rightMap137 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice35 : Residual1Cache.slice leftMap137 rightMap137 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice36 : Residual1Cache.slice leftMap137 rightMap137 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice37 : Residual1Cache.slice leftMap137 rightMap137 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice38 : Residual1Cache.slice leftMap137 rightMap137 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice39 : Residual1Cache.slice leftMap137 rightMap137 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice40 : Residual1Cache.slice leftMap137 rightMap137 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice41 : Residual1Cache.slice leftMap137 rightMap137 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice42 : Residual1Cache.slice leftMap137 rightMap137 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice43 : Residual1Cache.slice leftMap137 rightMap137 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice44 : Residual1Cache.slice leftMap137 rightMap137 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice45 : Residual1Cache.slice leftMap137 rightMap137 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice46 : Residual1Cache.slice leftMap137 rightMap137 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice47 : Residual1Cache.slice leftMap137 rightMap137 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice48 : Residual1Cache.slice leftMap137 rightMap137 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice49 : Residual1Cache.slice leftMap137 rightMap137 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice50 : Residual1Cache.slice leftMap137 rightMap137 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice51 : Residual1Cache.slice leftMap137 rightMap137 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice52 : Residual1Cache.slice leftMap137 rightMap137 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice53 : Residual1Cache.slice leftMap137 rightMap137 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice54 : Residual1Cache.slice leftMap137 rightMap137 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice55 : Residual1Cache.slice leftMap137 rightMap137 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice56 : Residual1Cache.slice leftMap137 rightMap137 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice57 : Residual1Cache.slice leftMap137 rightMap137 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice58 : Residual1Cache.slice leftMap137 rightMap137 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice59 : Residual1Cache.slice leftMap137 rightMap137 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice60 : Residual1Cache.slice leftMap137 rightMap137 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice61 : Residual1Cache.slice leftMap137 rightMap137 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice62 : Residual1Cache.slice leftMap137 rightMap137 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice63 : Residual1Cache.slice leftMap137 rightMap137 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice64 : Residual1Cache.slice leftMap137 rightMap137 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice65 : Residual1Cache.slice leftMap137 rightMap137 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice66 : Residual1Cache.slice leftMap137 rightMap137 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice67 : Residual1Cache.slice leftMap137 rightMap137 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice68 : Residual1Cache.slice leftMap137 rightMap137 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice69 : Residual1Cache.slice leftMap137 rightMap137 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice70 : Residual1Cache.slice leftMap137 rightMap137 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice71 : Residual1Cache.slice leftMap137 rightMap137 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice72 : Residual1Cache.slice leftMap137 rightMap137 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice73 : Residual1Cache.slice leftMap137 rightMap137 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice74 : Residual1Cache.slice leftMap137 rightMap137 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice75 : Residual1Cache.slice leftMap137 rightMap137 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice76 : Residual1Cache.slice leftMap137 rightMap137 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice77 : Residual1Cache.slice leftMap137 rightMap137 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice78 : Residual1Cache.slice leftMap137 rightMap137 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice79 : Residual1Cache.slice leftMap137 rightMap137 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice80 : Residual1Cache.slice leftMap137 rightMap137 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice81 : Residual1Cache.slice leftMap137 rightMap137 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice82 : Residual1Cache.slice leftMap137 rightMap137 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice83 : Residual1Cache.slice leftMap137 rightMap137 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice84 : Residual1Cache.slice leftMap137 rightMap137 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice85 : Residual1Cache.slice leftMap137 rightMap137 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice86 : Residual1Cache.slice leftMap137 rightMap137 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice87 : Residual1Cache.slice leftMap137 rightMap137 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice88 : Residual1Cache.slice leftMap137 rightMap137 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice89 : Residual1Cache.slice leftMap137 rightMap137 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice90 : Residual1Cache.slice leftMap137 rightMap137 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice91 : Residual1Cache.slice leftMap137 rightMap137 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice92 : Residual1Cache.slice leftMap137 rightMap137 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice93 : Residual1Cache.slice leftMap137 rightMap137 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice94 : Residual1Cache.slice leftMap137 rightMap137 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice95 : Residual1Cache.slice leftMap137 rightMap137 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice96 : Residual1Cache.slice leftMap137 rightMap137 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice97 : Residual1Cache.slice leftMap137 rightMap137 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice98 : Residual1Cache.slice leftMap137 rightMap137 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice99 : Residual1Cache.slice leftMap137 rightMap137 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice100 : Residual1Cache.slice leftMap137 rightMap137 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice101 : Residual1Cache.slice leftMap137 rightMap137 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice102 : Residual1Cache.slice leftMap137 rightMap137 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice103 : Residual1Cache.slice leftMap137 rightMap137 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice104 : Residual1Cache.slice leftMap137 rightMap137 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice105 : Residual1Cache.slice leftMap137 rightMap137 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice106 : Residual1Cache.slice leftMap137 rightMap137 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice107 : Residual1Cache.slice leftMap137 rightMap137 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice108 : Residual1Cache.slice leftMap137 rightMap137 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice109 : Residual1Cache.slice leftMap137 rightMap137 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice110 : Residual1Cache.slice leftMap137 rightMap137 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice111 : Residual1Cache.slice leftMap137 rightMap137 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice112 : Residual1Cache.slice leftMap137 rightMap137 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice113 : Residual1Cache.slice leftMap137 rightMap137 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice114 : Residual1Cache.slice leftMap137 rightMap137 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice115 : Residual1Cache.slice leftMap137 rightMap137 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice116 : Residual1Cache.slice leftMap137 rightMap137 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice117 : Residual1Cache.slice leftMap137 rightMap137 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice118 : Residual1Cache.slice leftMap137 rightMap137 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice119 : Residual1Cache.slice leftMap137 rightMap137 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice120 : Residual1Cache.slice leftMap137 rightMap137 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice121 : Residual1Cache.slice leftMap137 rightMap137 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice122 : Residual1Cache.slice leftMap137 rightMap137 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice123 : Residual1Cache.slice leftMap137 rightMap137 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice124 : Residual1Cache.slice leftMap137 rightMap137 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice125 : Residual1Cache.slice leftMap137 rightMap137 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice126 : Residual1Cache.slice leftMap137 rightMap137 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice127 : Residual1Cache.slice leftMap137 rightMap137 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice128 : Residual1Cache.slice leftMap137 rightMap137 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice129 : Residual1Cache.slice leftMap137 rightMap137 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice130 : Residual1Cache.slice leftMap137 rightMap137 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice131 : Residual1Cache.slice leftMap137 rightMap137 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice132 : Residual1Cache.slice leftMap137 rightMap137 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice133 : Residual1Cache.slice leftMap137 rightMap137 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice134 : Residual1Cache.slice leftMap137 rightMap137 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice135 : Residual1Cache.slice leftMap137 rightMap137 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice136 : Residual1Cache.slice leftMap137 rightMap137 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice137 : Residual1Cache.slice leftMap137 rightMap137 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice138 : Residual1Cache.slice leftMap137 rightMap137 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice139 : Residual1Cache.slice leftMap137 rightMap137 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice140 : Residual1Cache.slice leftMap137 rightMap137 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice141 : Residual1Cache.slice leftMap137 rightMap137 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice142 : Residual1Cache.slice leftMap137 rightMap137 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice143 : Residual1Cache.slice leftMap137 rightMap137 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice144 : Residual1Cache.slice leftMap137 rightMap137 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice145 : Residual1Cache.slice leftMap137 rightMap137 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice146 : Residual1Cache.slice leftMap137 rightMap137 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice147 : Residual1Cache.slice leftMap137 rightMap137 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice148 : Residual1Cache.slice leftMap137 rightMap137 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice149 : Residual1Cache.slice leftMap137 rightMap137 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice150 : Residual1Cache.slice leftMap137 rightMap137 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice151 : Residual1Cache.slice leftMap137 rightMap137 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice152 : Residual1Cache.slice leftMap137 rightMap137 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice153 : Residual1Cache.slice leftMap137 rightMap137 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice154 : Residual1Cache.slice leftMap137 rightMap137 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice155 : Residual1Cache.slice leftMap137 rightMap137 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice156 : Residual1Cache.slice leftMap137 rightMap137 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice157 : Residual1Cache.slice leftMap137 rightMap137 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice158 : Residual1Cache.slice leftMap137 rightMap137 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice159 : Residual1Cache.slice leftMap137 rightMap137 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice160 : Residual1Cache.slice leftMap137 rightMap137 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice161 : Residual1Cache.slice leftMap137 rightMap137 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice162 : Residual1Cache.slice leftMap137 rightMap137 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice163 : Residual1Cache.slice leftMap137 rightMap137 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice164 : Residual1Cache.slice leftMap137 rightMap137 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice165 : Residual1Cache.slice leftMap137 rightMap137 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice166 : Residual1Cache.slice leftMap137 rightMap137 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice167 : Residual1Cache.slice leftMap137 rightMap137 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice168 : Residual1Cache.slice leftMap137 rightMap137 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice169 : Residual1Cache.slice leftMap137 rightMap137 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice170 : Residual1Cache.slice leftMap137 rightMap137 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice171 : Residual1Cache.slice leftMap137 rightMap137 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice172 : Residual1Cache.slice leftMap137 rightMap137 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice173 : Residual1Cache.slice leftMap137 rightMap137 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice174 : Residual1Cache.slice leftMap137 rightMap137 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice175 : Residual1Cache.slice leftMap137 rightMap137 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice176 : Residual1Cache.slice leftMap137 rightMap137 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice177 : Residual1Cache.slice leftMap137 rightMap137 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice178 : Residual1Cache.slice leftMap137 rightMap137 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice179 : Residual1Cache.slice leftMap137 rightMap137 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice180 : Residual1Cache.slice leftMap137 rightMap137 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice181 : Residual1Cache.slice leftMap137 rightMap137 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice182 : Residual1Cache.slice leftMap137 rightMap137 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice183 : Residual1Cache.slice leftMap137 rightMap137 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice184 : Residual1Cache.slice leftMap137 rightMap137 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice185 : Residual1Cache.slice leftMap137 rightMap137 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice186 : Residual1Cache.slice leftMap137 rightMap137 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice187 : Residual1Cache.slice leftMap137 rightMap137 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice188 : Residual1Cache.slice leftMap137 rightMap137 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice189 : Residual1Cache.slice leftMap137 rightMap137 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice190 : Residual1Cache.slice leftMap137 rightMap137 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice191 : Residual1Cache.slice leftMap137 rightMap137 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice192 : Residual1Cache.slice leftMap137 rightMap137 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice193 : Residual1Cache.slice leftMap137 rightMap137 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice194 : Residual1Cache.slice leftMap137 rightMap137 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice195 : Residual1Cache.slice leftMap137 rightMap137 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice196 : Residual1Cache.slice leftMap137 rightMap137 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice197 : Residual1Cache.slice leftMap137 rightMap137 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice198 : Residual1Cache.slice leftMap137 rightMap137 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice199 : Residual1Cache.slice leftMap137 rightMap137 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice200 : Residual1Cache.slice leftMap137 rightMap137 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice201 : Residual1Cache.slice leftMap137 rightMap137 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point137slice202 : Residual1Cache.slice leftMap137 rightMap137 202 = true := by
  decide +kernel

private theorem point137_slices : ∀ c, Residual1Cache.slice leftMap137 rightMap137 c = true := by
  intro c
  fin_cases c
  · exact point137slice0
  · exact point137slice1
  · exact point137slice2
  · exact point137slice3
  · exact point137slice4
  · exact point137slice5
  · exact point137slice6
  · exact point137slice7
  · exact point137slice8
  · exact point137slice9
  · exact point137slice10
  · exact point137slice11
  · exact point137slice12
  · exact point137slice13
  · exact point137slice14
  · exact point137slice15
  · exact point137slice16
  · exact point137slice17
  · exact point137slice18
  · exact point137slice19
  · exact point137slice20
  · exact point137slice21
  · exact point137slice22
  · exact point137slice23
  · exact point137slice24
  · exact point137slice25
  · exact point137slice26
  · exact point137slice27
  · exact point137slice28
  · exact point137slice29
  · exact point137slice30
  · exact point137slice31
  · exact point137slice32
  · exact point137slice33
  · exact point137slice34
  · exact point137slice35
  · exact point137slice36
  · exact point137slice37
  · exact point137slice38
  · exact point137slice39
  · exact point137slice40
  · exact point137slice41
  · exact point137slice42
  · exact point137slice43
  · exact point137slice44
  · exact point137slice45
  · exact point137slice46
  · exact point137slice47
  · exact point137slice48
  · exact point137slice49
  · exact point137slice50
  · exact point137slice51
  · exact point137slice52
  · exact point137slice53
  · exact point137slice54
  · exact point137slice55
  · exact point137slice56
  · exact point137slice57
  · exact point137slice58
  · exact point137slice59
  · exact point137slice60
  · exact point137slice61
  · exact point137slice62
  · exact point137slice63
  · exact point137slice64
  · exact point137slice65
  · exact point137slice66
  · exact point137slice67
  · exact point137slice68
  · exact point137slice69
  · exact point137slice70
  · exact point137slice71
  · exact point137slice72
  · exact point137slice73
  · exact point137slice74
  · exact point137slice75
  · exact point137slice76
  · exact point137slice77
  · exact point137slice78
  · exact point137slice79
  · exact point137slice80
  · exact point137slice81
  · exact point137slice82
  · exact point137slice83
  · exact point137slice84
  · exact point137slice85
  · exact point137slice86
  · exact point137slice87
  · exact point137slice88
  · exact point137slice89
  · exact point137slice90
  · exact point137slice91
  · exact point137slice92
  · exact point137slice93
  · exact point137slice94
  · exact point137slice95
  · exact point137slice96
  · exact point137slice97
  · exact point137slice98
  · exact point137slice99
  · exact point137slice100
  · exact point137slice101
  · exact point137slice102
  · exact point137slice103
  · exact point137slice104
  · exact point137slice105
  · exact point137slice106
  · exact point137slice107
  · exact point137slice108
  · exact point137slice109
  · exact point137slice110
  · exact point137slice111
  · exact point137slice112
  · exact point137slice113
  · exact point137slice114
  · exact point137slice115
  · exact point137slice116
  · exact point137slice117
  · exact point137slice118
  · exact point137slice119
  · exact point137slice120
  · exact point137slice121
  · exact point137slice122
  · exact point137slice123
  · exact point137slice124
  · exact point137slice125
  · exact point137slice126
  · exact point137slice127
  · exact point137slice128
  · exact point137slice129
  · exact point137slice130
  · exact point137slice131
  · exact point137slice132
  · exact point137slice133
  · exact point137slice134
  · exact point137slice135
  · exact point137slice136
  · exact point137slice137
  · exact point137slice138
  · exact point137slice139
  · exact point137slice140
  · exact point137slice141
  · exact point137slice142
  · exact point137slice143
  · exact point137slice144
  · exact point137slice145
  · exact point137slice146
  · exact point137slice147
  · exact point137slice148
  · exact point137slice149
  · exact point137slice150
  · exact point137slice151
  · exact point137slice152
  · exact point137slice153
  · exact point137slice154
  · exact point137slice155
  · exact point137slice156
  · exact point137slice157
  · exact point137slice158
  · exact point137slice159
  · exact point137slice160
  · exact point137slice161
  · exact point137slice162
  · exact point137slice163
  · exact point137slice164
  · exact point137slice165
  · exact point137slice166
  · exact point137slice167
  · exact point137slice168
  · exact point137slice169
  · exact point137slice170
  · exact point137slice171
  · exact point137slice172
  · exact point137slice173
  · exact point137slice174
  · exact point137slice175
  · exact point137slice176
  · exact point137slice177
  · exact point137slice178
  · exact point137slice179
  · exact point137slice180
  · exact point137slice181
  · exact point137slice182
  · exact point137slice183
  · exact point137slice184
  · exact point137slice185
  · exact point137slice186
  · exact point137slice187
  · exact point137slice188
  · exact point137slice189
  · exact point137slice190
  · exact point137slice191
  · exact point137slice192
  · exact point137slice193
  · exact point137slice194
  · exact point137slice195
  · exact point137slice196
  · exact point137slice197
  · exact point137slice198
  · exact point137slice199
  · exact point137slice200
  · exact point137slice201
  · exact point137slice202

set_option maxHeartbeats 1600000 in
public theorem point137 : stepCheck 0 2841 := by
  have hleft : L0Gen 0 * L0Rep 2841 = leftPerm137 := by
    change L0Gen 0 * evalWord L0Gen [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0] = leftPerm137
    simp only [leftPerm137, p284, p124, p62, p53, p30, p20, p17, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 0 2841) * evalWord L1Gen (L0Factor 0 2841) = rightPerm137 := by
    change evalWord L0Gen [1, 0, 1, 0, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 1] * evalWord L1Gen [2, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 2, 3, 0, 3, 3, 2, 1, 1, 0, 1, 1, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 0, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0] = rightPerm137
    simp only [rightPerm137, p407, p406, p405, p403, p115, p109, p91, p89, p58, p56, p54, p51, p49, p48, p46, p45, p44, p43, p42, p41, p40, p39, p37, p36, p35, p34, p33, p32, p31, p30, p29, p28, p26, p25, p24, p23, p22, p21, p19, p18, p17, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 0 * L0Rep 2841) x =
    (L0Rep (L0Act 0 2841) * evalWord L1Gen (L0Factor 0 2841)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap137_eq, ← rightMap137_eq]
  exact Residual1Cache.ofSlices point137_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
