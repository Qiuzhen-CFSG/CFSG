module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2Residual1.Cached
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level01Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level02Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level03Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level04Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level05Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level06Part0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level07Part2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Level08Part0
import Mathlib.Tactic.FinCases

/-!
# Rudvalis part-2 residual transition 127

The original words are regrouped into previously certified products from
`OrderLevel0Part6Block2`. Their lookup functions are compared in 203 slices
of twenty points, each checked by the kernel. Source: `OrderLevel0Data`,
`Part2Residual.target`, and the cached products' ATLAS source witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
open Part6Block2.Cache Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private def leftMap127 (x : Nat) : Nat := force t236 (force t50 (t48 x))
private def leftPerm127 : Equiv.Perm (Fin 4060) := p236 * (p50 * (p48))
private theorem leftMap127_eq (x : Fin 4060) :
    leftMap127 x.val = (leftPerm127 x).val := (compose (t := fun x => force t236 (force t50 (t48 x))) (a := t236) (b := fun x => force t50 (t48 x)) (fun _ => rfl) c236 (compose (t := fun x => force t50 (t48 x)) (a := t50) (b := fun x => t48 x) (fun _ => rfl) c50 c48)) x

private def rightMap127 (x : Nat) : Nat := force t982 (force t86 (force t11 (force t10 (force t276 (force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x)))))))))))))
private def rightPerm127 : Equiv.Perm (Fin 4060) := p982 * (p86 * (p11 * (p10 * (p276 * (p55 * (p74 * (p19 * (p857 * (p259 * (p69 * (p6 * (p6 * (p66)))))))))))))
private theorem rightMap127_eq (x : Fin 4060) :
    rightMap127 x.val = (rightPerm127 x).val := (compose (t := fun x => force t982 (force t86 (force t11 (force t10 (force t276 (force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x)))))))))))))) (a := t982) (b := fun x => force t86 (force t11 (force t10 (force t276 (force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x))))))))))))) (fun _ => rfl) c982 (compose (t := fun x => force t86 (force t11 (force t10 (force t276 (force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x))))))))))))) (a := t86) (b := fun x => force t11 (force t10 (force t276 (force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x)))))))))))) (fun _ => rfl) c86 (compose (t := fun x => force t11 (force t10 (force t276 (force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x)))))))))))) (a := t11) (b := fun x => force t10 (force t276 (force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x))))))))))) (fun _ => rfl) c11 (compose (t := fun x => force t10 (force t276 (force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x))))))))))) (a := t10) (b := fun x => force t276 (force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x)))))))))) (fun _ => rfl) c10 (compose (t := fun x => force t276 (force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x)))))))))) (a := t276) (b := fun x => force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x))))))))) (fun _ => rfl) c276 (compose (t := fun x => force t55 (force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x))))))))) (a := t55) (b := fun x => force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x)))))))) (fun _ => rfl) c55 (compose (t := fun x => force t74 (force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x)))))))) (a := t74) (b := fun x => force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x))))))) (fun _ => rfl) c74 (compose (t := fun x => force t19 (force t857 (force t259 (force t69 (force t6 (force t6 (t66 x))))))) (a := t19) (b := fun x => force t857 (force t259 (force t69 (force t6 (force t6 (t66 x)))))) (fun _ => rfl) c19 (compose (t := fun x => force t857 (force t259 (force t69 (force t6 (force t6 (t66 x)))))) (a := t857) (b := fun x => force t259 (force t69 (force t6 (force t6 (t66 x))))) (fun _ => rfl) c857 (compose (t := fun x => force t259 (force t69 (force t6 (force t6 (t66 x))))) (a := t259) (b := fun x => force t69 (force t6 (force t6 (t66 x)))) (fun _ => rfl) c259 (compose (t := fun x => force t69 (force t6 (force t6 (t66 x)))) (a := t69) (b := fun x => force t6 (force t6 (t66 x))) (fun _ => rfl) c69 (compose (t := fun x => force t6 (force t6 (t66 x))) (a := t6) (b := fun x => force t6 (t66 x)) (fun _ => rfl) c6 (compose (t := fun x => force t6 (t66 x)) (a := t6) (b := fun x => t66 x) (fun _ => rfl) c6 c66))))))))))))) x

set_option maxHeartbeats 1600000 in
private theorem point127slice0 : Residual1Cache.slice leftMap127 rightMap127 0 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice1 : Residual1Cache.slice leftMap127 rightMap127 1 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice2 : Residual1Cache.slice leftMap127 rightMap127 2 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice3 : Residual1Cache.slice leftMap127 rightMap127 3 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice4 : Residual1Cache.slice leftMap127 rightMap127 4 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice5 : Residual1Cache.slice leftMap127 rightMap127 5 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice6 : Residual1Cache.slice leftMap127 rightMap127 6 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice7 : Residual1Cache.slice leftMap127 rightMap127 7 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice8 : Residual1Cache.slice leftMap127 rightMap127 8 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice9 : Residual1Cache.slice leftMap127 rightMap127 9 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice10 : Residual1Cache.slice leftMap127 rightMap127 10 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice11 : Residual1Cache.slice leftMap127 rightMap127 11 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice12 : Residual1Cache.slice leftMap127 rightMap127 12 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice13 : Residual1Cache.slice leftMap127 rightMap127 13 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice14 : Residual1Cache.slice leftMap127 rightMap127 14 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice15 : Residual1Cache.slice leftMap127 rightMap127 15 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice16 : Residual1Cache.slice leftMap127 rightMap127 16 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice17 : Residual1Cache.slice leftMap127 rightMap127 17 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice18 : Residual1Cache.slice leftMap127 rightMap127 18 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice19 : Residual1Cache.slice leftMap127 rightMap127 19 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice20 : Residual1Cache.slice leftMap127 rightMap127 20 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice21 : Residual1Cache.slice leftMap127 rightMap127 21 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice22 : Residual1Cache.slice leftMap127 rightMap127 22 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice23 : Residual1Cache.slice leftMap127 rightMap127 23 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice24 : Residual1Cache.slice leftMap127 rightMap127 24 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice25 : Residual1Cache.slice leftMap127 rightMap127 25 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice26 : Residual1Cache.slice leftMap127 rightMap127 26 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice27 : Residual1Cache.slice leftMap127 rightMap127 27 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice28 : Residual1Cache.slice leftMap127 rightMap127 28 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice29 : Residual1Cache.slice leftMap127 rightMap127 29 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice30 : Residual1Cache.slice leftMap127 rightMap127 30 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice31 : Residual1Cache.slice leftMap127 rightMap127 31 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice32 : Residual1Cache.slice leftMap127 rightMap127 32 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice33 : Residual1Cache.slice leftMap127 rightMap127 33 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice34 : Residual1Cache.slice leftMap127 rightMap127 34 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice35 : Residual1Cache.slice leftMap127 rightMap127 35 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice36 : Residual1Cache.slice leftMap127 rightMap127 36 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice37 : Residual1Cache.slice leftMap127 rightMap127 37 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice38 : Residual1Cache.slice leftMap127 rightMap127 38 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice39 : Residual1Cache.slice leftMap127 rightMap127 39 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice40 : Residual1Cache.slice leftMap127 rightMap127 40 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice41 : Residual1Cache.slice leftMap127 rightMap127 41 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice42 : Residual1Cache.slice leftMap127 rightMap127 42 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice43 : Residual1Cache.slice leftMap127 rightMap127 43 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice44 : Residual1Cache.slice leftMap127 rightMap127 44 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice45 : Residual1Cache.slice leftMap127 rightMap127 45 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice46 : Residual1Cache.slice leftMap127 rightMap127 46 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice47 : Residual1Cache.slice leftMap127 rightMap127 47 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice48 : Residual1Cache.slice leftMap127 rightMap127 48 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice49 : Residual1Cache.slice leftMap127 rightMap127 49 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice50 : Residual1Cache.slice leftMap127 rightMap127 50 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice51 : Residual1Cache.slice leftMap127 rightMap127 51 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice52 : Residual1Cache.slice leftMap127 rightMap127 52 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice53 : Residual1Cache.slice leftMap127 rightMap127 53 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice54 : Residual1Cache.slice leftMap127 rightMap127 54 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice55 : Residual1Cache.slice leftMap127 rightMap127 55 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice56 : Residual1Cache.slice leftMap127 rightMap127 56 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice57 : Residual1Cache.slice leftMap127 rightMap127 57 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice58 : Residual1Cache.slice leftMap127 rightMap127 58 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice59 : Residual1Cache.slice leftMap127 rightMap127 59 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice60 : Residual1Cache.slice leftMap127 rightMap127 60 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice61 : Residual1Cache.slice leftMap127 rightMap127 61 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice62 : Residual1Cache.slice leftMap127 rightMap127 62 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice63 : Residual1Cache.slice leftMap127 rightMap127 63 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice64 : Residual1Cache.slice leftMap127 rightMap127 64 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice65 : Residual1Cache.slice leftMap127 rightMap127 65 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice66 : Residual1Cache.slice leftMap127 rightMap127 66 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice67 : Residual1Cache.slice leftMap127 rightMap127 67 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice68 : Residual1Cache.slice leftMap127 rightMap127 68 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice69 : Residual1Cache.slice leftMap127 rightMap127 69 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice70 : Residual1Cache.slice leftMap127 rightMap127 70 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice71 : Residual1Cache.slice leftMap127 rightMap127 71 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice72 : Residual1Cache.slice leftMap127 rightMap127 72 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice73 : Residual1Cache.slice leftMap127 rightMap127 73 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice74 : Residual1Cache.slice leftMap127 rightMap127 74 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice75 : Residual1Cache.slice leftMap127 rightMap127 75 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice76 : Residual1Cache.slice leftMap127 rightMap127 76 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice77 : Residual1Cache.slice leftMap127 rightMap127 77 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice78 : Residual1Cache.slice leftMap127 rightMap127 78 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice79 : Residual1Cache.slice leftMap127 rightMap127 79 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice80 : Residual1Cache.slice leftMap127 rightMap127 80 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice81 : Residual1Cache.slice leftMap127 rightMap127 81 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice82 : Residual1Cache.slice leftMap127 rightMap127 82 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice83 : Residual1Cache.slice leftMap127 rightMap127 83 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice84 : Residual1Cache.slice leftMap127 rightMap127 84 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice85 : Residual1Cache.slice leftMap127 rightMap127 85 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice86 : Residual1Cache.slice leftMap127 rightMap127 86 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice87 : Residual1Cache.slice leftMap127 rightMap127 87 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice88 : Residual1Cache.slice leftMap127 rightMap127 88 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice89 : Residual1Cache.slice leftMap127 rightMap127 89 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice90 : Residual1Cache.slice leftMap127 rightMap127 90 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice91 : Residual1Cache.slice leftMap127 rightMap127 91 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice92 : Residual1Cache.slice leftMap127 rightMap127 92 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice93 : Residual1Cache.slice leftMap127 rightMap127 93 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice94 : Residual1Cache.slice leftMap127 rightMap127 94 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice95 : Residual1Cache.slice leftMap127 rightMap127 95 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice96 : Residual1Cache.slice leftMap127 rightMap127 96 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice97 : Residual1Cache.slice leftMap127 rightMap127 97 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice98 : Residual1Cache.slice leftMap127 rightMap127 98 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice99 : Residual1Cache.slice leftMap127 rightMap127 99 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice100 : Residual1Cache.slice leftMap127 rightMap127 100 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice101 : Residual1Cache.slice leftMap127 rightMap127 101 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice102 : Residual1Cache.slice leftMap127 rightMap127 102 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice103 : Residual1Cache.slice leftMap127 rightMap127 103 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice104 : Residual1Cache.slice leftMap127 rightMap127 104 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice105 : Residual1Cache.slice leftMap127 rightMap127 105 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice106 : Residual1Cache.slice leftMap127 rightMap127 106 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice107 : Residual1Cache.slice leftMap127 rightMap127 107 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice108 : Residual1Cache.slice leftMap127 rightMap127 108 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice109 : Residual1Cache.slice leftMap127 rightMap127 109 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice110 : Residual1Cache.slice leftMap127 rightMap127 110 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice111 : Residual1Cache.slice leftMap127 rightMap127 111 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice112 : Residual1Cache.slice leftMap127 rightMap127 112 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice113 : Residual1Cache.slice leftMap127 rightMap127 113 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice114 : Residual1Cache.slice leftMap127 rightMap127 114 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice115 : Residual1Cache.slice leftMap127 rightMap127 115 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice116 : Residual1Cache.slice leftMap127 rightMap127 116 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice117 : Residual1Cache.slice leftMap127 rightMap127 117 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice118 : Residual1Cache.slice leftMap127 rightMap127 118 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice119 : Residual1Cache.slice leftMap127 rightMap127 119 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice120 : Residual1Cache.slice leftMap127 rightMap127 120 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice121 : Residual1Cache.slice leftMap127 rightMap127 121 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice122 : Residual1Cache.slice leftMap127 rightMap127 122 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice123 : Residual1Cache.slice leftMap127 rightMap127 123 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice124 : Residual1Cache.slice leftMap127 rightMap127 124 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice125 : Residual1Cache.slice leftMap127 rightMap127 125 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice126 : Residual1Cache.slice leftMap127 rightMap127 126 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice127 : Residual1Cache.slice leftMap127 rightMap127 127 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice128 : Residual1Cache.slice leftMap127 rightMap127 128 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice129 : Residual1Cache.slice leftMap127 rightMap127 129 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice130 : Residual1Cache.slice leftMap127 rightMap127 130 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice131 : Residual1Cache.slice leftMap127 rightMap127 131 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice132 : Residual1Cache.slice leftMap127 rightMap127 132 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice133 : Residual1Cache.slice leftMap127 rightMap127 133 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice134 : Residual1Cache.slice leftMap127 rightMap127 134 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice135 : Residual1Cache.slice leftMap127 rightMap127 135 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice136 : Residual1Cache.slice leftMap127 rightMap127 136 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice137 : Residual1Cache.slice leftMap127 rightMap127 137 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice138 : Residual1Cache.slice leftMap127 rightMap127 138 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice139 : Residual1Cache.slice leftMap127 rightMap127 139 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice140 : Residual1Cache.slice leftMap127 rightMap127 140 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice141 : Residual1Cache.slice leftMap127 rightMap127 141 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice142 : Residual1Cache.slice leftMap127 rightMap127 142 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice143 : Residual1Cache.slice leftMap127 rightMap127 143 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice144 : Residual1Cache.slice leftMap127 rightMap127 144 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice145 : Residual1Cache.slice leftMap127 rightMap127 145 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice146 : Residual1Cache.slice leftMap127 rightMap127 146 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice147 : Residual1Cache.slice leftMap127 rightMap127 147 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice148 : Residual1Cache.slice leftMap127 rightMap127 148 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice149 : Residual1Cache.slice leftMap127 rightMap127 149 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice150 : Residual1Cache.slice leftMap127 rightMap127 150 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice151 : Residual1Cache.slice leftMap127 rightMap127 151 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice152 : Residual1Cache.slice leftMap127 rightMap127 152 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice153 : Residual1Cache.slice leftMap127 rightMap127 153 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice154 : Residual1Cache.slice leftMap127 rightMap127 154 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice155 : Residual1Cache.slice leftMap127 rightMap127 155 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice156 : Residual1Cache.slice leftMap127 rightMap127 156 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice157 : Residual1Cache.slice leftMap127 rightMap127 157 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice158 : Residual1Cache.slice leftMap127 rightMap127 158 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice159 : Residual1Cache.slice leftMap127 rightMap127 159 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice160 : Residual1Cache.slice leftMap127 rightMap127 160 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice161 : Residual1Cache.slice leftMap127 rightMap127 161 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice162 : Residual1Cache.slice leftMap127 rightMap127 162 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice163 : Residual1Cache.slice leftMap127 rightMap127 163 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice164 : Residual1Cache.slice leftMap127 rightMap127 164 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice165 : Residual1Cache.slice leftMap127 rightMap127 165 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice166 : Residual1Cache.slice leftMap127 rightMap127 166 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice167 : Residual1Cache.slice leftMap127 rightMap127 167 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice168 : Residual1Cache.slice leftMap127 rightMap127 168 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice169 : Residual1Cache.slice leftMap127 rightMap127 169 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice170 : Residual1Cache.slice leftMap127 rightMap127 170 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice171 : Residual1Cache.slice leftMap127 rightMap127 171 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice172 : Residual1Cache.slice leftMap127 rightMap127 172 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice173 : Residual1Cache.slice leftMap127 rightMap127 173 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice174 : Residual1Cache.slice leftMap127 rightMap127 174 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice175 : Residual1Cache.slice leftMap127 rightMap127 175 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice176 : Residual1Cache.slice leftMap127 rightMap127 176 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice177 : Residual1Cache.slice leftMap127 rightMap127 177 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice178 : Residual1Cache.slice leftMap127 rightMap127 178 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice179 : Residual1Cache.slice leftMap127 rightMap127 179 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice180 : Residual1Cache.slice leftMap127 rightMap127 180 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice181 : Residual1Cache.slice leftMap127 rightMap127 181 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice182 : Residual1Cache.slice leftMap127 rightMap127 182 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice183 : Residual1Cache.slice leftMap127 rightMap127 183 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice184 : Residual1Cache.slice leftMap127 rightMap127 184 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice185 : Residual1Cache.slice leftMap127 rightMap127 185 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice186 : Residual1Cache.slice leftMap127 rightMap127 186 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice187 : Residual1Cache.slice leftMap127 rightMap127 187 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice188 : Residual1Cache.slice leftMap127 rightMap127 188 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice189 : Residual1Cache.slice leftMap127 rightMap127 189 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice190 : Residual1Cache.slice leftMap127 rightMap127 190 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice191 : Residual1Cache.slice leftMap127 rightMap127 191 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice192 : Residual1Cache.slice leftMap127 rightMap127 192 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice193 : Residual1Cache.slice leftMap127 rightMap127 193 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice194 : Residual1Cache.slice leftMap127 rightMap127 194 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice195 : Residual1Cache.slice leftMap127 rightMap127 195 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice196 : Residual1Cache.slice leftMap127 rightMap127 196 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice197 : Residual1Cache.slice leftMap127 rightMap127 197 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice198 : Residual1Cache.slice leftMap127 rightMap127 198 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice199 : Residual1Cache.slice leftMap127 rightMap127 199 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice200 : Residual1Cache.slice leftMap127 rightMap127 200 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice201 : Residual1Cache.slice leftMap127 rightMap127 201 = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point127slice202 : Residual1Cache.slice leftMap127 rightMap127 202 = true := by
  decide +kernel

private theorem point127_slices : ∀ c, Residual1Cache.slice leftMap127 rightMap127 c = true := by
  intro c
  fin_cases c
  · exact point127slice0
  · exact point127slice1
  · exact point127slice2
  · exact point127slice3
  · exact point127slice4
  · exact point127slice5
  · exact point127slice6
  · exact point127slice7
  · exact point127slice8
  · exact point127slice9
  · exact point127slice10
  · exact point127slice11
  · exact point127slice12
  · exact point127slice13
  · exact point127slice14
  · exact point127slice15
  · exact point127slice16
  · exact point127slice17
  · exact point127slice18
  · exact point127slice19
  · exact point127slice20
  · exact point127slice21
  · exact point127slice22
  · exact point127slice23
  · exact point127slice24
  · exact point127slice25
  · exact point127slice26
  · exact point127slice27
  · exact point127slice28
  · exact point127slice29
  · exact point127slice30
  · exact point127slice31
  · exact point127slice32
  · exact point127slice33
  · exact point127slice34
  · exact point127slice35
  · exact point127slice36
  · exact point127slice37
  · exact point127slice38
  · exact point127slice39
  · exact point127slice40
  · exact point127slice41
  · exact point127slice42
  · exact point127slice43
  · exact point127slice44
  · exact point127slice45
  · exact point127slice46
  · exact point127slice47
  · exact point127slice48
  · exact point127slice49
  · exact point127slice50
  · exact point127slice51
  · exact point127slice52
  · exact point127slice53
  · exact point127slice54
  · exact point127slice55
  · exact point127slice56
  · exact point127slice57
  · exact point127slice58
  · exact point127slice59
  · exact point127slice60
  · exact point127slice61
  · exact point127slice62
  · exact point127slice63
  · exact point127slice64
  · exact point127slice65
  · exact point127slice66
  · exact point127slice67
  · exact point127slice68
  · exact point127slice69
  · exact point127slice70
  · exact point127slice71
  · exact point127slice72
  · exact point127slice73
  · exact point127slice74
  · exact point127slice75
  · exact point127slice76
  · exact point127slice77
  · exact point127slice78
  · exact point127slice79
  · exact point127slice80
  · exact point127slice81
  · exact point127slice82
  · exact point127slice83
  · exact point127slice84
  · exact point127slice85
  · exact point127slice86
  · exact point127slice87
  · exact point127slice88
  · exact point127slice89
  · exact point127slice90
  · exact point127slice91
  · exact point127slice92
  · exact point127slice93
  · exact point127slice94
  · exact point127slice95
  · exact point127slice96
  · exact point127slice97
  · exact point127slice98
  · exact point127slice99
  · exact point127slice100
  · exact point127slice101
  · exact point127slice102
  · exact point127slice103
  · exact point127slice104
  · exact point127slice105
  · exact point127slice106
  · exact point127slice107
  · exact point127slice108
  · exact point127slice109
  · exact point127slice110
  · exact point127slice111
  · exact point127slice112
  · exact point127slice113
  · exact point127slice114
  · exact point127slice115
  · exact point127slice116
  · exact point127slice117
  · exact point127slice118
  · exact point127slice119
  · exact point127slice120
  · exact point127slice121
  · exact point127slice122
  · exact point127slice123
  · exact point127slice124
  · exact point127slice125
  · exact point127slice126
  · exact point127slice127
  · exact point127slice128
  · exact point127slice129
  · exact point127slice130
  · exact point127slice131
  · exact point127slice132
  · exact point127slice133
  · exact point127slice134
  · exact point127slice135
  · exact point127slice136
  · exact point127slice137
  · exact point127slice138
  · exact point127slice139
  · exact point127slice140
  · exact point127slice141
  · exact point127slice142
  · exact point127slice143
  · exact point127slice144
  · exact point127slice145
  · exact point127slice146
  · exact point127slice147
  · exact point127slice148
  · exact point127slice149
  · exact point127slice150
  · exact point127slice151
  · exact point127slice152
  · exact point127slice153
  · exact point127slice154
  · exact point127slice155
  · exact point127slice156
  · exact point127slice157
  · exact point127slice158
  · exact point127slice159
  · exact point127slice160
  · exact point127slice161
  · exact point127slice162
  · exact point127slice163
  · exact point127slice164
  · exact point127slice165
  · exact point127slice166
  · exact point127slice167
  · exact point127slice168
  · exact point127slice169
  · exact point127slice170
  · exact point127slice171
  · exact point127slice172
  · exact point127slice173
  · exact point127slice174
  · exact point127slice175
  · exact point127slice176
  · exact point127slice177
  · exact point127slice178
  · exact point127slice179
  · exact point127slice180
  · exact point127slice181
  · exact point127slice182
  · exact point127slice183
  · exact point127slice184
  · exact point127slice185
  · exact point127slice186
  · exact point127slice187
  · exact point127slice188
  · exact point127slice189
  · exact point127slice190
  · exact point127slice191
  · exact point127slice192
  · exact point127slice193
  · exact point127slice194
  · exact point127slice195
  · exact point127slice196
  · exact point127slice197
  · exact point127slice198
  · exact point127slice199
  · exact point127slice200
  · exact point127slice201
  · exact point127slice202

set_option maxHeartbeats 1600000 in
public theorem point127 : stepCheck 1 2579 := by
  have hleft : L0Gen 1 * L0Rep 2579 = leftPerm127 := by
    change L0Gen 1 * evalWord L0Gen [1, 0, 3, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] = leftPerm127
    simp only [leftPerm127, p236, p59, p50, p48, p20, p14, p11, p3, p1, p0, evalWord, mul_one, mul_assoc]
  have hright : L0Rep (L0Act 1 2579) * evalWord L1Gen (L0Factor 1 2579) = rightPerm127 := by
    change evalWord L0Gen [0, 3, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0, 1, 0] * evalWord L1Gen [3, 2, 1, 2, 3, 2, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 0, 3, 0, 3, 3, 2, 3, 3, 0, 1, 1, 2, 1, 0, 3, 0, 3] = rightPerm127
    simp only [rightPerm127, p982, p857, p276, p259, p98, p86, p74, p69, p66, p65, p64, p61, p60, p58, p57, p55, p52, p38, p34, p33, p31, p29, p28, p27, p26, p25, p24, p23, p21, p20, p19, p18, p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p1, p0, evalWord, mul_one, mul_assoc]
  right
  apply (checkFin_spec _).mpr
  intro x
  apply decide_eq_true
  change (L0Gen 1 * L0Rep 2579) x =
    (L0Rep (L0Act 1 2579) * evalWord L1Gen (L0Factor 1 2579)) x
  rw [hleft, hright]
  apply Fin.ext
  rw [← leftMap127_eq, ← rightMap127_eq]
  exact Residual1Cache.ofSlices point127_slices x

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
