module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Generators
import Mathlib.Tactic.FinCases

/-!
# HS stabilizer level 3: representatives and transition witnesses

Part of the order-divisibility certificate for the exact ATLAS HS carrier.
Source: GLS volume 3, Table 5.3m, printed p.274; ATLAS HSG1-p100B0.
The generator in `OrderBound/source/` supplies witnesses only. Every finite
identity is checked by Lean's kernel.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 100000
set_option Elab.async false

def repWord3 (x : Fin 20) : List (Fin 10) :=
  match x.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [2]
  | 4 => [3]
  | 5 => [2, 0]
  | 6 => [3, 0]
  | 7 => [4, 0]
  | 8 => [5, 0]
  | 9 => [8, 0]
  | 10 => [9, 0]
  | 11 => [2, 1]
  | 12 => [3, 1]
  | 13 => [4, 1]
  | 14 => [5, 1]
  | 15 => [7, 1]
  | 16 => [1, 2]
  | 17 => [6, 3]
  | 18 => [2, 2, 0]
  | _ => [2, 5, 0]

def rep3 : Fin 20 → Equiv.Perm (Fin 100) :=
  fun r => evalWord gen3 (repWord3 r)

def point3 (x : Fin 20) : Fin 100 :=
  match x.val with
  | 0 => 14
  | 1 => 97
  | 2 => 54
  | 3 => 86
  | 4 => 18
  | 5 => 68
  | 6 => 83
  | 7 => 35
  | 8 => 20
  | 9 => 72
  | 10 => 63
  | 11 => 93
  | 12 => 79
  | 13 => 42
  | 14 => 59
  | 15 => 43
  | 16 => 25
  | 17 => 82
  | 18 => 64
  | _ => 33

theorem rep3_mem (r : Fin 20) : rep3 r ∈ H3 := ⟨repWord3 r, rfl⟩

theorem rep3_base : rep3 0 = 1 := rfl

theorem rep3_point : ∀ r, rep3 r 14 = point3 r := by
  apply allFin
  decide +kernel

theorem point3_injective : Function.Injective point3 := by
  have h : ∀ i j : Fin 20, point3 i = point3 j → i = j := by decide +kernel
  exact h

theorem next3_fix : ∀ g : H4, (g : Equiv.Perm (Fin 100)) 14 = 14 := by
  apply wordSubgroup_fix_of_gen_fix
  apply allFin
  decide +kernel

def act3 (x : Fin 10) : Fin 20 → Fin 20 :=
  match x.val with
  | 0 => ![1, 2, 0, 12, 5, 8, 6, 15, 4, 13, 14, 7, 16, 19, 18, 11, 3, 17, 10, 9]
  | 1 => ![2, 0, 1, 16, 8, 4, 6, 11, 5, 19, 18, 15, 3, 9, 10, 7, 12, 17, 14, 13]
  | 2 => ![3, 5, 11, 15, 0, 18, 1, 9, 19, 8, 17, 10, 2, 6, 7, 16, 4, 12, 13, 14]
  | 3 => ![4, 6, 12, 0, 16, 1, 13, 14, 9, 7, 11, 2, 17, 18, 19, 3, 15, 10, 5, 8]
  | 4 => ![0, 7, 13, 3, 16, 10, 5, 8, 1, 11, 6, 17, 19, 14, 2, 4, 15, 9, 12, 18]
  | 5 => ![0, 8, 14, 3, 15, 6, 10, 1, 7, 17, 5, 9, 18, 2, 13, 16, 4, 11, 19, 12]
  | 6 => ![0, 7, 9, 1, 17, 4, 13, 3, 8, 15, 11, 14, 18, 16, 10, 2, 6, 5, 19, 12]
  | 7 => ![0, 3, 15, 7, 5, 17, 16, 1, 8, 2, 14, 10, 19, 6, 11, 9, 13, 4, 12, 18]
  | 8 => ![0, 9, 5, 4, 15, 11, 13, 14, 6, 10, 1, 2, 19, 8, 17, 3, 16, 7, 12, 18]
  | _ => ![0, 10, 11, 15, 3, 2, 8, 17, 13, 1, 9, 5, 18, 6, 7, 4, 16, 14, 19, 12]

def factor3 (x : Fin 10) : Fin 20 → List (Fin 6) :=
  match x.val with
  | 0 => ![[], [], [], [1, 2, 5], [5, 3, 0, 4], [2, 1, 4], [1], [1, 2, 4], [2, 0, 5], [2, 4], [2, 1, 5], [2, 0, 4], [1, 2, 5], [3, 1, 4], [5, 3, 0, 4], [0, 5], [], [4, 0, 5], [5, 2], [1]]
  | 1 => ![[], [], [], [], [3, 1, 4], [3, 0, 5], [0], [5, 2, 0], [3, 4, 0, 4], [0], [3, 4], [0, 5], [1, 2, 5], [2, 4], [2, 1, 5], [5, 3, 0], [1, 2, 5], [0, 4], [3, 0, 5], [2, 0, 5]]
  | 2 => ![[], [], [], [5, 3, 0, 4], [], [], [], [5, 2, 5], [], [2, 0], [2], [5, 3, 0, 5], [], [5, 2, 0, 4], [5, 3, 0, 5], [3, 1, 5], [0, 3], [0, 3, 5], [5, 2, 0, 4], [5, 2, 0, 4]]
  | 3 => ![[], [], [], [], [2, 1], [], [5, 2, 0, 4], [5, 3, 0, 5], [2, 0], [5, 2, 5], [5, 3, 0, 5], [], [3, 4, 0, 5], [5, 2, 0, 4], [5, 2, 0, 4], [3, 0, 5], [5, 2, 0, 5], [3], [], []]
  | 4 => ![[0], [], [], [0, 4], [5, 3, 0, 4], [3, 4, 0], [5, 2, 5], [], [], [5, 2, 0, 4], [2, 0], [5, 3, 0, 4], [3, 1], [], [], [3], [0, 5], [2, 5], [4, 0, 4], [3, 4, 0]]
  | 5 => ![[1], [], [], [4, 0, 5], [2], [5, 2, 5], [2, 0], [], [], [5, 2, 4], [3, 4, 0], [5, 2, 0, 4], [4, 0, 4], [], [], [0, 5], [3, 0, 5], [3, 0, 5], [3, 4, 0], [3, 1]]
  | 6 => ![[2], [3, 1, 5], [3, 4], [2, 1], [], [5, 2, 0, 4], [5, 3, 0, 4], [2, 4], [5, 2, 0, 5], [5, 2], [4], [3, 4, 0, 4], [2, 4], [0, 5], [0, 3, 5], [], [3], [5, 2, 0, 4], [1, 2, 5], [3, 4, 0]]
  | 7 => ![[3], [0, 3], [], [2, 4], [5, 2, 0, 4], [5, 2, 0, 4], [2], [5, 2, 0, 5], [3, 1, 5], [5, 2], [3, 4, 0, 5], [5], [3, 4, 0], [3, 0, 5], [2, 1, 4], [3, 4], [0, 5], [], [2, 4], [1, 2, 5]]
  | 8 => ![[4], [], [3, 1], [5], [2, 0], [5, 3, 0, 5], [5, 3, 0, 5], [4, 0, 4], [2, 0], [], [], [5, 2, 5], [5, 3, 0, 5], [4, 0, 4], [0, 3], [3, 1, 4], [3, 4], [2, 5], [3, 1], [5, 2, 5]]
  | _ => ![[5], [], [5, 2, 5], [2, 0, 5], [4], [3, 1], [2, 0], [5, 2, 4], [4, 0, 4], [], [], [5, 3, 0, 5], [3, 1], [5, 3, 0, 5], [4, 0, 4], [2, 0], [5, 2], [2, 1], [5, 2, 5], [5, 3, 0, 5]]

def stepCheck3 : Fin 10 → Bool :=
  fun i => checkFin (fun r : Fin 20 => checkFin (fun x : Fin 100 => decide
    ((gen3 i * rep3 r) x = (rep3 (act3 i r) * evalWord gen4 (factor3 i r)) x)))

theorem step3_of_check (i : Fin 10) (h : stepCheck3 i = true) :
    ∀ r, gen3 i * rep3 r = rep3 (act3 i r) * evalWord gen4 (factor3 i r) := by
  have hr := allFin (fun r : Fin 20 => checkFin (fun x : Fin 100 => decide
    ((gen3 i * rep3 r) x = (rep3 (act3 i r) * evalWord gen4 (factor3 i r)) x)) = true) (by
      simpa only [stepCheck3, Bool.decide_eq_true] using h)
  intro r
  exact Equiv.ext (allFin _ (hr r))

end Sporadic.LeechRelated.HS.OrderCertificate
