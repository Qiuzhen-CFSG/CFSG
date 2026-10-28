module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Generators
import Mathlib.Tactic.FinCases

/-!
# HS stabilizer level 4: representatives and transition witnesses

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

def repWord4 (x : Fin 16) : List (Fin 6) :=
  match x.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [2]
  | 4 => [3]
  | 5 => [2, 0]
  | 6 => [3, 0]
  | 7 => [4, 0]
  | 8 => [2, 1]
  | 9 => [3, 1]
  | 10 => [1, 2]
  | 11 => [5, 2]
  | 12 => [0, 3]
  | 13 => [5, 2, 0]
  | 14 => [5, 3, 0]
  | _ => [3, 4, 0]

def rep4 : Fin 16 → Equiv.Perm (Fin 100) :=
  fun r => evalWord gen4 (repWord4 r)

def point4 (x : Fin 16) : Fin 100 :=
  match x.val with
  | 0 => 1
  | 1 => 58
  | 2 => 15
  | 3 => 22
  | 4 => 3
  | 5 => 90
  | 6 => 41
  | 7 => 94
  | 8 => 62
  | 9 => 65
  | 10 => 7
  | 11 => 84
  | 12 => 23
  | 13 => 77
  | 14 => 98
  | _ => 13

theorem rep4_mem (r : Fin 16) : rep4 r ∈ H4 := ⟨repWord4 r, rfl⟩

theorem rep4_base : rep4 0 = 1 := rfl

theorem rep4_point : ∀ r, rep4 r 1 = point4 r := by
  apply allFin
  decide +kernel

theorem point4_injective : Function.Injective point4 := by
  have h : ∀ i j : Fin 16, point4 i = point4 j → i = j := by decide +kernel
  exact h

theorem next4_fix : ∀ g : H5, (g : Equiv.Perm (Fin 100)) 1 = 1 := by
  apply wordSubgroup_fix_of_gen_fix
  apply allFin
  decide +kernel

def act4 (x : Fin 6) : Fin 16 → Fin 16 :=
  match x.val with
  | 0 => ![1, 2, 0, 9, 12, 4, 13, 7, 6, 10, 3, 14, 5, 8, 15, 11]
  | 1 => ![2, 0, 1, 10, 5, 12, 8, 7, 13, 3, 9, 15, 4, 6, 11, 14]
  | 2 => ![3, 5, 8, 4, 0, 6, 1, 14, 9, 2, 13, 11, 10, 12, 15, 7]
  | 3 => ![4, 6, 9, 0, 3, 1, 5, 15, 2, 8, 12, 11, 13, 10, 7, 14]
  | 4 => ![0, 7, 1, 4, 11, 9, 10, 2, 15, 13, 14, 3, 8, 5, 6, 12]
  | _ => ![0, 2, 7, 11, 3, 13, 14, 1, 12, 5, 6, 4, 15, 9, 10, 8]

def factor4 (x : Fin 6) : Fin 16 → List (Fin 2) :=
  match x.val with
  | 0 => ![[], [], [], [], [], [], [0], [0], [], [], [], [0], [], [1], [1], []]
  | 1 => ![[], [], [], [], [], [], [], [1], [0], [], [], [], [], [1], [1], [0]]
  | 2 => ![[], [], [], [], [], [], [], [], [], [], [0], [1], [], [1], [], []]
  | 3 => ![[], [], [], [], [], [], [], [], [], [], [], [0], [0], [1], [], []]
  | 4 => ![[0], [], [1], [1], [0], [0], [1], [0], [1], [1], [0], [], [1], [], [], [1]]
  | _ => ![[1], [0], [1], [], [0], [], [], [], [0], [1], [0], [1], [0], [0], [1], [0]]

def stepCheck4 : Fin 6 → Bool :=
  fun i => checkFin (fun r : Fin 16 => checkFin (fun x : Fin 100 => decide
    ((gen4 i * rep4 r) x = (rep4 (act4 i r) * evalWord gen5 (factor4 i r)) x)))

theorem step4_of_check (i : Fin 6) (h : stepCheck4 i = true) :
    ∀ r, gen4 i * rep4 r = rep4 (act4 i r) * evalWord gen5 (factor4 i r) := by
  have hr := allFin (fun r : Fin 16 => checkFin (fun x : Fin 100 => decide
    ((gen4 i * rep4 r) x = (rep4 (act4 i r) * evalWord gen5 (factor4 i r)) x)) = true) (by
      simpa only [stepCheck4, Bool.decide_eq_true] using h)
  intro r
  exact Equiv.ext (allFin _ (hr r))

end Sporadic.LeechRelated.HS.OrderCertificate
