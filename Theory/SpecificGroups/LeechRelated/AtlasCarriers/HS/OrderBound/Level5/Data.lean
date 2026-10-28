module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Generators
import Mathlib.Tactic.FinCases

/-!
# HS stabilizer level 5: representatives and transition witnesses

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

def repWord5 (x : Fin 3) : List (Fin 2) :=
  match x.val with
  | 0 => []
  | 1 => [0]
  | _ => [1]

def rep5 : Fin 3 → Equiv.Perm (Fin 100) :=
  fun r => evalWord gen5 (repWord5 r)

def point5 (x : Fin 3) : Fin 100 :=
  match x.val with
  | 0 => 3
  | 1 => 84
  | _ => 22

theorem rep5_mem (r : Fin 3) : rep5 r ∈ H5 := ⟨repWord5 r, rfl⟩

theorem rep5_base : rep5 0 = 1 := rfl

theorem rep5_point : ∀ r, rep5 r 3 = point5 r := by
  apply allFin
  decide +kernel

theorem point5_injective : Function.Injective point5 := by
  have h : ∀ i j : Fin 3, point5 i = point5 j → i = j := by decide +kernel
  exact h

theorem next5_fix : ∀ g : H6, (g : Equiv.Perm (Fin 100)) 3 = 3 := by
  apply wordSubgroup_fix_of_gen_fix
  intro i
  exact Fin.elim0 i

def act5 (x : Fin 2) : Fin 3 → Fin 3 :=
  match x.val with
  | 0 => ![1, 2, 0]
  | _ => ![2, 0, 1]

def factor5 (x : Fin 2) : Fin 3 → List (Fin 0) :=
  match x.val with
  | 0 => ![[], [], []]
  | _ => ![[], [], []]

def stepCheck5 : Fin 2 → Bool :=
  fun i => checkFin (fun r : Fin 3 => checkFin (fun x : Fin 100 => decide
    ((gen5 i * rep5 r) x = (rep5 (act5 i r) * evalWord gen6 (factor5 i r)) x)))

theorem step5_of_check (i : Fin 2) (h : stepCheck5 i = true) :
    ∀ r, gen5 i * rep5 r = rep5 (act5 i r) * evalWord gen6 (factor5 i r) := by
  have hr := allFin (fun r : Fin 3 => checkFin (fun x : Fin 100 => decide
    ((gen5 i * rep5 r) x = (rep5 (act5 i r) * evalWord gen6 (factor5 i r)) x)) = true) (by
      simpa only [stepCheck5, Bool.decide_eq_true] using h)
  intro r
  exact Equiv.ext (allFin _ (hr r))

end Sporadic.LeechRelated.HS.OrderCertificate
