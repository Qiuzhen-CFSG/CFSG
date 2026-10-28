module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Five-subgroups of A₅ are self-centralizing

An element of order five on five letters is a full five-cycle. The permutation
centralizer formula gives its centralizer order five already in S₅. The
centralizer of an order-five subgroup of A₅ embeds into that centralizer and
contains the original cyclic subgroup, so it is precisely that subgroup.

This structural calculation supplies the A₅ factor in Aschbacher,
*Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

public section

namespace Theory.SpecificGroups.Alternating
open Subgroup Equiv.Perm

/-- Every order-five subgroup of the concrete alternating group on five letters
is its own full centralizer. -/
theorem centralizer_eq_of_card_five (F : Subgroup (alternatingGroup (Fin 5)))
    (hF : Nat.card F = 5) :
    centralizer (F : Set (alternatingGroup (Fin 5))) = F := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic F := isCyclic_of_prime_card hF
  have hFC : F ≤ centralizer (F : Set (alternatingGroup (Fin 5))) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  apply (eq_of_le_of_card_ge hFC ?_).symm
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 5 (by rw [hF])
  let p : Equiv.Perm (Fin 5) := x.val.val
  have hp : orderOf p = 5 := (orderOf_coe x.val).trans ((orderOf_coe x).trans hx)
  have hcycle : p.IsCycle := isCycle_of_prime_order'' (by decide) (by simpa using hp)
  have htype : p.cycleType = {5} := by rw [hcycle.cycleType, ← hcycle.orderOf, hp]
  have hcard : Nat.card (centralizer ({p} : Set (Equiv.Perm (Fin 5)))) = 5 := by
    rw [nat_card_centralizer, htype]
    norm_num
  let f : centralizer (F : Set (alternatingGroup (Fin 5))) →
      centralizer ({p} : Set (Equiv.Perm (Fin 5))) := fun y =>
    ⟨y.val.val, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (y.property x.val x.property).symm)⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val) h))
  have hle := Nat.card_le_card_of_injective f hf
  simpa only [hcard, hF] using hle

end Theory.SpecificGroups.Alternating
