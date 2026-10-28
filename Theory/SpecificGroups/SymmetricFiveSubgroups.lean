module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.NormNum

/-!
# The order-thirty obstruction in the symmetric group on five points

A subgroup of order thirty in S₅ would have index four. Its intersection
with A₅ would consequently have index at most four in A₅. Simplicity and
the coset action force that intersection to be all of A₅, contradicting
the orders. No subgroup classification is needed.

This is the final permutation-group obstruction in Aschbacher–Smith,
proof of 16.4.9(2), combined manuscript of 1 March 2004, printed p.1192.
Constructing the five-point action in that application is a separate step.
-/

namespace Equiv.Perm

open Subgroup

/-- The symmetric group on five letters has no subgroup of order thirty. -/
public theorem subgroup_card_ne_thirty (H : Subgroup (Equiv.Perm (Fin 5))) :
    Nat.card H ≠ 30 := by
  intro hcard
  have hS : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  have hi : H.index = 4 := by
    have hh := H.card_mul_index
    rw [hcard, hS] at hh
    omega
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hle : H.relIndex (alternatingGroup (Fin 5)) ≤ 4 := by
    have hh := H.relIndex_le_of_le_right
      (show alternatingGroup (Fin 5) ≤ ⊤ from le_top)
      (by simp only [H.relIndex_top_right, hi]; decide : H.relIndex ⊤ ≠ 0)
    simpa only [H.relIndex_top_right, hi] using hh
  have htop : H.subgroupOf (alternatingGroup (Fin 5)) = ⊤ := by
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hb := Nat.factorial_le hle
    rw [hA]
    norm_num [Nat.factorial] at hb ⊢
    exact lt_of_le_of_lt hb (by decide)
  have hAH : alternatingGroup (Fin 5) ≤ H :=
    Subgroup.relIndex_eq_one.mp ((Subgroup.index_eq_one).mpr htop)
  have hh := Subgroup.card_le_of_le hAH
  omega

/-- An injective permutation representation on five points excludes order thirty. -/
public theorem card_ne_thirty_of_injective_hom {H : Type*} [Group H]
    (f : H →* Equiv.Perm (Fin 5)) (hf : Function.Injective f) : Nat.card H ≠ 30 := by
  have he : Nat.card H = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  rw [he]
  exact subgroup_card_ne_thirty f.range

end Equiv.Perm
