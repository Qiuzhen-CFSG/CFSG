module

public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic

/-!
# Conjugacy classes in a normal subgroup

A nonidentity element of a finite normal subgroup has fewer conjugates than
the order of that subgroup: its orbit avoids the identity. Orbit-stabilizer
turns this into a strict bound on its centralizer index.

Source/application: Parrott, *A characterization of the Tits' simple group*
(1972), p.677, the order and quotient deductions in Lemma 6.
-/

open Subgroup

/-- A nonidentity conjugacy class in a normal subgroup avoids its identity. -/
public theorem centralizer_index_lt_card_normal {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (z : G) (hz : z ∈ L) (hz1 : z ≠ 1) :
    (centralizer ({z} : Set G)).index < Nat.card L := by
  let _ := MulDistribMulAction.compHom L (MulAut.conjNormal : G →* MulAut L)
  let zL : L := ⟨z, hz⟩
  have hzL : zL ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
  have hsub : MulAction.orbit G zL ⊆ ({1} : Set L)ᶜ := by
    intro x hx
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    change g • zL ≠ 1
    intro hh
    exact hzL (by simpa using congrArg (fun y : L => g⁻¹ • y) hh)
  have hstab : MulAction.stabilizer G zL = centralizer ({z} : Set G) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_centralizer_singleton_iff]
    rw [Subtype.ext_iff]
    change g * z * g⁻¹ = z ↔ g * z = z * g
    rw [mul_inv_eq_iff_eq_mul]
  have hbound := Set.ncard_le_ncard hsub
  rw [Set.ncard_compl, Set.ncard_singleton] at hbound
  have heq : (centralizer ({z} : Set G)).index = (MulAction.orbit G zL).ncard := by
    rw [← hstab, MulAction.index_stabilizer]
  rw [heq]
  have hpos : 0 < Nat.card L := Nat.card_pos
  omega
