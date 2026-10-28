module

public import Theory.SpecificGroups.MinusExtraspecial.CentralStructure

/-!
# The ten noncentral involutions of the minus extraspecial group of order 32

The quaternion–dihedral coordinates count the involutions outside the center.
Transport along an actual group isomorphism gives the same count in any
realization. This is the orbit underlying the involution-centralizer order
calculation in Aschbacher, *Sporadic Groups* (1994), 46.1–46.3, p.251.
-/

public section
namespace MinusExtraspecial
open Subgroup

theorem card_noncentral_involutions :
    Nat.card {x : Model // x ^ 2 = 1 ∧ x ∉ center Model} = 10 := by
  calc
    _ = Nat.card {x : Model // x ^ 2 = 1 ∧ ¬ (x = 1 ∨ x = quaternion z)} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [mem_center_iff]))
    _ = 10 := by rw [Nat.card_eq_fintype_card]; decide +kernel

theorem card_noncentral_involutions_of_equiv {Q : Type*} [Group Q]
    (e : Q ≃* Model) :
    Nat.card {x : Q // x ^ 2 = 1 ∧ x ∉ center Q} = 10 := by
  apply (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)).trans
    card_noncentral_involutions
  intro x
  have hc : x ∈ center Q ↔ e x ∈ center Model := by
    constructor
    · intro hx
      exact (centerCongr e ⟨x, hx⟩).property
    · intro hx
      have hh := (centerCongr e.symm ⟨e x, hx⟩).property
      change e.symm (e x) ∈ center Q at hh
      rwa [e.symm_apply_apply] at hh
  change x ^ 2 = 1 ∧ x ∉ center Q ↔ e x ^ 2 = 1 ∧ e x ∉ center Model
  rw [← hc, ← map_pow, ← map_one e, e.injective.eq_iff]

end MinusExtraspecial
