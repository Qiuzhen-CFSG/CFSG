module

public import Theory.ElementaryAbelian.Basic

/-!
# Uniqueness of elementary subgroups of a given order

A multiplicative equivalence preserves existence and uniqueness of an
elementary subgroup of specified order. Such a unique subgroup is
characteristic. These elementary transports retain the actual subgroups
used to distinguish the Sylow models in Aschbacher–Smith F.6.18.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

theorem existsUnique_elementary_subgroup_of_equiv (e : G ≃* H) {p n : ℕ} [Fact p.Prime]
    (h : ∃! E : Subgroup G, IsElementaryAbelian p E ∧ Nat.card E = n) :
    ∃! E : Subgroup H, IsElementaryAbelian p E ∧ Nat.card E = n := by
  obtain ⟨E, ⟨hE, hc⟩, hu⟩ := h
  let := hE
  refine ⟨E.map e.toMonoidHom, ⟨IsElementaryAbelian.map _,
    (card_map_of_injective e.injective).trans hc⟩, ?_⟩
  intro F hF
  let := hF.1
  have he : F.map e.symm.toMonoidHom = E := hu _
    ⟨IsElementaryAbelian.map _, (card_map_of_injective e.symm.injective).trans hF.2⟩
  have hh := congrArg (Subgroup.map e.toMonoidHom) he
  simpa [map_map] using hh

theorem characteristic_of_unique_elementary_subgroup {p n : ℕ} [Fact p.Prime]
    (E : Subgroup G) (hE : IsElementaryAbelian p E) (hc : Nat.card E = n)
    (hu : ∀ F : Subgroup G, IsElementaryAbelian p F ∧ Nat.card F = n → F = E) :
    E.Characteristic := by
  let := hE
  apply characteristic_iff_map_eq.mpr
  intro e
  exact hu _ ⟨IsElementaryAbelian.map _, (card_map_of_injective e.injective).trans hc⟩
end Theory.GroupTheory
