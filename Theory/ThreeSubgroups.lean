module

public import Mathlib.GroupTheory.Commutator.Basic

@[expose] public section

namespace Subgroup


/-- Relative form of the three-subgroups lemma: the rotated commutators may
land in a common normal subgroup instead of being trivial. -/
theorem commutator_commutator_le_of_rotate
    {G : Type*} [Group G] {H₁ H₂ H₃ K : Subgroup G} [K.Normal]
    (h₁ : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ K) (h₂ : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ K)
    : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ K := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have h₁q : ⁅⁅H₂.map q, H₃.map q⁆, H₁.map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact h₁
  have h₂q : ⁅⁅H₃.map q, H₁.map q⁆, H₂.map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact h₂
  have hq : ⁅⁅H₁.map q, H₂.map q⁆, H₃.map q⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h₁q h₂q
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator] at hq
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hq
  exact hq

/-- Relative three-subgroups lemma when the target subgroup is normalized by
the three participating subgroups. -/
theorem commutator_commutator_le_of_rotate_of_le_normalizer
    {G : Type*} [Group G] {H₁ H₂ H₃ K : Subgroup G}
    (hnorm₁ : H₁ ≤ normalizer K) (hnorm₂ : H₂ ≤ normalizer K)
    (hnorm₃ : H₃ ≤ normalizer K)
    (h₁ : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ K) (h₂ : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ K)
    : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ K := by
  let L : Subgroup G := H₁ ⊔ H₂ ⊔ H₃ ⊔ K
  have hH₁L : H₁ ≤ L :=
    le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  have hH₂L : H₂ ≤ L :=
    le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have hH₃L : H₃ ≤ L := le_sup_of_le_left le_sup_right
  have hLnorm : L ≤ normalizer K := by
    exact sup_le (sup_le (sup_le hnorm₁ hnorm₂) hnorm₃) K.le_normalizer
  let H₁' : Subgroup L := H₁.subgroupOf L
  let H₂' : Subgroup L := H₂.subgroupOf L
  let H₃' : Subgroup L := H₃.subgroupOf L
  let K' : Subgroup L := K.subgroupOf L
  let : K'.Normal := by
    dsimp [K']
    exact Subgroup.normal_subgroupOf_of_le_normalizer hLnorm
  have hmapH₁ : H₁'.map L.subtype = H₁ := by
    exact Subgroup.map_subgroupOf_eq_of_le hH₁L
  have hmapH₂ : H₂'.map L.subtype = H₂ := by
    exact Subgroup.map_subgroupOf_eq_of_le hH₂L
  have hmapH₃ : H₃'.map L.subtype = H₃ := by
    exact Subgroup.map_subgroupOf_eq_of_le hH₃L
  have hrot₁ : ⁅⁅H₂', H₃'⁆, H₁'⁆ ≤ K' := by
    intro x hx
    change ((x : L) : G) ∈ K
    apply h₁
    have hxmap := Subgroup.mem_map_of_mem L.subtype hx
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      hmapH₁, hmapH₂, hmapH₃] at hxmap
    exact hxmap
  have hrot₂ : ⁅⁅H₃', H₁'⁆, H₂'⁆ ≤ K' := by
    intro x hx
    change ((x : L) : G) ∈ K
    apply h₂
    have hxmap := Subgroup.mem_map_of_mem L.subtype hx
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      hmapH₁, hmapH₂, hmapH₃] at hxmap
    exact hxmap
  have hresult : ⁅⁅H₁', H₂'⁆, H₃'⁆ ≤ K' :=
    Subgroup.commutator_commutator_le_of_rotate hrot₁ hrot₂
  intro x hx
  have hxmap : x ∈ (⁅⁅H₁', H₂'⁆, H₃'⁆).map L.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      hmapH₁, hmapH₂, hmapH₃]
    exact hx
  rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, rfl⟩
  exact hresult hy

end Subgroup
