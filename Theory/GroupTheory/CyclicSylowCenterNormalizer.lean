module
public import Theory.GroupTheory.CyclicTwoAut
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Normalizers of cyclic subgroups in a Sylow two-center

A cyclic subgroup C contained in and centralized by a Sylow two-subgroup
P has centralizing ambient normalizer. This elementary local argument
supplies the fixed-center step for ABG Chapter II Section 1 Proposition 2,
article p. 12, before restricting the quaternion central-product action.

The normalizer action on C has a two-group automorphism target. Its image
order, the normalizer-centralizer index, thus divides a power of two.
Since P centralizes C, the same index divides the odd index of P in the
ambient finite group. Coprimality forces the action image to be trivial.
The statement uses only the displayed containment and centralization
hypotheses and has no campaign imports.
-/

namespace Subgroup

/-- A cyclic subgroup of the center of a Sylow two-subgroup has trivial automizer. -/
public theorem normalizer_le_centralizer_of_cyclic_sylow_center
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (C : Subgroup G) [IsCyclic C] (hCP : C ≤ P)
    (hPC : (P : Subgroup G) ≤ centralizer (C : Set G)) :
    normalizer (C : Set G) ≤ centralizer (C : Set G) := by
  let N := normalizer (C : Set G)
  let Z := centralizer (C : Set G)
  have hC : IsPGroup 2 C := P.isPGroup'.to_le hCP
  obtain ⟨k, hk⟩ := hC.mulAut_of_isCyclic_two.exists_card_eq
  have hauto : Z.relIndex N ∣ 2 ^ k := by
    have h := C.normalizerMonoidHom.range.card_subgroup_dvd_card
    rw [← Subgroup.index_ker, Subgroup.normalizerMonoidHom_ker] at h
    exact h.trans (hk ▸ dvd_rfl)
  have hindex : Z.relIndex N ∣ (P : Subgroup G).index :=
    (Subgroup.relIndex_dvd_of_le_left N hPC).trans
      (Subgroup.relIndex_dvd_index_of_le (hPC.trans (centralizer_le_normalizer _)))
  have hcop : Nat.Coprime ((P : Subgroup G).index) (2 ^ k) := by
    exact ((Nat.prime_two.coprime_iff_not_dvd.mpr P.not_dvd_index).symm).pow_right k
  exact Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop hindex hauto)

end Subgroup
