module
public import Theory.SpecificGroups.CyclicTwoSymmetricFourSylow
public import Theory.GroupTheory.SymmetricFourModelCoreData

/-!
# Sylow two-subgroups of C₂ times S₄ are self-normalizing

Every supplied Sylow two-subgroup of a finite group isomorphic to C₂ × S₄
is its own normalizer. The existing Sylow model gives its order sixteen,
while the ambient model has order forty-eight and two-core of order eight.
Its index is therefore three, so its normalizer is either the Sylow itself
or the whole group. The latter would make it a normal two-subgroup,
contradicting the order of the two-core.

This intrinsic model fact supplies the local normalizer step in the
order-32 branch of Kurzweil–Stellmacher, The Theory of Finite Groups,
Chapter 12, printed p.367. No global simplicity, N₂ or Z hypothesis is used.
-/

namespace CyclicTwoSymmetricFour

/-- A Sylow two-subgroup of an actual C₂ × S₄ model is self-normalizing. -/
public theorem sylow_normalizer_eq_self
    {P : Type*} [Group P] [Finite P]
    (hModel : Nonempty (P ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))
    (T : Sylow 2 P) : Subgroup.normalizer (T : Set P) = (T : Subgroup P) := by
  obtain ⟨e⟩ := hModel
  have hPcard : Nat.card P = 48 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  obtain ⟨eT⟩ := sylow_two_equiv ⟨e⟩ T
  have hTcard : Nat.card T = 16 := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hidx : (T : Subgroup P).index = 3 := by
    have h := (T : Subgroup P).card_mul_index
    rw [hTcard, hPcard] at h
    omega
  have hcorecard : Nat.card (pCore 2 P) = 8 := by
    rcases (symmetric_four_model_twoCore_data (Or.inr ⟨e⟩)).2 with h | h
    · omega
    · exact h.1
  have hdvd := Subgroup.index_dvd_of_le (T : Subgroup P).le_normalizer
  rw [hidx] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hN | hN
  · have hnormal : (T : Subgroup P).Normal := Subgroup.normalizer_eq_top_iff.mp
      (Subgroup.index_eq_one.mp hN)
    have hle : (T : Subgroup P) ≤ pCore 2 P := le_sSup ⟨hnormal, T.isPGroup'⟩
    have hcard := Subgroup.card_le_of_le hle
    rw [hTcard, hcorecard] at hcard
    omega
  · have hrel := Subgroup.relIndex_mul_index (T : Subgroup P).le_normalizer
    rw [hN, hidx] at hrel
    have hrel1 : (T : Subgroup P).relIndex
        (Subgroup.normalizer ((T : Subgroup P) : Set P)) = 1 := by
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel1) (T : Subgroup P).le_normalizer

end CyclicTwoSymmetricFour
