module

public import Theory.GroupTheory.Hall.OddSylowComplement
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Odd Hall subgroups in normalized products

Restriction of a Hall subgroup to a normalized subgroup preserves the Hall
property: its order divides the original Hall order, and the product index
formula makes its index divide the original Hall index. An odd Hall subgroup
complements every Sylow two-subgroup. Conversely, an odd supplement to a
normalized two-subgroup is Hall.

These elementary forms of Hall theory are used for the compatible Cartan
complements in Aschbacher–Smith, F.1.3(5), printed p.260.
-/

@[expose] public section
namespace Subgroup.OddHall
open Subgroup
variable {G : Type*} [Group G]

/-- The primes different from two. -/
def oddPrimes : Set Nat.Primes := {p | p.val ≠ 2}

/-- An odd Hall subgroup complements the supplied Sylow two-subgroup. -/
theorem sylow_complement_of_hall [Finite G] (T : Sylow 2 G) {D : Subgroup G}
    (hd : IsHallSubgroup oddPrimes D) : (T : Subgroup G).IsComplement' D := by
  have ho : ¬ 2 ∣ Nat.card D := fun h => hd.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ h rfl
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hc : Nat.Coprime (Nat.card D) (Nat.card T) := by
    rw [hn]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr ho).symm.pow_right n
  have hi : Nat.Coprime (T : Subgroup G).index D.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpT hpD
    have hp2 : p = 2 := Classical.not_not.mp (hd.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpD)
    exact T.not_dvd_index (hp2 ▸ hpT)
  have hdi : Nat.card D ∣ (T : Subgroup G).index :=
    hc.dvd_of_dvd_mul_right (by simpa only [index_mul_card] using card_subgroup_dvd_card D)
  have hid : (T : Subgroup G).index ∣ Nat.card D :=
    hi.dvd_of_dvd_mul_right (by simpa only [card_mul_index] using (T : Subgroup G).index_dvd_card)
  apply isComplement'_of_coprime _ hc.symm
  rw [Nat.dvd_antisymm hdi hid]
  exact (T : Subgroup G).card_mul_index

/-- Hall restriction across a normalized product, without ambient finiteness. -/
theorem hall_restrict_of_normalizes {D B N : Subgroup G} [Finite D]
    (hd : IsHallSubgroup oddPrimes (D.subgroupOf B)) (hDB : D ≤ B)
    (hNB : N ≤ B) (hn : D ≤ normalizer (N : Set G)) :
    IsHallSubgroup oddPrimes (D.subgroupOf N) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    apply hd.p_in_pi_of_p_dvd_card p
    rw [Nat.card_congr (subgroupOfEquivOfLe hDB).toEquiv]
    have hc : Nat.card (D.subgroupOf N) ∣ Nat.card D := by
      rw [← inf_subgroupOf_right D N,
        Nat.card_congr (subgroupOfEquivOfLe (show D ⊓ N ≤ N from inf_le_right)).toEquiv]
      exact card_dvd_of_le inf_le_left
    exact hp.trans hc
  · intro p hp
    apply hd.p_in_pi_of_p_dvd_index p
    have hi : D.relIndex N ∣ D.relIndex B := by
      rw [← relIndex_sup_of_normalizes N D hn]
      exact dvd_of_mul_right_eq _ (relIndex_mul_relIndex D (N ⊔ D) B le_sup_right (sup_le hNB hDB))
    exact hp.trans hi

/-- An odd supplement to a normalized two-subgroup is Hall in their product. -/
theorem oddHall_of_normalized_sup {D T B : Subgroup G} [Finite D] [Finite T]
    (hT : IsPGroup 2 T) (ho : Nat.Coprime 2 (Nat.card D))
    (hn : D ≤ normalizer (T : Set G)) (hs : T ⊔ D = B) :
    IsHallSubgroup oddPrimes (D.subgroupOf B) := by
  have hDB : D ≤ B := hs ▸ le_sup_right
  refine ⟨?_, ?_⟩
  · intro p hp he
    have hp2 : p.val = 2 := he
    rw [Nat.card_congr (subgroupOfEquivOfLe hDB).toEquiv, hp2] at hp
    exact Nat.prime_two.coprime_iff_not_dvd.mp ho hp
  · intro p hp hp2
    obtain ⟨n, hnT⟩ := hT.exists_card_eq
    have hi : (D.subgroupOf B).index ∣ Nat.card T := by
      change D.relIndex B ∣ Nat.card T
      rw [← hs, relIndex_sup_of_normalizes T D hn]
      exact relIndex_dvd_card (H := D) (K := T)
    have hpT := hp.trans hi
    rw [hnT] at hpT
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two hpT)

/-- The index of the normalized factor in a subgroup product. -/
theorem relIndex_normalized_sup (A C : Subgroup G)
    (hn : C ≤ normalizer (A : Set G)) : A.relIndex (A ⊔ C) = A.relIndex C := by
  let J := A ⊔ C
  let : (A.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have he := relIndex_sup_left (C.subgroupOf J) (A.subgroupOf J)
  rw [← subgroupOf_sup (show A ≤ J from le_sup_left) (show C ≤ J from le_sup_right),
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf (show C ≤ J from le_sup_right)] at he
  exact he

end Subgroup.OddHall
