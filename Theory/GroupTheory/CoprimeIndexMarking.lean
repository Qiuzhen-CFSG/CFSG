module

public import Mathlib.GroupTheory.Sylow

/-!
# Subgroup markings at coprime index

Coprime subgroup indices force generation. A normal subgroup of index prime
to p contains every p-subgroup, and a Sylow subgroup of a subgroup of index
prime to p stays Sylow after the literal subtype inclusion. These elementary
index arguments preserve the embeddings needed for subgroup amalgams.
-/

@[expose] public section

namespace Subgroup
variable {G : Type*} [Group G]

/-- Subgroups with coprime indices generate the ambient group. -/
theorem sup_eq_top_of_coprime_index (H K : Subgroup G)
    (h : H.index.Coprime K.index) : H ⊔ K = ⊤ := by
  apply Subgroup.index_eq_one.mp
  exact Nat.eq_one_of_dvd_coprimes h (Subgroup.index_dvd_of_le le_sup_left)
    (Subgroup.index_dvd_of_le le_sup_right)

end Subgroup

namespace IsPGroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

/-- A normal subgroup of index prime to p contains each p-subgroup. -/
theorem le_normal_of_index_primeTo (N P : Subgroup G) [N.Normal]
    (hP : IsPGroup p P) (hN : ¬ p ∣ N.index) : P ≤ N := by
  apply Subgroup.relIndex_eq_one.mp
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  apply Nat.eq_one_of_dvd_coprimes
    (hp.out.coprime_pow_of_not_dvd (m := n) hN)
  · exact N.relIndex_dvd_index_of_normal P
  · simpa only [hn] using N.relIndex_dvd_card P

end IsPGroup

namespace Sylow
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- The literal inclusion of a Sylow subgroup through a subgroup of prime-to-p index. -/
def mapSubtypeOfIndexPrimeTo {H : Subgroup G} (P : Sylow p H)
    (hH : ¬ p ∣ H.index) [Finite H] : Sylow p G :=
  (P.isPGroup'.map H.subtype).toSylow (by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out P.not_dvd_index hH)

@[simp] theorem coe_mapSubtypeOfIndexPrimeTo {H : Subgroup G} (P : Sylow p H)
    (hH : ¬ p ∣ H.index) [Finite H] :
    (P.mapSubtypeOfIndexPrimeTo hH : Subgroup G) = (P : Subgroup H).map H.subtype := rfl

end Sylow
