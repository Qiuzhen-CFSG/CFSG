module
public import Theory.GroupTheory.IndexTwoDihedralNormalizer

/-!
# Sylow placement above a cubic factor

In a commuting product of two groups of order six, a nontrivial two-subgroup
of the first factor generates an index-three subgroup with the whole second
factor. An odd-index subgroup contains a Sylow two-subgroup of the overgroup.
The latter statement uses the literal ambient embeddings.

These counting and Sylow arguments are used in the rank-eight exclusion of
Aschbacher--Smith 14.6.17, printed p.1036.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The first involution and the second cubic factor generate an index-three subgroup. -/
theorem cubic_factor_join_relIndex
    (A B C : Subgroup G) (hAB : Disjoint A B)
    (hc : A ≤ centralizer (B : Set G))
    (hA : Nat.card A = 6) (hB : Nat.card B = 6)
    (hCA : C ≤ A) (hp : IsPGroup 2 C) (hne : C ≠ ⊥) :
    (C ⊔ B).relIndex (A ⊔ B) = 3 := by
  have hd : Nat.card C ∣ 2 * 3 := by simpa only [hA] using card_dvd_of_le hCA
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card C) 3 := by
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hc2 : Nat.card C ≤ 2 := Nat.le_of_dvd (by decide)
    (hcop.dvd_of_dvd_mul_right hd)
  have hcn : 1 < Nat.card C := C.one_lt_card_iff_ne_bot.mpr hne
  have hcC : Nat.card C = 2 := by omega
  obtain ⟨eAB,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hAB hc
  obtain ⟨eCB,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C B
    (hAB.mono_left hCA) (hCA.trans hc)
  have hcAB : Nat.card ↥(A ⊔ B) = 36 := by
    rw [← Nat.card_congr eAB.toEquiv,Nat.card_prod,hA,hB]
  have hcCB : Nat.card ↥(C ⊔ B) = 12 := by
    rw [← Nat.card_congr eCB.toEquiv,Nat.card_prod,hcC,hB]
  have hle : C ⊔ B ≤ A ⊔ B := sup_le_sup_right hCA B
  have hh := ((C ⊔ B).subgroupOf (A ⊔ B)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,hcCB,hcAB] at hh
  change 12 * (C ⊔ B).relIndex (A ⊔ B) = 36 at hh
  omega

/-- A subgroup of odd index contains an ambient Sylow two-subgroup. -/
theorem exists_sylow_map_le_of_odd_relIndex
    (E K : Subgroup G) (hEK : E ≤ K) (hi : Odd (E.relIndex K)) :
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype ≤ E := by
  let J := E.subgroupOf K
  let P : Sylow 2 J := Sylow.nonempty.some
  let Q := (P : Subgroup J).map J.subtype
  have hp : IsPGroup 2 Q := P.isPGroup'.map J.subtype
  have hind : ¬ 2 ∣ Q.index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two P.not_dvd_index hi.not_two_dvd_nat
  refine ⟨hp.toSylow hind,?_⟩
  change Q.map K.subtype ≤ E
  exact (map_mono (map_subtype_le _)).trans_eq (map_subgroupOf_eq_of_le hEK)

end Subgroup
