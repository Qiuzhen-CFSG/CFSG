module
public import Theory.GroupTheory.NormalizedSupConsequences
public import Mathlib.GroupTheory.Sylow

/-!
# The genuine Sylow in the product of commuting blocks

If S is a two-group normalizing each of two commuting factors and S∩Kᵢ is
Sylow in Kᵢ, then S is Sylow in K₁K₂S. The two indices in the subgroup
tower S≤K₁S≤K₁K₂S are odd. This constructs the Sylow required for the
global Gaschütz application from the individual C.5.4 Sylows.

Source: Aschbacher–Smith, C.5.4 and C.5.6(7), printed pp.155,159.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

theorem not_two_dvd_relIndex_of_sylow_intersection (S K : Subgroup G)
    (h : ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = S ⊓ K) :
    ¬ 2 ∣ S.relIndex K := by
  obtain ⟨P,hP⟩ := h
  have he : (P : Subgroup K) = S.subgroupOf K :=
    (map_injective K.subtype_injective) (hP.trans (subgroupOf_map_subtype S K).symm)
  change ¬ 2 ∣ (S.subgroupOf K).index
  rw [← he]
  exact P.not_dvd_index

theorem exists_sylow_normalized_join (S K : Subgroup G)
    (hS : IsPGroup 2 S) (hn : S ≤ normalizer (K : Set G))
    (hi : ¬ 2 ∣ S.relIndex K) :
    ∃ P : Sylow 2 (K ⊔ S : Subgroup G),
      (P : Subgroup (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = S := by
  let N := K ⊔ S
  have hp : IsPGroup 2 (S.subgroupOf N) :=
    hS.of_equiv (subgroupOfEquivOfLe (show S ≤ N from le_sup_right)).symm
  have hindex : ¬ 2 ∣ (S.subgroupOf N).index := by
    change ¬ 2 ∣ S.relIndex N
    rw [relIndex_sup_of_normalizes K S hn]
    exact hi
  exact ⟨hp.toSylow hindex,map_subgroupOf_eq_of_le le_sup_right⟩

theorem exists_sylow_two_block_join (S K L : Subgroup G)
    (hS : IsPGroup 2 S) (hSK : S ≤ normalizer (K : Set G))
    (hSL : S ≤ normalizer (L : Set G)) (hKL : K ≤ centralizer (L : Set G))
    (hK : ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = S ⊓ K)
    (hL : ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = S ⊓ L) :
    ∃ P : Sylow 2 ((K ⊔ L) ⊔ S : Subgroup G),
      (P : Subgroup ((K ⊔ L) ⊔ S : Subgroup G)).map ((K ⊔ L) ⊔ S).subtype = S := by
  have hSN : S ≤ normalizer (K ⊔ L : Subgroup G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (hSK hs),
      mem_normalizer_iff_map_conj_eq.mp (hSL hs)]
  apply exists_sylow_normalized_join S (K ⊔ L) hS hSN
  have h1 : ¬ 2 ∣ S.relIndex (K ⊔ S) := by
    rw [relIndex_sup_of_normalizes K S hSK]
    exact not_two_dvd_relIndex_of_sylow_intersection S K hK
  have h2 : ¬ 2 ∣ (K ⊔ S).relIndex (L ⊔ (K ⊔ S)) := by
    rw [relIndex_sup_of_normalizes L (K ⊔ S)
      (sup_le (hKL.trans (Subgroup.centralizer_le_normalizer _)) hSL)]
    exact fun hh => not_two_dvd_relIndex_of_sylow_intersection S L hL
      (hh.trans (relIndex_dvd_of_le_left L (show S ≤ K ⊔ S from le_sup_right)))
  have he := relIndex_mul_relIndex S (K ⊔ S) (L ⊔ (K ⊔ S)) le_sup_right le_sup_right
  have hi : ¬ 2 ∣ S.relIndex (L ⊔ (K ⊔ S)) := by
    rw [← he]
    exact fun hh => (Nat.prime_two.dvd_mul.mp hh).elim h1 h2
  have hindex : ¬ 2 ∣ S.relIndex ((K ⊔ L) ⊔ S) := by
    simpa only [sup_assoc,sup_left_comm] using hi
  rw [relIndex_sup_of_normalizes (K ⊔ L) S hSN] at hindex
  exact hindex
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
