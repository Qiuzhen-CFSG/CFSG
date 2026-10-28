module
public import Theory.SpecificGroups.Alternating.SevenFiveSection
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Binary-three sections inside A₇

A normal two-subgroup with quotient of order 168 has order dividing the odd
index 15, so it is trivial. The resulting subgroup is maximal: a larger
proper overgroup would have index at most five, contradicting the faithful
coset-action bound for A₇. Simplicity then makes it self-normalizing.
The image results retain the original homomorphism and its two-group kernel.

These facts supply the smaller-image obstruction in the constrained branch
of Aschbacher--Smith 10.2.9, printed pp.751--752.
-/

public noncomputable section
open Subgroup
namespace alternatingGroup.SevenThreeSection

private theorem card_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem normal_two_subgroup_eq_bot_of_quotient_card
    (B : Subgroup (alternatingGroup (Fin 7))) (N : Subgroup B) [N.Normal]
    (hN : IsPGroup 2 N) (hq : Nat.card (B ⧸ N) = 168) : N = ⊥ := by
  have hc : Nat.card B = 168 * Nat.card N := by
    rw [card_eq_card_quotient_mul_card_subgroup N, hq]
  have hd : Nat.card N ∣ 15 := by
    have hh := B.card_subgroup_dvd_card
    rw [hc, card_seven] at hh
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 168) hh
  have hcop : Nat.Coprime (Nat.card N) 15 := by
    obtain ⟨n,hn⟩ := hN.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 15).pow_left n
  exact card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hd)

theorem twoCore_eq_bot (B : Subgroup (alternatingGroup (Fin 7)))
    (e : (B ⧸ pCore 2 B) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    pCore 2 B = ⊥ := by
  apply normal_two_subgroup_eq_bot_of_quotient_card B _ pCore_isPGroup
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL]

theorem card_eq (B : Subgroup (alternatingGroup (Fin 7)))
    (e : (B ⧸ pCore 2 B) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Nat.card B = 168 := by
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B),
    Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL, twoCore_eq_bot B e, card_bot, mul_one]

private theorem index_le_six_eq_top (B : Subgroup (alternatingGroup (Fin 7)))
    (hi : B.index ≤ 6) : B = ⊤ := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
  have hh := Nat.factorial_le hi
  rw [card_seven]
  norm_num [Nat.factorial] at hh ⊢
  omega

theorem eq_of_le_of_card (B N : Subgroup (alternatingGroup (Fin 7)))
    (hB : Nat.card B = 168) (hBN : B ≤ N) (hN : N ≠ ⊤) : N = B := by
  have hindex : B.index = 15 := by
    have hh := B.card_mul_index
    rw [hB, card_seven] at hh
    omega
  have hd : N.index ∣ 15 := hindex ▸ index_dvd_of_le hBN
  have hlow : 7 ≤ N.index := by
    by_contra hn
    exact hN (index_le_six_eq_top N (by omega))
  have he : N.index = 15 := by
    have hb := Nat.le_of_dvd (by decide : 0 < 15) hd
    interval_cases N.index <;> omega
  have hc := N.card_mul_index
  rw [he, card_seven] at hc
  exact (eq_of_le_of_card_ge hBN (by omega)).symm

theorem normalizer_eq (B : Subgroup (alternatingGroup (Fin 7)))
    (e : (B ⧸ pCore 2 B) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    normalizer (B : Set (alternatingGroup (Fin 7))) = B := by
  have hc := card_eq B e
  apply eq_of_le_of_card B _ hc B.le_normalizer
  intro hn
  let : B.Normal := normalizer_eq_top_iff.mp hn
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : B.Normal).eq_bot_or_eq_top with hb | ht
  · rw [hb, card_bot] at hc
    norm_num at hc
  · rw [ht, card_top, card_seven] at hc
    norm_num at hc

theorem image_twoCore_eq_bot_and_ker_eq {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (L : Subgroup G)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    pCore 2 (L.map f) = ⊥ ∧ (f.subgroupMap L).ker = pCore 2 L := by
  let d := ((f.subgroupMap L).pCoreQuotientEquiv (f.subgroupMap_surjective L) hk).symm.trans e
  have hbot := twoCore_eq_bot (L.map f) d
  refine ⟨hbot, ?_⟩
  have hh := (f.subgroupMap L).comap_pCore_of_ker_isPGroup
    (f.subgroupMap_surjective L) hk
  rwa [hbot] at hh

theorem image_normalizer_eq {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (L : Subgroup G)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    normalizer (L.map f : Set (alternatingGroup (Fin 7))) = L.map f :=
  normalizer_eq _ (((f.subgroupMap L).pCoreQuotientEquiv
    (f.subgroupMap_surjective L) hk).symm.trans e)

end alternatingGroup.SevenThreeSection
