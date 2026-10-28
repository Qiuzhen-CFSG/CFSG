module
public import Theory.GroupTheory.SylowPrimeIndexSelfNormalizer
public import Theory.GroupTheory.PCoreSurjective
/-!
# Sylow normalizers in the small rank-one core quotients

The quotient orders6,10,20 give Sylow index3 or5 through the normal
binary core. These Sylow subgroups are nonnormal, hence self-normalizing;
prime index also leaves no proper intermediate overgroup. These are the
local Borel facts needed to construct the original14.2.20 amalgam.
Source: Aschbacher--Smith14.2.20--21, printed p.988.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem sylow_index_small_core_quotient (S : Sylow 2 G)
    (hc : Nat.card (G ⧸ pCore 2 G) = 6 ∨ Nat.card (G ⧸ pCore 2 G) = 10 ∨
      Nat.card (G ⧸ pCore 2 G) = 20) : S.index = 3 ∨ S.index = 5 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hi : P.index = S.index := (S : Subgroup G).index_map_eq
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S)
  have hcount := (P : Subgroup (G ⧸ pCore 2 G)).index_mul_card
  have hPc := P.card_eq_multiplicity
  rcases hc with hc | hc | hc
  all_goals rw [hc] at hPc hcount
  · norm_num [show (Nat.factorization 6) 2 = 1 from by decide +kernel] at hPc
    rw [hPc,hi] at hcount
    omega
  · norm_num [show (Nat.factorization 10) 2 = 1 from by decide +kernel] at hPc
    rw [hPc,hi] at hcount
    omega
  · norm_num [show (Nat.factorization 20) 2 = 2 from by decide +kernel] at hPc
    rw [hPc,hi] at hcount
    omega

theorem sylow_normalizer_small_core_quotient (S : Sylow 2 G)
    (hc : Nat.card (G ⧸ pCore 2 G) = 6 ∨ Nat.card (G ⧸ pCore 2 G) = 10 ∨
      Nat.card (G ⧸ pCore 2 G) = 20) :
    normalizer (S : Set G) = (S : Subgroup G) ∧
      ∀ K : Subgroup G, (S : Subgroup G) ≤ K → K < ⊤ → K = S := by
  have hi : S.index.Prime := (sylow_index_small_core_quotient S hc).elim
    (fun h => h ▸ Nat.prime_three) (fun h => h ▸ Nat.prime_five)
  have hnot : ¬ (S : Subgroup G) ≤ pCore 2 G := by
    intro hs
    let q := QuotientGroup.mk' (pCore 2 G)
    let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
    have hne := P.ne_bot_of_dvd_card (hc.elim (fun h => by rw [h]; decide)
      (fun h => h.elim (fun h => by rw [h]; decide) (fun h => by rw [h]; decide)))
    apply hne
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact hs)
  refine ⟨S.normalizer_eq_of_prime_index_not_le_core hi hnot,?_⟩
  intro K hSK hK
  have he := relIndex_mul_index hSK
  have hp : ((S : Subgroup G).relIndex K * K.index).Prime := he.symm ▸ hi
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hKi⟩ | ⟨_,hrel⟩
  · exact (hK.ne (index_eq_one.mp hKi)).elim
  · exact (relIndex_eq_one.mp hrel).antisymm hSK

end Theory.GroupTheory
