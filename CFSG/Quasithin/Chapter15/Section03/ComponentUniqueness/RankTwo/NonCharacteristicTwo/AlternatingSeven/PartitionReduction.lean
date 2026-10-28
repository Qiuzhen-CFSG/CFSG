module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.PartitionObstruction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PermutationOvergroups
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# The odd-core obstruction in a solvable seven-point Sylow overgroup

The actual solvable-overgroup theorem places YP in one of two partition
stabilizers. Three-rank two forces nine to divide |Y|, ruling out the pair
stabilizer of order 48. Inside the (4,3)-stabilizer of order 144, the normal
three-point factor must lie in Y: otherwise its product with Y would have
order divisible by 27. Thus O₃(Y) is nontrivial. All transport is through
injective maps and subgroup equivalences, without an odd-subgroup lift across
a centralizer quotient.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.42,
printed p.1138, using the partition geometry of 13.8.24, pp.958--959.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.AlternatingSeven
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open LocalGeometry.PermutationOvergroups PartitionObstruction

/-- Three-rank two forces a factor of nine in the group order. -/
theorem nine_dvd_of_threeRank_two {H : Type*} [Group H] [Finite H]
    (hrank : primeRank 3 H = 2) : 9 ∣ Nat.card H := by
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := H)
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  by_contra h9
  have hnle : n ≤ 1 := by
    by_contra! hh
    have hd : 9 ∣ Nat.card P := by
      rw [hn]
      exact Nat.pow_dvd_pow 3 hh
    exact h9 (hd.trans (P : Subgroup H).card_subgroup_dvd_card)
  have hcyc : IsCyclic P := isCyclic_of_card_dvd_prime (p := 3) (by
    rw [hn]
    interval_cases n <;> norm_num)
  have hle := P.primeRank_le_one_of_isCyclic hcyc
  rw [hrank] at hle
  omega

/-- Nine forces the normal three-point factor into every subgroup of the
partition stabilizer. The argument only uses its actual order 144. -/
theorem contains_threeCycles_of_nine (J : Subgroup fourThreeStabilizer)
    (h9 : 9 ∣ Nat.card J) : threeCycles ≤ J := by
  have hd : Nat.card (threeCycles ⊓ J : Subgroup fourThreeStabilizer) ∣ 3 := by
    simpa only [card_threeCycles] using card_dvd_of_le
      (show threeCycles ⊓ J ≤ threeCycles from inf_le_left)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hc | hc
  · have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes threeCycles J
      (by rw [normalizer_eq_top]; exact le_top)
    rw [card_threeCycles, hc, one_mul] at hh
    have h27 : 27 ∣ Nat.card (threeCycles ⊔ J : Subgroup fourThreeStabilizer) := by
      rw [← hh]
      exact Nat.mul_dvd_mul_left 3 h9
    have hbad : 27 ∣ 144 := by
      simpa only [fourThreeStabilizer_card] using
        h27.trans (threeCycles ⊔ J : Subgroup fourThreeStabilizer).card_subgroup_dvd_card
    norm_num at hbad
  · have he : threeCycles ⊓ J = threeCycles :=
      eq_of_le_of_card_ge inf_le_left (by rw [hc, card_threeCycles])
    exact inf_eq_left.mp he

/-- The factor of order three gives a nontrivial intrinsic three-core. -/
theorem threeCore_ne_bot_of_nine (J : Subgroup fourThreeStabilizer)
    (h9 : 9 ∣ Nat.card J) : pCore 3 J ≠ ⊥ := by
  have hC := contains_threeCycles_of_nine J h9
  have hc : Nat.card (threeCycles.subgroupOf J) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv).trans card_threeCycles
  have hp : IsPGroup 3 (threeCycles.subgroupOf J) := IsPGroup.of_card (by simpa using hc :
    Nat.card (threeCycles.subgroupOf J) = 3 ^ 1)
  have hle : threeCycles.subgroupOf J ≤ pCore 3 J := le_sSup ⟨inferInstance, hp⟩
  intro hz
  have he := (threeCycles.subgroupOf J).card_eq_one.mpr (le_bot_iff.mp (hz ▸ hle))
  omega

private theorem solvable_placement_short (B : Subgroup S7)
    (hB : alternatingGroup (Fin 7) ≤ B) (P : Sylow 2 B) (H : Subgroup B)
    [Group.IsSolvable H] (hPH : (P : Subgroup B) ≤ H) :
    ∃ (σ : S7) (R : Subgroup S7),
      (R = fourThreeStabilizer ∨ R = pairStabilizer) ∧
      let ψ := (MulAut.conj σ).toMonoidHom.comp B.subtype
      H.map ψ ≤ R ∧ (P : Subgroup B).map ψ = (standardTwoIn B).map B.subtype := by
  obtain ⟨σ, R, hR, _, hle, _, _, hP, _, _, _⟩ :=
    solvable_sylow_overgroup_compatible_placement B hB P H hPH
  exact ⟨σ, R, hR, map_le_iff_le_comap.mpr hle, hP⟩

/-- A solvable Sylow overgroup with three-rank two has the four-plus-three
placement. The pair stabilizer is excluded by its order 48. -/
theorem fourThree_placement (Q : Subgroup (alternatingGroup (Fin 7)))
    (P : Sylow 2 (alternatingGroup (Fin 7)))
    [Group.IsSolvable (Q ⊔ (P : Subgroup _) : Subgroup _)]
    (hrank : primeRank 3 Q = 2) :
    ∃ σ : S7, let ψ := (MulAut.conj σ).toMonoidHom.comp (alternatingGroup (Fin 7)).subtype
      (Q ⊔ (P : Subgroup _)).map ψ ≤ fourThreeStabilizer ∧
      (P : Subgroup _).map ψ = standardEvenTwo.map (alternatingGroup (Fin 7)).subtype := by
  obtain ⟨σ, R, hR, hle, hP⟩ :=
    solvable_placement_short (alternatingGroup (Fin 7)) le_rfl P
      (Q ⊔ (P : Subgroup (alternatingGroup (Fin 7)))) le_sup_right
  let ψ := (MulAut.conj σ).toMonoidHom.comp (alternatingGroup (Fin 7)).subtype
  have hψ : Function.Injective ψ :=
    (MulAut.conj σ).injective.comp (alternatingGroup (Fin 7)).subtype_injective
  have h9 : 9 ∣ Nat.card (Q.map ψ) := by
    rw [card_map_of_injective hψ]
    exact nine_dvd_of_threeRank_two hrank
  rcases hR with rfl | rfl
  · exact ⟨σ, hle, hP⟩
  · have hQ : Q.map ψ ≤ pairStabilizer :=
      (map_mono le_sup_left).trans hle
    exact (nine_not_dvd_pairStabilizer_card (h9.trans (card_dvd_of_le hQ))).elim

/-- Every rank-two subgroup of A₇ in a solvable Sylow overgroup has a
nontrivial three-core, transported from the literal partition action. -/
theorem model_threeCore_ne_bot (Q : Subgroup (alternatingGroup (Fin 7)))
    (P : Sylow 2 (alternatingGroup (Fin 7)))
    [Group.IsSolvable (Q ⊔ (P : Subgroup _) : Subgroup _)]
    (hrank : primeRank 3 Q = 2) : pCore 3 Q ≠ ⊥ := by
  obtain ⟨σ, hplace, _⟩ := fourThree_placement Q P hrank
  let ψ := (MulAut.conj σ).toMonoidHom.comp (alternatingGroup (Fin 7)).subtype
  have hψ : Function.Injective ψ :=
    (MulAut.conj σ).injective.comp (alternatingGroup (Fin 7)).subtype_injective
  have hQ : Q.map ψ ≤ fourThreeStabilizer := (map_mono le_sup_left).trans hplace
  let J := (Q.map ψ).subgroupOf fourThreeStabilizer
  let e : Q ≃* J := (Q.equivMapOfInjective ψ hψ).trans (subgroupOfEquivOfLe hQ).symm
  have h9 : 9 ∣ Nat.card J := by
    rw [← Nat.card_congr e.toEquiv]
    exact nine_dvd_of_threeRank_two hrank
  intro hz
  apply threeCore_ne_bot_of_nine J h9
  rw [← pCore_map_iso 3 e, hz, Subgroup.map_bot]

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.AlternatingSeven
