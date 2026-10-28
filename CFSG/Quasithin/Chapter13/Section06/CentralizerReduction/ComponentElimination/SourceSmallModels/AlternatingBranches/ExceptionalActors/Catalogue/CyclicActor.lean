module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Intrinsic
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The cyclic exceptional A₇ actor

An order-three subgroup normalized by a Sylow two-subgroup of A₇ is generated
by a single three-cycle. Otherwise its generator is a double three-cycle.
The latter has centralizer of order eighteen in S₇, and the automorphism group
of its cyclic subgroup has order two. Its normalizer thus has order dividing
36, which cannot contain the Sylow subgroup's eight elements.

This argument works with the actual subgroup and the literal permutation
embedding. It supplies the trivial-two-core branch of the actor witness.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors

private theorem normalizer_doubleThree_dvd (a : Equiv.Perm (Fin 7))
    (ha : orderOf a = 3) (ht : ¬ a.IsThreeCycle) :
    Nat.card (normalizer (zpowers a : Set (Equiv.Perm (Fin 7)))) ∣ 36 := by
  have hct : a.cycleType = {3, 3} := by
    obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (by rw [ha]; exact Nat.prime_three)
    rw [ha] at hn
    have hs := a.sum_cycleType_le
    rw [hn, Multiset.sum_replicate] at hs
    simp only [Fintype.card_fin, smul_eq_mul] at hs
    have hnle : n ≤ 1 := by omega
    interval_cases n
    · exact False.elim (ht (by simpa [Equiv.Perm.IsThreeCycle] using hn))
    · simpa using hn
  let H := zpowers a
  let f := H.normalizerMonoidHom
  have hAut : Nat.card (MulAut H) = 2 := by
    rw [IsCyclic.card_mulAut, Nat.card_zpowers, ha]
    decide
  have hr : Nat.card f.range ∣ 2 := hAut ▸ f.range.card_subgroup_dvd_card
  have hk : Nat.card f.ker = 18 := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe
        (centralizer_le_normalizer (H : Set (Equiv.Perm (Fin 7))))).toEquiv]
    change Nat.card (centralizer (zpowers a : Set (Equiv.Perm (Fin 7)))) = 18
    rw [zpowers_eq_closure, centralizer_closure, Equiv.Perm.nat_card_centralizer, hct]
    norm_num
  have hh := Nat.mul_dvd_mul (dvd_of_eq hk) hr
  have hp := f.ker.card_mul_index
  rw [index_ker] at hp
  simpa only [hp] using hh

theorem threeCycle_mem_of_card_three (S : Sylow 2 A7) (D : Subgroup A7)
    (hD : Nat.card D = 3) (hN : (S : Subgroup A7) ≤ normalizer (D : Set A7)) :
    ∃ a ∈ D, Equiv.Perm.IsThreeCycle a.val := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hD])
  have hoa : orderOf a.val = 3 := (Subgroup.orderOf_coe a).trans ha
  have hz : zpowers a.val = D := eq_of_le_of_card_ge
    (zpowers_le.mpr a.property) (by rw [Nat.card_zpowers, hoa, hD])
  refine ⟨a.val, a.property, ?_⟩
  by_contra ht
  let f := (alternatingGroup (Fin 7)).subtype
  have hn : (S : Subgroup A7).map f ≤ normalizer (zpowers a.val.val : Set _) := by
    change (S : Subgroup A7).map f ≤ normalizer (zpowers (f a.val) : Set (Equiv.Perm (Fin 7)))
    rw [← MonoidHom.map_zpowers f a.val, hz]
    exact (map_mono hN).trans (D.le_normalizer_map f)
  have hd := (card_dvd_of_le hn).trans
    (normalizer_doubleThree_dvd a.val.val ((Subgroup.orderOf_coe a.val).trans hoa) ht)
  rw [card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective] at hd
  have hc : Nat.card A7 = 2520 := by
    have hh := two_mul_nat_card_alternatingGroup (α := Fin 7)
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hh ⊢
    omega
  have h8 : 2 ^ 3 ∣ Nat.card S :=
    S.pow_dvd_card_of_pow_dvd_card (by rw [hc]; decide)
  have hbad : 8 ∣ 36 := h8.trans hd
  norm_num at hbad

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
