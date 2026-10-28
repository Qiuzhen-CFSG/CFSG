module
public import Theory.SpecificGroups.BinaryLinear.FourTwoLocalFive
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.SymmetricSeven.OddNormalizers
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Mathlib.GroupTheory.Perm.Centralizer
public import Theory.GroupTheory.PrimeRankHom

/-!
# Two-subgroups normalized by six-point alternating sections

The actual A8 ≃ GL4(2) comparison makes every nontrivial even two-subgroup
normalizer prime to five. Restriction gives the same assertion in A7.
In S7, an odd two-subgroup normalizer has three-rank at most one. In S8,
trivial even intersection makes the two-subgroup have order two. A factor
five in its centralizer forces a transposition; that centralizer has order
1440 and cannot contain a full Sylow two-subgroup of A8.

These are intrinsic permutation-group exclusions. Their C.2.7 application
retains the actual A6 image, radical and inherited Sylow subgroup.
Source: Aschbacher--Smith 3.3.22, printed p.597, excluding the alternating
source models in C.2.7, pp.145--147. The cycle-type calculation follows the
existing SymmetricSeven/OddNormalizers proof and Mathlib's centralizer formula.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.AlternatingSixNormalizer

private def eightLinear : alternatingGroup (Fin 8) ≃* BinaryLinear.OuterCyclic.LinearGroup 4 :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide))

/-- No nontrivial two-subgroup in A8 has a normalizer with a factor five. -/
theorem eight_five_not_dvd_normalizer (Q : Subgroup (alternatingGroup (Fin 8)))
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    ¬5 ∣ Nat.card (normalizer (Q : Set (alternatingGroup (Fin 8)))) := by
  intro hd
  apply BinaryLinear.FourTwoLocalFive.five_not_dvd_normalizer
    (Q.map eightLinear.toMonoidHom) (hQ.map _) (by
      intro hh
      exact hne ((Q.map_eq_bot_iff_of_injective eightLinear.injective).mp hh))
  rwa [←map_equiv_normalizer_eq,card_map_of_injective eightLinear.injective]

private def sevenEight : alternatingGroup (Fin 7) →* alternatingGroup (Fin 8) := by
  let s : Finset (Fin 8) := Finset.univ.erase 7
  let e : Fin 7 ≃ s := Fintype.equivOfCardEq (by decide)
  exact (alternatingGroup.ofSubtype s).comp e.altCongrHom.toMonoidHom

private theorem sevenEight_injective : Function.Injective sevenEight := by
  unfold sevenEight
  exact alternatingGroup.ofSubtype_injective.comp (Equiv.altCongrHom _).injective

/-- The same two-local exclusion holds in the actual seven-letter subgroup. -/
theorem seven_five_not_dvd_normalizer (Q : Subgroup (alternatingGroup (Fin 7)))
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    ¬5 ∣ Nat.card (normalizer (Q : Set (alternatingGroup (Fin 7)))) := by
  intro hd
  apply eight_five_not_dvd_normalizer (Q.map sevenEight) (hQ.map _) (by
    intro hh
    exact hne ((Q.map_eq_bot_iff_of_injective sevenEight_injective).mp hh))
  have hm := Q.le_normalizer_map sevenEight
  have hc : Nat.card ((normalizer (Q : Set (alternatingGroup (Fin 7)))).map sevenEight) =
      Nat.card (normalizer (Q : Set (alternatingGroup (Fin 7)))) := card_map_of_injective sevenEight_injective
  exact (hc.symm ▸ hd).trans (card_dvd_of_le hm)

private theorem even_intersection_eq_bot {n : ℕ}
    (hfive : ∀ Q : Subgroup (alternatingGroup (Fin n)),
      IsPGroup 2 Q → Q ≠ ⊥ → ¬5 ∣ Nat.card (normalizer (Q : Set (alternatingGroup (Fin n)))))
    (Q N : Subgroup (Equiv.Perm (Fin n))) (hQ : IsPGroup 2 Q)
    (hN : N ≤ alternatingGroup (Fin n)) (hn : N ≤ normalizer (Q : Set _))
    (h5 : 5 ∣ Nat.card N) : Q ⊓ alternatingGroup (Fin n) = ⊥ := by
  have he : Q.subgroupOf (alternatingGroup (Fin n)) = ⊥ := by
    by_contra he
    apply hfive _ hQ.comap_subtype he
    have hNN : N.subgroupOf (alternatingGroup (Fin n)) ≤
        normalizer (Q.subgroupOf (alternatingGroup (Fin n)) : Set _) := by
      intro x hx
      apply mem_normalizer_iff.mpr
      intro y
      exact mem_normalizer_iff.mp (hn hx) y.val
    have hc : Nat.card (N.subgroupOf (alternatingGroup (Fin n))) = Nat.card N :=
      Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv
    exact (hc.symm ▸ h5).trans (card_dvd_of_le hNN)
  have hh := congrArg (map (alternatingGroup (Fin n)).subtype) he
  simpa only [subgroupOf_map_subtype,Subgroup.map_bot] using hh

/-- A rank-two subgroup with a factor five in A7 normalizes no nontrivial
permutation two-subgroup, including outer ones. -/
theorem seven_no_normalized_two
    (Q N : Subgroup (Equiv.Perm (Fin 7))) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hN : N ≤ alternatingGroup (Fin 7)) (hn : N ≤ normalizer (Q : Set _))
    (h5 : 5 ∣ Nat.card N) (hr : 2 ≤ primeRank 3 N) : False := by
  have he := even_intersection_eq_bot seven_five_not_dvd_normalizer Q N hQ hN hn h5
  have hodd : ¬Q ≤ alternatingGroup (Fin 7) := by
    intro hh
    exact hne ((inf_eq_left.mpr hh).symm.trans he)
  have hb := (_root_.primeRank_le_of_injective 3 (inclusion hn)
    (inclusion_injective hn)).trans
    (Theory.SpecificGroups.SymmetricSeven.OddNormalizers.normalizer_rank Q hQ hodd)
  omega

private theorem card_two_of_even_intersection_bot {n : ℕ}
    (Q : Subgroup (Equiv.Perm (Fin n))) (hne : Q ≠ ⊥)
    (he : Q ⊓ alternatingGroup (Fin n) = ⊥) : Nat.card Q = 2 := by
  let f := Equiv.Perm.sign.comp Q.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←he]
    exact ⟨x.property,Equiv.Perm.mem_alternatingGroup.mpr hx⟩
  have hl := Nat.card_le_card_of_injective f hf
  have hn : 1 < Nat.card Q := Finite.one_lt_card_iff_nontrivial.mpr
    ((nontrivial_iff_ne_bot Q).mpr hne)
  have hc : Nat.card (ℤˣ) = 2 := by simp [Nat.card_eq_fintype_card]
  rw [hc] at hl
  omega

private theorem involution_isSwap_of_five_centralizer
    (z : Equiv.Perm (Fin 8)) (hz : z ^ 2 = 1) (hne : z ≠ 1)
    (h5 : 5 ∣ Nat.card (centralizer ({z} : Set (Equiv.Perm (Fin 8))))) : z.IsSwap := by
  have ht := Equiv.Perm.cycleType_of_pow_prime_eq_one hz
  have hs := z.support.card_le_univ
  have hs' := z.sum_cycleType
  rw [ht,Multiset.sum_replicate] at hs'
  have hp : 0 < z.cycleType.card := by
    apply Nat.pos_of_ne_zero
    intro hh
    exact hne (Equiv.Perm.cycleType_eq_zero.mp (Multiset.card_eq_zero.mp hh))
  have hb : z.cycleType.card ≤ 4 := by
    simp only [Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hs hs'
    omega
  have h1 : z.cycleType.card = 1 := by
    rw [Equiv.Perm.nat_card_centralizer,ht] at h5
    interval_cases hh : z.cycleType.card <;>
      first | rfl | norm_num [Nat.factorial] at h5
  apply Equiv.Perm.isSwap_iff_cycleType.mpr
  rw [ht,h1]
  rfl

/-- The even normalizer obstruction and the inherited full Sylow exclude
also the outer two-subgroup case in S8. -/
theorem eight_no_normalized_two
    (Q N : Subgroup (Equiv.Perm (Fin 8))) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hN : N ≤ alternatingGroup (Fin 8)) (hn : N ≤ normalizer (Q : Set _))
    (h5 : 5 ∣ Nat.card N)
    (U : Sylow 2 (alternatingGroup (Fin 8)))
    (hU : (U : Subgroup _).map (alternatingGroup (Fin 8)).subtype ≤ normalizer (Q : Set _)) :
    False := by
  have he := even_intersection_eq_bot eight_five_not_dvd_normalizer Q N hQ hN hn h5
  have hcard := card_two_of_even_intersection_bot Q hne he
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hcard
  have hz0 : (z : Equiv.Perm (Fin 8)) ≠ 1 := fun hh => hz (Subtype.ext hh)
  have hz2 : (z : Equiv.Perm (Fin 8)) ^ 2 = 1 := by
    have hh : z ^ Nat.card Q = 1 := pow_card_eq_one'
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  have hNC : normalizer (Q : Set _) ≤ centralizer ({(z : Equiv.Perm (Fin 8))} : Set _) :=
    (normalizer_le_centralizer_of_card_two Q hcard).trans
      (centralizer_le (Set.singleton_subset_iff.mpr z.property))
  have hswap := involution_isSwap_of_five_centralizer z hz2 hz0
    (h5.trans (card_dvd_of_le (hn.trans hNC)))
  have h64 : 64 ∣ Nat.card U := U.pow_dvd_card_of_pow_dvd_card (n := 6) (by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
  have hc : Nat.card ((U : Subgroup _).map (alternatingGroup (Fin 8)).subtype) = Nat.card U :=
    card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective
  have hd := (hc.symm ▸ h64).trans (card_dvd_of_le (hU.trans hNC))
  rw [Equiv.Perm.nat_card_centralizer,Equiv.Perm.isSwap_iff_cycleType.mp hswap] at hd
  norm_num [Nat.factorial] at hd

end Theory.SpecificGroups.AlternatingSixNormalizer
