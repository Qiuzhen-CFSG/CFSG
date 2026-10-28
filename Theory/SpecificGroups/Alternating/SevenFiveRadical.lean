module
public import Theory.SpecificGroups.AlternatingSixNormalizer

/-!
# A two-subgroup normalized by a five-divisible subgroup of A₇

Every nontrivial even two-subgroup has normalizer order prime to five.
Thus the original two-subgroup injects into the sign group, so has order
two. The permutation centralizer formula forces its generator to be a
transposition. The actual subgroup is retained as the generated subgroup.

Source application: Aschbacher--Smith C.2.7(3)(b), pp.145--147,
in the fixed-centralizer comparison of 14.7.68(2), pp.1071--1072.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.Alternating.SevenFiveRadical

theorem generated_by_swap
    (Q N : Subgroup (Equiv.Perm (Fin 7))) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hN : N ≤ alternatingGroup (Fin 7)) (hn : N ≤ normalizer (Q : Set _))
    (h5 : 5 ∣ Nat.card N) :
    Nat.card Q = 2 ∧ ∃ z : Equiv.Perm (Fin 7), z.IsSwap ∧ Q = closure {z} := by
  have he : Q ⊓ alternatingGroup (Fin 7) = ⊥ := by
    have hb : Q.subgroupOf (alternatingGroup (Fin 7)) = ⊥ := by
      by_contra hb
      apply Theory.SpecificGroups.AlternatingSixNormalizer.seven_five_not_dvd_normalizer
        _ hQ.comap_subtype hb
      have hn' : N.subgroupOf (alternatingGroup (Fin 7)) ≤
          normalizer (Q.subgroupOf (alternatingGroup (Fin 7)) : Set _) := by
        intro x hx
        apply mem_normalizer_iff.mpr
        intro y
        exact mem_normalizer_iff.mp (hn hx) y.val
      have hc : Nat.card (N.subgroupOf (alternatingGroup (Fin 7))) = Nat.card N :=
        Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv
      exact (hc.symm ▸ h5).trans (card_dvd_of_le hn')
    have hh := congrArg (map (alternatingGroup (Fin 7)).subtype) hb
    simpa only [subgroupOf_map_subtype,Subgroup.map_bot] using hh
  have hc : Nat.card Q = 2 := by
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
    have hl' : 1 < Nat.card Q := Finite.one_lt_card_iff_nontrivial.mpr
      ((nontrivial_iff_ne_bot Q).mpr hne)
    have hu : Nat.card (ℤˣ) = 2 := by simp [Nat.card_eq_fintype_card]
    rw [hu] at hl
    omega
  obtain ⟨z,hz,hunique⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hc
  have hz0 : (z : Equiv.Perm (Fin 7)) ≠ 1 := fun hh => hz (Subtype.ext hh)
  have hz2 : (z : Equiv.Perm (Fin 7)) ^ 2 = 1 := by
    have hh : z ^ Nat.card Q = 1 := pow_card_eq_one'
    rw [hc] at hh
    exact congrArg Subtype.val hh
  have hNC : normalizer (Q : Set _) ≤ centralizer ({(z : Equiv.Perm (Fin 7))} : Set _) :=
    (normalizer_le_centralizer_of_card_two Q hc).trans
      (centralizer_le (Set.singleton_subset_iff.mpr z.property))
  have h5z := h5.trans (card_dvd_of_le (hn.trans hNC))
  have hswap : (z : Equiv.Perm (Fin 7)).IsSwap := by
    have ht := Equiv.Perm.cycleType_of_pow_prime_eq_one hz2
    have hs := (z : Equiv.Perm (Fin 7)).support.card_le_univ
    have hs' := (z : Equiv.Perm (Fin 7)).sum_cycleType
    rw [ht,Multiset.sum_replicate] at hs'
    have hp : 0 < (z : Equiv.Perm (Fin 7)).cycleType.card := by
      apply Nat.pos_of_ne_zero
      intro hh
      exact hz0 (Equiv.Perm.cycleType_eq_zero.mp (Multiset.card_eq_zero.mp hh))
    have hb : (z : Equiv.Perm (Fin 7)).cycleType.card ≤ 3 := by
      simp only [Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hs hs'
      omega
    have h1 : (z : Equiv.Perm (Fin 7)).cycleType.card = 1 := by
      rw [Equiv.Perm.nat_card_centralizer,ht] at h5z
      interval_cases hh : (z : Equiv.Perm (Fin 7)).cycleType.card <;>
        first | rfl | norm_num [Nat.factorial] at h5z
    apply Equiv.Perm.isSwap_iff_cycleType.mpr
    rw [ht,h1]
    rfl
  refine ⟨hc,z,hswap,le_antisymm ?_ ((closure_le _).mpr (Set.singleton_subset_iff.mpr z.property))⟩
  intro x hx
  by_cases hx1 : x = 1
  · exact hx1 ▸ one_mem _
  have hxz : x = z := congrArg Subtype.val (hunique ⟨x,hx⟩ (fun hh => hx1 (congrArg Subtype.val hh)))
  rw [hxz]
  exact subset_closure (Set.mem_singleton _)

end Theory.SpecificGroups.Alternating.SevenFiveRadical
