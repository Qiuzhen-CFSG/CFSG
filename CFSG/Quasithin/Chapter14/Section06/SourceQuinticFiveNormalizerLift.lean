module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveSymmetry
public import Theory.GroupTheory.FiveSquaringPowers

/-!
# Native five-normalizer and finite-order squaring lift

The actual Sz(2) quotient and the full native five-normalizer action give
exact orders for the five-normalizer and its centralizer. These constrain
the lift inside the original endpoint without assuming a split complement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The full native five-normalizer has order eighty in the retained large core. -/
theorem source_quintic_large_five_normalizer_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    H.pCoreIn 2 ⊓ normalizer (A : Set G) = H.pCoreIn 2 ⊓ centralizer (A : Set G) ∧
      Nat.card (H ⊓ normalizer (A : Set G) : Subgroup G) = 80 := by
  let Q := H.pCoreIn 2
  let N := H ⊓ normalizer (A : Set G)
  let B := Q ⊓ centralizer (A : Set G)
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hd : Disjoint Q A := (isPGroup_pCoreIn 2 H).disjoint_of_coprime hAp (by decide)
  have hQB : Q ⊓ normalizer (A : Set G) = B := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      rw [← commutator_eq_bot_iff_le_centralizer]
      apply bot_unique
      exact ((le_inf ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hAH.trans hHQ)))
        (le_normalizer_iff_commutator_le_right.mp inf_le_right)).trans hd.le_bot)
    · exact inf_le_inf_left _ (centralizer_le_normalizer A)
  have hQN : Q ⊓ N = B := by
    change Q ⊓ (H ⊓ normalizer (A : Set G)) = B
    rw [← inf_assoc, inf_eq_left.mpr (pCoreIn_le 2 H)]
    exact hQB
  have hB : Nat.card B = 4 := (source_quintic_large_five_residual
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2.2.1
  have hsup : Q ⊔ N = H := by
    rw [sup_comm]
    exact (source_quintic_five_normalizer_action
      hG T hempty hM hu hmany hcard e H hH hi A hAH hA).2.1
  obtain ⟨_, ⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient
    hG T hempty hM hu hmany hcard e H hH hi
  have hquot : Nat.card (H ⧸ pCore 2 H) = 20 :=
    (Nat.card_congr eSuz.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
  have hcore : Nat.card (pCore 2 H) = 1024 :=
    (card_map_of_injective H.subtype_injective).symm.trans hlarge
  have hHcard : Nat.card H = 20480 := by
    have hh := (pCore 2 H).card_mul_index
    rw [index_eq_card, hcore, hquot] at hh
    exact hh.symm
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q N (inf_le_left.trans hHQ)
  rw [hlarge, hQN, hB, hsup, hHcard] at hc
  refine ⟨hQB, ?_⟩
  change Nat.card N = 80
  omega

/-- The actual local centralizer has order twenty and is precisely the product
of the prescribed five-subgroup and its fixed subgroup in the full core. -/
theorem source_quintic_large_five_local_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    Nat.card (H ⊓ centralizer (A : Set G) : Subgroup G) = 20 ∧
      H ⊓ centralizer (A : Set G) = A ⊔ (H.pCoreIn 2 ⊓ centralizer (A : Set G)) := by
  let Q := H.pCoreIn 2
  let N := H ⊓ normalizer (A : Set G)
  let C := H ⊓ centralizer (A : Set G)
  let B := Q ⊓ centralizer (A : Set G)
  let f : N →* MulAut A := A.normalizerMonoidHom.comp (inclusion inf_le_right)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨b, hb⟩ := (source_quintic_five_normalizer_action
      hG T hempty hM hu hmany hcard e H hH hi A hAH hA).1 a
    exact ⟨⟨b, b.property, b.val.property⟩, hb⟩
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : IsCyclic A := isCyclic_of_prime_card hA
  have hautindex : f.ker.index = 4 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr hf, card_top, IsCyclic.card_mulAut, hA]
    decide
  have hn : Nat.card N = 80 := (source_quintic_large_five_normalizer_card
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2
  have hker : f.ker.map N.subtype = C := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨n.property.1, ?_⟩
      change inclusion (show N ≤ normalizer (A : Set G) from inf_le_right) n ∈
        A.normalizerMonoidHom.ker at hn
      rwa [normalizerMonoidHom_ker] at hn
    · rintro ⟨hxH, hxC⟩
      refine ⟨⟨x, hxH, centralizer_le_normalizer A hxC⟩, ?_, rfl⟩
      change (⟨x, centralizer_le_normalizer A hxC⟩ : normalizer (A : Set G)) ∈
        A.normalizerMonoidHom.ker
      rwa [normalizerMonoidHom_ker]
  have hc : Nat.card C = 20 := by
    have hh := f.ker.card_mul_index
    rw [hautindex, hn] at hh
    rw [← hker, card_map_of_injective N.subtype_injective]
    omega
  have hB : Nat.card B = 4 := (source_quintic_large_five_residual
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2.2.1
  have hAC : A ≤ C := le_inf hAH (le_centralizer A)
  have hBC : B ≤ C := inf_le_inf_right _ (pCoreIn_le 2 H)
  have hAB : Disjoint A B := (IsPGroup.of_card (p := 5) (n := 1)
    (by simpa using hA)).disjoint_of_coprime
    ((isPGroup_pCoreIn 2 H).to_le inf_le_left) (by decide)
  have hABcard : Nat.card (A ⊔ B : Subgroup G) = 20 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A B
      (inf_le_right.trans (centralizer_le_normalizer A)) hAB, hA, hB]
  exact ⟨hc, (eq_of_le_of_card_ge (sup_le hAC hBC) (by rw [hc, hABcard])).symm⟩

/-- Every native squaring lift already has two-power order at most sixteen.
Its fourth power lies in the actual cyclic-four fixed subgroup of the core;
no choice of a split lift is made. -/
theorem source_quintic_large_five_squaring_power
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5)
    (s : G) (hsH : s ∈ H) (hsN : s ∈ normalizer (A : Set G))
    (hs : ∀ a ∈ A, s * a * s⁻¹ = a ^ 2) :
    s ^ 4 ∈ H.pCoreIn 2 ⊓ centralizer (A : Set G) ∧
      s ^ 16 = 1 ∧ (orderOf s = 4 ∨ orderOf s = 8 ∨ orderOf s = 16) := by
  let N := H ⊓ normalizer (A : Set G)
  let AN := A.subgroupOf N
  have hAN : A ≤ N := le_inf hAH A.le_normalizer
  let : AN.Normal := normal_subgroupOf_of_le_normalizer
    (show N ≤ normalizer (A : Set G) from inf_le_right)
  have hANcard : Nat.card AN = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv).trans hA
  have hNcard : Nat.card N = 80 := (source_quintic_large_five_normalizer_card
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2
  have hquotN : Nat.card (N ⧸ AN) = 16 := by
    have hh := AN.card_mul_index
    rw [index_eq_card, hANcard, hNcard] at hh
    omega
  let sN : N := ⟨s, hsH, hsN⟩
  have hs16A : s ^ 16 ∈ A := by
    have hh := pow_card_eq_one' (x := QuotientGroup.mk' AN sN)
    rw [hquotN, ← map_pow] at hh
    exact (QuotientGroup.eq_one_iff (N := AN) _).mp hh
  have hs16 : s ^ 16 = 1 := by
    have hh : (s ^ 16) ^ 2 = s ^ 16 := (hs _ hs16A).symm.trans (by group)
    exact mul_left_cancel (show s ^ 16 * s ^ 16 = s ^ 16 * 1 by
      simpa only [pow_two, mul_one] using hh)
  have hs4Q : s ^ 4 ∈ H.pCoreIn 2 := by
    obtain ⟨_, ⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient
      hG T hempty hM hu hmany hcard e H hH hi
    have hquot : Nat.card (H ⧸ pCore 2 H) = 20 :=
      (Nat.card_congr eSuz.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
    let sH : H := ⟨s, hsH⟩
    let q := QuotientGroup.mk' (pCore 2 H) sH
    have hq16 : q ^ 16 = 1 := by
      rw [← map_pow, show sH ^ 16 = 1 from Subtype.ext hs16, map_one]
    have hd : orderOf q ∣ 4 := by
      have h20 : orderOf q ∣ 20 := hquot ▸ orderOf_dvd_natCard q
      exact Nat.dvd_gcd h20 (orderOf_dvd_of_pow_eq_one hq16)
    have hq4 : q ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
    rw [← map_pow] at hq4
    exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp hq4)
  have horders : orderOf s = 4 ∨ orderOf s = 8 ∨ orderOf s = 16 := by
    have hne := square_ne_one_of_squares_five A hA s hs
    obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show orderOf s ∣ 2 ^ 4 from orderOf_dvd_of_pow_eq_one hs16)
    interval_cases n
    · exact (hne (orderOf_dvd_iff_pow_eq_one.mp (by rw [he]; decide))).elim
    · exact (hne (orderOf_dvd_iff_pow_eq_one.mp (by rw [he]; decide))).elim
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  exact ⟨⟨hs4Q, fourth_power_centralizes_five A hA s hs⟩, hs16, horders⟩

/-- The original large endpoint supplies a bounded-order squaring lift with
all native subgroup and fixed-root markings retained. -/
theorem source_quintic_large_five_bounded_squaring_lift
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let Q := H.pCoreIn 2
    let R := ⁅Q,A⁆
    let B := Q ⊓ centralizer (A : Set G)
    ∃ s : G, s ∈ H ∧ s ∈ normalizer (A : Set G) ∧
      s ∈ normalizer (Q : Set G) ∧ s ∈ normalizer (R : Set G) ∧
      s ∈ normalizer (B : Set G) ∧ s ^ 4 ∈ B ∧ s ^ 16 = 1 ∧
      (orderOf s = 4 ∨ orderOf s = 8 ∨ orderOf s = 16) ∧
      (∀ a ∈ A, s * a * s⁻¹ = a ^ 2) ∧
      ∀ t : G, orderOf t = 4 → zpowers t = B →
        s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t⁻¹ := by
  obtain ⟨s, hsH, hsA, hsQ, hsR, hsB, hs, hroot⟩ :=
    source_quintic_five_squaring_element
      hG T hempty hM hu hmany hcard e H hH hi A hAH hA
  obtain ⟨hfour, hsixteen, horder⟩ := source_quintic_large_five_squaring_power
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA s hsH hsA hs
  exact ⟨s, hsH, hsA, hsQ, hsR, hsB, hfour, hsixteen, horder, hs, hroot⟩

end CFSG.Quasithin.Chapter14.Section06
