module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveNormalizerEight

/-!
# Five-squaring actors in the original Sylow subgroup

Sylow conjugacy inside the original endpoint moves a genuine squaring lift
into the prescribed Sylow subgroup. Conjugating its order-five subgroup at
the same time retains the action, without imposing a split complement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original large endpoint has an order-five generator and a squaring
actor in the prescribed Sylow subgroup, with the genuine central fourth power. -/
theorem source_quintic_large_sylow_five_actors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024) :
    ∃ (A : Subgroup G) (c s : G), A ≤ H ∧ Nat.card A = 5 ∧
      orderOf c = 5 ∧ zpowers c = A ∧ s ∈ T ∧
      s ∈ normalizer (A : Set G) ∧
      (∀ a ∈ A, s * a * s⁻¹ = a ^ 2) ∧
      s ^ 4 ∈ centralInvolutions T ∧ s ^ 8 = 1 ∧
      (orderOf s = 4 ∨ orderOf s = 8) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hfive : 5 ∣ Nat.card H := by
    have hh := relIndex_mul_card_of_le hTH
    rw [hi] at hh
    exact hh ▸ dvd_mul_right 5 (Nat.card (T : Subgroup G))
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 hfive
  let A : Subgroup G := zpowers (c : G)
  have hAH : A ≤ H := zpowers_le.mpr c.property
  have hc5 : orderOf (c : G) = 5 := (orderOf_coe c).trans hc
  have hA : Nat.card A = 5 := (Nat.card_zpowers (c : G)).trans hc5
  obtain ⟨s, hsH, hsA, _, _, _, hs, _⟩ := source_quintic_five_squaring_element
    hG T hempty hM hu hmany hcard e H hH hi A hAH hA
  have hs8 := (source_quintic_large_five_squaring_eighth
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA s hsH hsA hs).2.1
  let sH : H := ⟨s, hsH⟩
  have hp : IsPGroup 2 (zpowers sH) := IsPGroup.of_card_dvd_pow (n := 3) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (show sH ^ 8 = 1 from Subtype.ext hs8))
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P (T.subtype hTH)
  have hsT : (MulAut.conj g) sH ∈ T.subtype hTH := by
    rw [← hg]
    change (MulAut.conj g) • sH ∈ (MulAut.conj g) • (P : Set H)
    exact Set.smul_mem_smul_set (hP (mem_zpowers sH))
  let f : G ≃* G := MulAut.conj (g : G)
  let B := A.map f.toMonoidHom
  have hBH : B ≤ H := by
    rintro _ ⟨a, ha, rfl⟩
    exact H.mul_mem (H.mul_mem g.property (hAH ha)) (H.inv_mem g.property)
  have hB : Nat.card B = 5 := (card_map_of_injective f.injective).trans hA
  have hsB : f s ∈ normalizer (B : Set G) :=
    A.le_normalizer_map f.toMonoidHom (mem_map_of_mem _ hsA)
  have hfs : ∀ a ∈ B, f s * a * (f s)⁻¹ = a ^ 2 := by
    rintro _ ⟨a, ha, rfl⟩
    change f s * f a * (f s)⁻¹ = (f a) ^ 2
    simpa only [map_mul, map_inv, map_pow] using congrArg f (hs a ha)
  have hfsT : f s ∈ T := hsT
  obtain ⟨hf4, hf8, hforder⟩ := source_quintic_large_five_squaring_eighth
    hG T hempty hM hu hmany hcard e H hH hi hlarge B hBH hB (f s)
      (hTH hfsT) hsB hfs
  refine ⟨B, f c, f s, hBH, hB, (f.orderOf_eq c).trans hc5, ?_,
    hfsT, hsB, hfs, hf4, hf8, hforder⟩
  exact (MonoidHom.map_zpowers f.toMonoidHom (c : G)).symm

/-- Any actual squaring actor in the prescribed Sylow subgroup generates it
with the full two-core. Its image modulo the core has order exactly four. -/
theorem source_quintic_large_squaring_generates_sylow
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
    (s : G) (hsT : s ∈ T) (hsA : s ∈ normalizer (A : Set G))
    (hs : ∀ a ∈ A, s * a * s⁻¹ = a ^ 2) :
    H.pCoreIn 2 ⊔ zpowers s = (T : Subgroup G) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype hTH)).trans_eq (map_subgroupOf_eq_of_le hTH)
  have hQcard : Nat.card (pCore 2 H) = 1024 :=
    (card_map_of_injective H.subtype_injective).symm.trans hlarge
  obtain ⟨_, ⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient
    hG T hempty hM hu hmany hcard e H hH hi
  have hquot : Nat.card (H ⧸ pCore 2 H) = 20 :=
    (Nat.card_congr eSuz.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
  have hHcard : Nat.card H = 20480 := by
    have hh := (pCore 2 H).card_mul_index
    rw [index_eq_card, hQcard, hquot] at hh
    exact hh.symm
  have hTcard : Nat.card (T : Subgroup G) = 4096 := by
    have hh := relIndex_mul_card_of_le hTH
    rw [hi, hHcard] at hh
    omega
  have hs2 : s ^ 2 ∉ H.pCoreIn 2 := by
    intro hmem
    have hcent : s ^ 2 ∈ centralizer (A : Set G) := by
      have hh : s ^ 2 ∈ H.pCoreIn 2 ⊓ normalizer (A : Set G) :=
        ⟨hmem, pow_mem hsA 2⟩
      rw [(source_quintic_large_five_normalizer_card
        hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).1] at hh
      exact hh.2
    let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := A) 5
      (hA ▸ (by decide : 5 ∣ 5))
    have hc5 : orderOf (c : G) = 5 := (orderOf_coe c).trans hc
    have hsc : (MulAut.conj s) (c : G) = (c : G) ^ 2 := hs c c.property
    have hconj : (MulAut.conj (s ^ 2)) (c : G) = (c : G) ^ 4 := by
      rw [pow_two, map_mul, MulAut.mul_apply, hsc, map_pow, hsc, ← pow_mul]
    have hfour : (c : G) ^ 4 = c := hconj.symm.trans
      (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hcent c c.property).symm)
    have hthree : (c : G) ^ 3 = 1 := by
      apply mul_left_cancel (a := (c : G))
      calc
        (c : G) * (c : G) ^ 3 = (c : G) ^ 4 := by group
        _ = (c : G) := hfour
        _ = (c : G) * 1 := by rw [mul_one]
    have hd := orderOf_dvd_of_pow_eq_one hthree
    rw [hc5] at hd
    norm_num at hd
  have hs4 : s ^ 4 ∈ H.pCoreIn 2 := (source_quintic_large_five_squaring_power
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA s (hTH hsT) hsA hs).1.1
  let sH : H := ⟨s, hTH hsT⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq4 : (q sH) ^ 4 = 1 := by
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨u, hu, he⟩ := hs4
    exact (show u = sH ^ 4 from Subtype.ext he) ▸ hu
  have hq2 : (q sH) ^ 2 ≠ 1 := by
    intro hh
    rw [← map_pow] at hh
    exact hs2 (mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp hh))
  have hqo : orderOf (q sH) = 4 := orderOf_eq_prime_pow (p := 2) (n := 1) hq2 hq4
  let J : Subgroup H := pCore 2 H ⊔ zpowers sH
  have hmapcore : (pCore 2 H).map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by
    rw [show q = QuotientGroup.mk' (pCore 2 H) from rfl, QuotientGroup.ker_mk'])
  have hJindex : (pCore 2 H).relIndex J = 4 := by
    rw [← QuotientGroup.ker_mk' (pCore 2 H), relIndex_ker]
    change Nat.card (J.map q) = 4
    rw [show J = pCore 2 H ⊔ zpowers sH from rfl, Subgroup.map_sup, hmapcore,
      bot_sup_eq, MonoidHom.map_zpowers, Nat.card_zpowers, hqo]
  have hJcard : Nat.card J = 4096 := by
    have hh := relIndex_mul_card_of_le (show pCore 2 H ≤ J from le_sup_left)
    rw [hJindex, hQcard] at hh
    exact hh.symm
  have hJmap : J.map H.subtype = H.pCoreIn 2 ⊔ zpowers s := by
    rw [show J = pCore 2 H ⊔ zpowers sH from rfl, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  apply eq_of_le_of_card_ge (sup_le hQT (zpowers_le.mpr hsT))
  rw [← hJmap, card_map_of_injective H.subtype_injective, hJcard, hTcard]

end CFSG.Quasithin.Chapter14.Section06
