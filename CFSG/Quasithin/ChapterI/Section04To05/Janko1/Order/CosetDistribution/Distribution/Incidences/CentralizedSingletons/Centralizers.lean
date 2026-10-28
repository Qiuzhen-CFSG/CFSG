module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Commuting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Incidences.Counting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.FourCentralizers
/-!
# Three-subgroup centralizers in Bender's singleton incidence

A singleton involution has no commuting involution in the Sylow normalizer.
Its nontrivial centralizer there therefore has order three: its order divides
both 168 and 120, and is odd. Each three-subgroup has one inside commuting
involution, since its centralizer in the normalizer is cyclic of order six.

For an outside commuting involution, the three-subgroup normalizes its literal
inverted subgroup. Cyclic automorphism orders and the common-centralizer bound
exclude inverted subgroups of orders two, three and six. This leaves precisely
the singleton and septuple branches needed by the incidence assembly.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed p.227, the commuting-three-subgroup paragraph.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A singleton fiber excludes every involution in its centralizer inside H. -/
public theorem bender_singleton_no_commuting_involution (H : Subgroup G)
    (u : BenderInvolutionsInFibers H 1) (a : G) (haH : a ∈ H)
    (ha : orderOf a = 2) (hau : Commute a u.1) : False := by
  have huH : u.1 ∉ H := fun hm => u.2.2.1 ((benderRightCoset_eq_base_iff H _).mpr hm)
  have hc : Nat.card (BenderInverted H u.1) = 1 :=
    (Nat.card_congr (benderFiberEquivInverted H u.1 u.2.1 huH)).symm.trans u.2.2.2
  have hs : Subsingleton (BenderInverted H u.1) := (Nat.card_eq_one_iff_unique.mp hc).1
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ha).1)
  let ai : BenderInverted H u.1 := ⟨⟨a, haH⟩,
    (mul_inv_eq_iff_eq_mul.mpr hau.symm.eq).trans hai.symm⟩
  let oi : BenderInverted H u.1 := ⟨1, by simp⟩
  have he : a = 1 := congrArg (fun x : BenderInverted H u.1 => (x.1 : G)) (hs.elim ai oi)
  simp [he] at ha

/-- A centralized singleton has a centralizer of order three in the actual H. -/
public theorem bender_singleton_centralizer_card [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (normalizerData : BenderNormalizerData h)
    (u : BenderCentralizedSingletons (normalizer (h.sylow : Set G))) :
    Nat.card (normalizer (h.sylow : Set G) ⊓ centralizer ({u.1} : Set G) : Subgroup G) = 3 := by
  let H := normalizer (h.sylow : Set G)
  let C := H ⊓ centralizer ({u.1} : Set G)
  have hcH : Nat.card C ∣ 168 := normalizerData.normalizer_card ▸ card_dvd_of_le inf_le_left
  have hcG : Nat.card C ∣ 120 := h.involution_centralizer_card u.1 u.2.1 ▸
    card_dvd_of_le (show C ≤ centralizer ({u.1} : Set G) from inf_le_right)
  have hc24 : Nat.card C ∣ 24 := Nat.dvd_gcd hcH hcG
  have hn2 : ¬ 2 ∣ Nat.card C := by
    intro hd
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hd
    exact bender_singleton_no_commuting_involution H
      ⟨u.1, u.2.1, u.2.2.1, u.2.2.2.1⟩ a a.2.1
      ((orderOf_coe a).trans ha) (mem_centralizer_singleton_iff.mp a.2.2)
  have hn1 : Nat.card C ≠ 1 := by
    intro hc
    have hs : Subsingleton C := (Nat.card_eq_one_iff_unique.mp hc).1
    obtain ⟨a, haH, hane, hau⟩ := u.2.2.2.2
    exact hane (congrArg Subtype.val (hs.elim
      (⟨a, haH, mem_centralizer_singleton_iff.mpr hau.eq⟩ : C) 1))
  have hle : Nat.card C ≤ 24 := Nat.le_of_dvd (by decide) hc24
  change Nat.card C = 3
  generalize Nat.card C = n at *
  interval_cases n <;> norm_num at *

/-- The unique three-subgroup centralized by an actual centralized singleton. -/
public theorem bender_singleton_unique_three [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (normalizerData : BenderNormalizerData h)
    (u : BenderCentralizedSingletons (normalizer (h.sylow : Set G))) :
    ∃! X : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3,
      X.1 ≤ centralizer ({u.1} : Set G) := by
  let C := normalizer (h.sylow : Set G) ⊓ centralizer ({u.1} : Set G)
  have hc : Nat.card C = 3 := bender_singleton_centralizer_card h normalizerData u
  refine ⟨⟨C, inf_le_left, hc⟩, inf_le_right, ?_⟩
  intro X hX
  apply Subtype.ext
  exact eq_of_le_of_card_ge (le_inf X.2.1 hX) (by rw [hc, X.2.2])

/-- The ambient generator realizing an actual three-subgroup. -/
public theorem bender_three_generator (X : Subgroup G) (hX : Nat.card X = 3) :
    ∃ x : G, orderOf x = 3 ∧ X = zpowers x := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hX])
  have hxG : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
  exact ⟨x, hxG, (eq_of_le_of_card_ge (zpowers_le.mpr x.2)
    (by rw [Nat.card_zpowers, hxG, hX])).symm⟩

/-- The number of involutions in a finite cyclic group of order six. -/
private theorem cyclic_six_involutions_card (K : Type*) [Group K] [Finite K]
    [IsCyclic K] (hK : Nat.card K = 6) : Nat.card {u : K // orderOf u = 2} = 1 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hd : 2 ∣ Fintype.card K := by rw [← Nat.card_eq_fintype_card, hK]; decide
  exact (IsCyclic.card_orderOf_eq_totient hd).trans (by decide)

/-- Each actual three-subgroup commutes with exactly one inside involution. -/
public theorem bender_three_inside_commuting_card
    (h : Janko1CentralizerData G) (geometry : BenderNormalizerGeometry h)
    (X : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3) :
    Nat.card {u : G // orderOf u = 2 ∧ X.1 ≤ centralizer ({u} : Set G) ∧
      u ∈ normalizer (h.sylow : Set G)} = 1 := by
  let C := normalizer (h.sylow : Set G) ⊓ centralizer (X.1 : Set G)
  have hc : Nat.card C = 6 := geometry.three_centralizer X.1 X.2.1 X.2.2
  let : IsCyclic C := geometry.six_cyclic C inf_le_left hc
  let ec : {u : G // orderOf u = 2 ∧ X.1 ≤ centralizer ({u} : Set G) ∧
      u ∈ normalizer (h.sylow : Set G)} ≃ {u : C // orderOf u = 2} :=
    { toFun := fun u => ⟨⟨u.1, u.2.2.2, mem_centralizer_iff.mpr
        (fun a ha => mem_centralizer_singleton_iff.mp (u.2.2.1 ha))⟩,
        (orderOf_coe _).symm.trans u.2.1⟩
      invFun := fun u => ⟨u.1.1, (orderOf_coe _).trans u.2,
        fun a ha => mem_centralizer_singleton_iff.mpr
          (mem_centralizer_iff.mp u.1.2.2 a ha), u.1.2.1⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  exact (Nat.card_congr ec).trans (cyclic_six_involutions_card C hc)

/-- The supplied local three-count, less its one inside involution. -/
public theorem bender_three_outside_commuting_card
    (h : Janko1CentralizerData G) (d : ℕ) (localData : BenderPrimeData G d)
    (geometry : BenderNormalizerGeometry h)
    (X : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3) :
    Nat.card {u : BenderOutsideInvolutions (normalizer (h.sylow : Set G)) //
      X.1 ≤ centralizer ({u.1} : Set G)} + 2 = 2 * d := by
  classical
  let H := normalizer (h.sylow : Set G)
  let J := {u : G // orderOf u = 2 ∧ X.1 ≤ centralizer ({u} : Set G)}
  let p : J → Prop := fun u => u.1 ∈ H
  obtain ⟨x, hx, hX⟩ := bender_three_generator X.1 X.2.2
  have hcomm (u : G) : (X.1 ≤ centralizer ({u} : Set G)) ↔ Commute u x := by
    rw [hX, zpowers_le, mem_centralizer_singleton_iff]
    exact ⟨fun he => he.symm, fun he => he.eq.symm⟩
  have htotal : Nat.card J = 2 * d - 1 := by
    let ec : J ≃ {u : G // orderOf u = 2 ∧ Commute u x} :=
      Equiv.subtypeEquivRight (fun u => and_congr_right (fun _ => hcomm u))
    exact (Nat.card_congr ec).trans (localData.commuting_three x hx)
  let ei : {u : J // p u} ≃ {u : G // orderOf u = 2 ∧
      X.1 ≤ centralizer ({u} : Set G) ∧ u ∈ H} :=
    { toFun := fun u => ⟨u.1.1, u.1.2.1, u.1.2.2, u.2⟩
      invFun := fun u => ⟨⟨u.1, u.2.1, u.2.2.1⟩, u.2.2.2⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  let eo : {u : J // ¬ p u} ≃ {u : BenderOutsideInvolutions H //
      X.1 ≤ centralizer ({u.1} : Set G)} :=
    { toFun := fun u => ⟨⟨u.1.1, u.1.2.1, u.2⟩, u.1.2.2⟩
      invFun := fun u => ⟨⟨u.1.1, u.1.2.1, u.2⟩, u.1.2.2⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  have hc := Nat.card_congr (Equiv.sumCompl p).symm
  rw [Nat.card_sum, Nat.card_congr ei, Nat.card_congr eo,
    bender_three_inside_commuting_card h geometry X] at hc
  rw [htotal] at hc
  change Nat.card {u : BenderOutsideInvolutions H //
    X.1 ≤ centralizer ({u.1} : Set G)} + 2 = 2 * d
  rcases localData.d_cases with hd | hd <;> omega

omit [Finite G] in
/-- Commuting elements of H normalize the literal subgroup inverted by u. -/
public theorem bender_commuting_normalizes_inverted (H X K : Subgroup G) (u : G)
    (hXH : X ≤ H) (hXu : X ≤ centralizer ({u} : Set G))
    (hK : ∀ a : G, a ∈ K ↔ a ∈ H ∧ u * a * u⁻¹ = a⁻¹) :
    X ≤ normalizer (K : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx a ha
  let e := MulAut.conj x
  have hex : e u = u := mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_singleton_iff.mp (hXu hx))
  apply (hK _).mpr
  refine ⟨H.mul_mem (H.mul_mem (hXH hx) ((hK a).mp ha).1) (H.inv_mem (hXH hx)), ?_⟩
  have he := congrArg e ((hK a).mp ha).2
  simpa only [map_mul, map_inv, hex, e, MulAut.conj_apply] using he

private theorem three_centralizes_small_cyclic (X K : Subgroup G) [IsCyclic K]
    (hX : Nat.card X = 3) (hK : Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 6)
    (hXN : X ≤ normalizer (K : Set G)) : X ≤ centralizer (K : Set G) := by
  let f : X →* MulAut K := K.normalizerMonoidHom.comp (inclusion hXN)
  have hf (x : X) : f x = 1 := by
    have h3 : orderOf (f x) ∣ 3 :=
      (orderOf_map_dvd f x).trans (hX ▸ orderOf_dvd_natCard x)
    have h2 : orderOf (f x) ∣ 2 := by
      have hd := orderOf_dvd_natCard (f x)
      rw [IsCyclic.card_mulAut] at hd
      rcases hK with hK | hK | hK
      · rw [hK, show Nat.totient 2 = 1 by decide] at hd
        exact hd.trans (by decide)
      · simpa only [hK, show Nat.totient 3 = 2 by decide] using hd
      · simpa only [hK, show Nat.totient 6 = 2 by decide] using hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (Nat.dvd_gcd h3 h2))
  intro x hx
  apply mem_centralizer_iff.mpr
  intro a ha
  have he := congrArg (fun f : MulAut K => (f ⟨a, ha⟩ : G)) (hf ⟨x, hx⟩)
  change x * a * x⁻¹ = a at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- An outside involution commuting with a three-subgroup has fiber size one or seven. -/
public theorem bender_three_commuting_fiber_cases [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (d : ℕ) (localData : BenderPrimeData G d)
    (geometry : BenderNormalizerGeometry h)
    (X : BenderSubgroupsOfOrder (normalizer (h.sylow : Set G)) 3)
    (u : BenderOutsideInvolutions (normalizer (h.sylow : Set G)))
    (hXu : X.1 ≤ centralizer ({u.1} : Set G)) :
    Nat.card (BenderFiber (normalizer (h.sylow : Set G))
      (benderRightCoset (normalizer (h.sylow : Set G)) u.1)) = 1 ∨
    Nat.card (BenderFiber (normalizer (h.sylow : Set G))
      (benderRightCoset (normalizer (h.sylow : Set G)) u.1)) = 7 := by
  let H := normalizer (h.sylow : Set G)
  obtain ⟨K, hK, hc⟩ := geometry.inverted_subgroup u.1 u.2.1 u.2.2
  rw [bender_fiber_card_of_inverted_subgroup H u.1 u.2.1 u.2.2 K hK]
  have hKH : K ≤ H := fun a ha => ((hK a).mp ha).1
  have hXN := bender_commuting_normalizes_inverted H X.1 K u.1 X.2.1 hXu hK
  have hexclude (hc : Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 6) : False := by
    have hcyc : IsCyclic K := by
      rcases hc with hc | hc | hc
      · exact isCyclic_of_prime_card (p := 2) hc
      · exact isCyclic_of_prime_card (p := 3) hc
      · exact geometry.six_cyclic K hKH hc
    let : IsCyclic K := hcyc
    have hXC : X.1 ≤ centralizer (K : Set G) :=
      three_centralizes_small_cyclic X.1 K X.2.2 hc hXN
    have heven (h2 : 2 ∣ Nat.card K) : False := by
      obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
      have ha2 : orderOf (a : G) = 2 := (orderOf_coe a).trans ha
      have hai : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right
        (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ha2).1)
      have hua : Commute u.1 (a : G) := mul_inv_eq_iff_eq_mul.mp
        (((hK a).mp a.2).2.trans hai)
      have hane : (a : G) ∉ zpowers u.1 := by
        intro ham
        have hz : zpowers (a : G) = zpowers u.1 :=
          eq_of_le_of_card_ge (zpowers_le.mpr ham) (by rw [Nat.card_zpowers,
            Nat.card_zpowers, ha2, u.2.1])
        exact u.2.2 ((hz ▸ (zpowers_le.mpr (hKH a.2) : zpowers (a : G) ≤ H))
          (mem_zpowers u.1))
      have hd := card_dvd_of_le (show X.1 ≤ centralizer ({u.1} : Set G) ⊓
          centralizer ({(a : G)} : Set G) from le_inf hXu (fun x hx =>
            mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hXC hx) a a.2).symm))
      rw [X.2.2, h.common_centralizer_card_of_involutions u.1 a u.2.1 hua
        (orderOf_eq_prime_iff.mp ha2).1 hane] at hd
      norm_num at hd
    rcases hc with hc | hc | hc
    · exact heven (by rw [hc])
    · obtain ⟨x, hx, hX⟩ := bender_three_generator X.1 X.2.2
      have hPK : IsPGroup 3 K := IsPGroup.of_card (n := 1) (by simpa using hc)
      have hPX : IsPGroup 3 X.1 := IsPGroup.of_card (n := 1) (by simpa using X.2.2)
      have hsup := hPX.to_sup_of_normal_right' hPK hXN
      obtain ⟨P, hsupP⟩ := hsup.exists_le_sylow
      have hKP : K ≤ (P : Subgroup G) := le_trans le_sup_right hsupP
      have hXP : X.1 ≤ (P : Subgroup G) := le_trans le_sup_left hsupP
      have heq : K = X.1 := by
        have heK := eq_of_le_of_card_ge hKP (by rw [localData.sylow_three P, hc])
        have heX := eq_of_le_of_card_ge hXP (by rw [localData.sylow_three P, X.2.2])
        exact heK.trans heX.symm
      have hxu : Commute x u.1 := mem_centralizer_singleton_iff.mp (hXu (hX ▸ mem_zpowers x))
      have hi := ((hK x).mp (heq ▸ (hX ▸ mem_zpowers x))).2
      have hxinv : x = x⁻¹ := (mul_inv_eq_iff_eq_mul.mpr hxu.symm.eq).symm.trans hi
      have hx2 : x ^ 2 = 1 := by
        calc
          x ^ 2 = x * x := pow_two x
          _ = x * x⁻¹ := congrArg (x * ·) hxinv
          _ = 1 := mul_inv_cancel x
      have hd := orderOf_dvd_of_pow_eq_one hx2
      rw [hx] at hd
      norm_num at hd
    · exact heven (by rw [hc]; decide)
  rcases hc with hc | hc | hc | hc | hc
  · exact Or.inl hc
  · exact (hexclude (Or.inl hc)).elim
  · exact (hexclude (Or.inr (Or.inl hc))).elim
  · exact (hexclude (Or.inr (Or.inr hc))).elim
  · exact Or.inr hc

end CFSG.Quasithin.Janko1CentralizerData
