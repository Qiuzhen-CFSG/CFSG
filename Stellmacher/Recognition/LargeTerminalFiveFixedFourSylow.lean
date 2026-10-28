module

public import Stellmacher.Recognition.LargeTerminalFiveFixedFourNormalizer
public import Theory.GroupTheory.AbelianSylowAutomizer

/-!
# Sylow structure of the actual fixed four-group

Write Q for the second core, A for the order-five subgroup and V = C_Q(A).
The faithful Frobenius quotient of the second local group puts every
A-normalized two-subgroup there inside Q. Confinement of N_G(V), followed
by the normalizer condition in a two-group, then promotes V to a Sylow
two-subgroup of C_G(A). Its normalizer action has odd order dividing both
six and the local order 20480, so it is trivial. Burnside transfer supplies
a normal odd complement. The local five-centralizer has order twenty.
The final normality assembly is kept in LargeTerminalFiveFixedFourNormal.

Source: Thompson VI, printed p.630, the noncyclic four-fixed alternative.
The remaining invariance assertion concerns the odd part of C_G(A).
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix Subgroup

universe u

/-- A five-normalized two-subgroup of the second local group lies in its core. -/
public theorem LargeTerminalContext.five_normalized_two_subgroup_le_second_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A U : Subgroup G) (hA : Nat.card A = 5)
    (hAP : A ≤ ctx.second) (hUP : U ≤ ctx.second)
    (hU : IsPGroup 2 U) (hAU : A ≤ normalizer (U : Set G)) :
    U ≤ twoCoreIn ctx.second := by
  let H := U ⊔ A
  have hUH : U ≤ H := le_sup_left
  have hUnormal : (U.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUH).mpr (sup_le U.le_normalizer hAU)
  have hUcore : U.subgroupOf H ≤ pCore 2 H :=
    le_sSup ⟨hUnormal, hU.of_equiv (subgroupOfEquivOfLe hUH).symm⟩
  have hUcore' : U ≤ twoCoreIn H := by
    rw [← map_subgroupOf_eq_of_le hUH]
    exact map_mono hUcore
  exact hUcore'.trans (ctx.five_overgroup_core_le_second_core A H hA
    le_sup_right (sup_le hUP hAP))

/-- The actual fixed four-group is a Sylow two-subgroup of the full
five-centralizer. The normalizer condition excludes every larger two-overgroup. -/
public theorem LargeTerminalContext.exists_five_centralizer_sylow_eq_fixed_four
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    ∃ T : Sylow 2 (centralizer (A : Set G)),
      (T : Subgroup (centralizer (A : Set G))) =
        (twoCoreIn ctx.second ⊓ centralizer (A : Set G)).subgroupOf
          (centralizer (A : Set G)) := by
  let C := centralizer (A : Set G)
  let V := twoCoreIn ctx.second ⊓ C
  let VC := V.subgroupOf C
  have hVC : V ≤ C := inf_le_right
  have hVtwo : IsPGroup 2 V :=
    ((pCore_isPGroup (p := 2) (G := ctx.second)).map ctx.second.subtype).to_le inf_le_left
  have hVCtwo : IsPGroup 2 VC := hVtwo.of_equiv (subgroupOfEquivOfLe hVC).symm
  obtain ⟨T, hVT⟩ := hVCtwo.exists_le_sylow
  refine ⟨T, ?_⟩
  by_contra hne
  have hproper : VC.subgroupOf (T : Subgroup C) < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact fun h => hne (le_antisymm h hVT)
  let _ : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent
    (VC.subgroupOf (T : Subgroup C)) hproper
  obtain ⟨t, htN, htV⟩ := SetLike.exists_of_lt hlt
  have htNC : (t : C) ∈ normalizer (VC : Set C) := by
    rw [← subgroupOf_normalizer_eq hVT] at htN
    exact htN
  let D := ((T : Subgroup C) ⊓ normalizer (VC : Set C)).map C.subtype
  have hDC : D ≤ C := map_subtype_le _
  have hDtwo : IsPGroup 2 D := (T.isPGroup'.to_le inf_le_left).map C.subtype
  have hDN : D ≤ normalizer (V : Set G) := by
    have hh := (map_mono (inf_le_right :
      (T : Subgroup C) ⊓ normalizer (VC : Set C) ≤ normalizer (VC : Set C))).trans
        (le_normalizer_map (H := VC) C.subtype)
    rwa [map_subgroupOf_eq_of_le hVC] at hh
  have hDP : D ≤ ctx.second := hDN.trans
    (ctx.five_fixed_four_normalizer_le_second hS A hA hAP hAN hcard hncyc hfixed)
  have hAD : A ≤ normalizer (D : Set G) :=
    (le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le_normalizer _)
  have hDQ := ctx.five_normalized_two_subgroup_le_second_core A D hA hAP hDP hDtwo hAD
  have htD : ((t : C) : G) ∈ D := mem_map.mpr ⟨t, ⟨t.property, htNC⟩, rfl⟩
  exact htV (show ((t : C) : G) ∈ V from ⟨hDQ htD, (t : C).property⟩)

/-- The normalizer inside the full five-centralizer acts trivially on its
fixed-four Sylow subgroup: the action order is odd and divides both six and 20480. -/
public theorem LargeTerminalContext.five_fixed_four_normalizer_le_centralizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    let C := centralizer (A : Set G)
    let V := (twoCoreIn ctx.second ⊓ C).subgroupOf C
    normalizer (V : Set C) ≤ centralizer (V : Set C) := by
  let C := centralizer (A : Set G)
  let V := twoCoreIn ctx.second ⊓ C
  let VC := V.subgroupOf C
  have hVC : V ≤ C := inf_le_right
  obtain ⟨T, hT⟩ := ctx.exists_five_centralizer_sylow_eq_fixed_four
    hS A hA hAP hAN hcard hncyc hfixed
  have hVfour : IsKleinFour V := (ctx.five_fixed_four_ambient_data A hAN hcard hncyc hfixed).1
  let _ := hVfour
  let e : VC ≃* V := subgroupOfEquivOfLe hVC
  let _ : IsKleinFour VC := ⟨(Nat.card_congr e.toEquiv).trans IsKleinFour.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two⟩
  have hTcomm : IsMulCommutative T := by
    rw [hT]
    exact IsKleinFour.isMulCommutative
  let _ := hTcomm
  have hodd := T.odd_card_normalizer_action
  rw [hT] at hodd
  let f := VC.normalizerMonoidHom
  have hN : (normalizer (VC : Set C)).map C.subtype ≤ ctx.second := by
    have hh := le_normalizer_map (H := VC) C.subtype
    rw [map_subgroupOf_eq_of_le hVC] at hh
    exact hh.trans (ctx.five_fixed_four_normalizer_le_second
      hS A hA hAP hAN hcard hncyc hfixed)
  have hNcard : Nat.card (normalizer (VC : Set C)) ∣ 20480 := by
    rw [← card_map_of_injective C.subtype_injective]
    exact ctx.second_card_of_large_card hS ▸ card_dvd_of_le hN
  have hf6 : Nat.card f.range ∣ 6 := IsKleinFour.card_mulAut VC ▸ f.range.card_subgroup_dvd_card
  have hf20480 : Nat.card f.range ∣ 20480 := (card_range_dvd f).trans hNcard
  have hf2 : Nat.card f.range ∣ 2 := by
    simpa using Nat.dvd_gcd hf6 hf20480
  have hf1 : Nat.card f.range = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hf2 with h | h
    · exact h
    · rw [h] at hodd
      norm_num at hodd
  have hfbot : f.range = ⊥ := card_eq_one.mp hf1
  change normalizer (VC : Set C) ≤ centralizer (VC : Set C)
  intro c hc
  have he : f ⟨c, hc⟩ = 1 := mem_bot.mp (hfbot ▸ show f ⟨c, hc⟩ ∈ f.range from ⟨⟨c, hc⟩, rfl⟩)
  have hk : (⟨c, hc⟩ : normalizer (VC : Set C)) ∈ f.ker := he
  rwa [normalizerMonoidHom_ker] at hk

/-- Burnside transfer gives a normal odd complement to the actual fixed four.
This asserts a complement, not normality of the four-group. -/
public theorem LargeTerminalContext.five_centralizer_exists_normal_odd_complement
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    let C := centralizer (A : Set G)
    let V := (twoCoreIn ctx.second ⊓ C).subgroupOf C
    ∃ K : Subgroup C, K.Normal ∧ Odd (Nat.card K) ∧ K.IsComplement' V := by
  let C := centralizer (A : Set G)
  let V := (twoCoreIn ctx.second ⊓ C).subgroupOf C
  obtain ⟨T, hT⟩ := ctx.exists_five_centralizer_sylow_eq_fixed_four
    hS A hA hAP hAN hcard hncyc hfixed
  have hNC : normalizer (T : Set C) ≤ centralizer (T : Set C) := by
    change normalizer ((T : Subgroup C) : Set C) ≤ centralizer ((T : Subgroup C) : Set C)
    rw [hT]
    exact ctx.five_fixed_four_normalizer_le_centralizer hS A hA hAP hAN hcard hncyc hfixed
  let f := MonoidHom.transferSylow T hNC
  refine ⟨f.ker, inferInstance, ?_, ?_⟩
  · exact Nat.not_even_iff_odd.mp (fun h =>
      MonoidHom.not_dvd_card_ker_transferSylow T hNC h.two_dvd)
  · exact hT ▸ MonoidHom.ker_transferSylow_isComplement' T hNC

/-- The centralizer inside the second local group has order twenty.
This uses the actual Sylow four and the local order, without global confinement. -/
public theorem LargeTerminalContext.five_centralizer_inter_second_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    Nat.card (ctx.second ⊓ centralizer (A : Set G) : Subgroup G) = 20 := by
  let C := centralizer (A : Set G)
  let L := ctx.second ⊓ C
  let V := twoCoreIn ctx.second ⊓ C
  have hVC : V ≤ C := inf_le_right
  have hVL : V ≤ L := inf_le_inf_right C (twoCoreIn_le _)
  have hVcard : Nat.card V = 4 :=
    (ctx.five_fixed_four_ambient_data A hAN hcard hncyc hfixed).1.card_four
  obtain ⟨T, hT⟩ := ctx.exists_five_centralizer_sylow_eq_fixed_four
    hS A hA hAP hAN hcard hncyc hfixed
  have hTL : (T : Subgroup C) ≤ L.subgroupOf C := by
    rw [hT]
    exact fun t ht => hVL ht
  let U := T.subtype hTL
  have hUcard : Nat.card U = 4 := by
    change Nat.card ((T : Subgroup C).subgroupOf (L.subgroupOf C)) = 4
    rw [Nat.card_congr (subgroupOfEquivOfLe hTL).toEquiv]
    rw [hT, Nat.card_congr (subgroupOfEquivOfLe hVC).toEquiv]
    exact hVcard
  have hLcard : Nat.card (L.subgroupOf C) = Nat.card L :=
    Nat.card_congr (subgroupOfEquivOfLe (show L ≤ C from inf_le_right)).toEquiv
  have hcount := (U : Subgroup (L.subgroupOf C)).card_mul_index
  rw [hUcard, hLcard] at hcount
  have hLdiv : Nat.card L ∣ 20480 := ctx.second_card_of_large_card hS ▸
    card_dvd_of_le (show L ≤ ctx.second from inf_le_left)
  have hidx : (U : Subgroup (L.subgroupOf C)).index ∣ 5120 := by
    rw [← hcount] at hLdiv
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp hLdiv
  have hcop : Nat.Coprime (U : Subgroup (L.subgroupOf C)).index 1024 := by
    exact ((Nat.prime_two.coprime_iff_not_dvd.mpr U.not_dvd_index).symm).pow_right 10
  have hi5 : (U : Subgroup (L.subgroupOf C)).index ∣ 5 :=
    hcop.dvd_of_dvd_mul_left hidx
  have hbound : Nat.card L ≤ 20 := by
    have hh := Nat.le_of_dvd (by decide : 0 < 5) hi5
    omega
  have h4 : 4 ∣ Nat.card L := hVcard ▸ card_dvd_of_le hVL
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  have hAC : A ≤ C := le_centralizer_iff_isMulCommutative.mpr inferInstance
  have h5 : 5 ∣ Nat.card L := hA ▸ card_dvd_of_le (le_inf hAP hAC)
  have h20 : 20 ∣ Nat.card L := (show Nat.Coprime 4 5 by decide).mul_dvd_of_dvd_of_dvd h4 h5
  exact le_antisymm hbound (Nat.le_of_dvd Nat.card_pos h20)

end Stellmacher.Recognition
