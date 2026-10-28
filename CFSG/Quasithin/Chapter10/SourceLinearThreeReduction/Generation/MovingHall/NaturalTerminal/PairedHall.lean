module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.HStarFieldOrder
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.HallOrder
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SourceBorelDivisors

/-!
# The moving H-star source is paired, with the full original Hall order

The single natural H-star source would have field order q². Its Borel
forces q²−1 into the original odd Hall order, which divides (q−1)².
Since q+1 and q−1 are coprime, this is impossible. The surviving paired
source has field order q, and its Borel forces the full Hall order (q−1)².
Consequently any containing original torus of that order is this same Hall.
All actions and subgroups remain those selected from the original H orbit.
Source: Aschbacher–Smith 10.2.3(4), printed pp.746–747.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

omit [Finite G] in
private theorem hstar_proper_overgroup_le_overlap
    {M H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (J : Subgroup H) (hSJ : (T.subtype hH.1.1.2 : Subgroup H) ≤ J) (hJ : J ≠ ⊤) :
    J ≤ M.subgroupOf H := by
  have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
    have hh := map_mono (f := H.subtype) hSJ
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hJH : J.map H.subtype < H := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr (lt_top_iff_ne_top.mpr hJ)
    change J.map H.subtype < (⊤ : Subgroup H).map H.subtype at hh
    simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
  exact map_le_iff_le_comap.mp (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)

private theorem odd_dvd_hall_card {X : Type*} [Group X] (C : Subgroup X)
    (hC : IsHallSubgroup Subgroup.OddHall.oddPrimes C) {m : ℕ} (hm : Odd m)
    (hd : m ∣ Nat.card X) : m ∣ Nat.card C := by
  have hc : Nat.Coprime m C.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpm hpi
    exact hC.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpi
      (show p ≠ 2 from fun he => hm.not_two_dvd_nat (he ▸ hpm))
  rw [←C.index_mul_card] at hd
  exact hc.dvd_of_dvd_mul_left hd

theorem Context.hstar_paired_same_field_of_borel
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    let S := T.subtype ctx.hstar.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D ctx.hstar).normal
    letI := (source_hstar_omega_orbit_reduced D ctx.hstar).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    let σ := α.comp Y.subtype
    letI := offenderSubgroup_normal α
    ∃ (d : SourceTwoFactorCase σ) (K : BinaryField),
        Nat.card K.Carrier = Nat.card F ∧ Nonempty (d.MarkedProduct (linearNatural K 2)) ∧
        ∃ t : S.mapSurjective hq,
          d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
          d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first := by
  let S := T.subtype ctx.hstar.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D ctx.hstar
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  have hBR : B.map H.subtype ≤ localOrbit T L :=
    hBB.trans ((map_subtype_le _).trans inf_le_left)
  rcases ctx.hstar_linear_field_alternatives D n hn hF e mark hBR with
    ⟨_,c,K,hK,hlinear⟩ | hp
  · have hd := quasisimple_linear_borel_card_dvd_of_proper_overgroups S U q hq hk c.sectionData K
      hlinear (D.maximalLocal.subgroupOf H) (hstar_proper_overgroup_le_overlap ctx.hstar)
    have hodd : Odd (Nat.card K.Carrier - 1) := by
      have htwo : Even (Nat.card K.Carrier) := by
        rw [K.card_eq]
        exact even_two.pow_of_ne_zero K.degree_pos.ne'
      exact Nat.Even.sub_odd (by have := Finite.one_lt_card (α := K.Carrier); omega) htwo odd_one
    have hdB := odd_dvd_hall_card _ ctx.hall hodd ((dvd_mul_left _ _).trans hd)
    rw [Nat.card_congr (subgroupOfEquivOfLe ctx.hall_le).toEquiv,hK] at hdB
    have hbad := hdB.trans (ctx.hall_card_dvd_torus_square D n hn hF e hBB)
    have hqgt : 1 < Nat.card F := Finite.one_lt_card
    have hqeven : Even (Nat.card F) := by
      rw [hF]
      exact even_two.pow_of_ne_zero (by omega)
    have hqm : Odd (Nat.card F - 1) := Nat.Even.sub_odd (by omega) hqeven odd_one
    have hplus : Nat.card F + 1 ∣ Nat.card F ^ 2 - 1 := by
      refine ⟨Nat.card F - 1,?_⟩
      have hh := Nat.sub_add_cancel (show 1 ≤ Nat.card F by omega)
      have hs := Nat.sub_add_cancel (show 1 ≤ Nat.card F ^ 2 by nlinarith)
      nlinarith
    have hc : Nat.Coprime (Nat.card F + 1) (Nat.card F - 1) := by
      rw [show Nat.card F + 1 = 2 + (Nat.card F - 1) by omega,Nat.coprime_add_self_left]
      exact hqm.coprime_two_left
    have hone := Nat.eq_one_of_dvd_coprimes (hc.pow_right 2) (dvd_refl _) (hplus.trans hbad)
    omega
  · exact hp

/-- The original Hall has the full paired Cartan order. -/
theorem Context.hall_card_eq_torus_square
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    Nat.card B = (Nat.card F - 1)^2 := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D ctx.hstar
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  obtain ⟨d,K,hK,⟨c⟩,_⟩ := ctx.hstar_paired_same_field_of_borel D n hn hF e mark hBB
  have hd := paired_linear_borel_odd_square_dvd_of_proper_overgroups
    (T.subtype ctx.hstar.1.1.2) U q hq hk d K c
    (D.maximalLocal.subgroupOf H) (hstar_proper_overgroup_le_overlap ctx.hstar)
  have hodd : Odd (Nat.card K.Carrier - 1) := by
    have htwo : Even (Nat.card K.Carrier) := by
      rw [K.card_eq]
      exact even_two.pow_of_ne_zero K.degree_pos.ne'
    exact Nat.Even.sub_odd (by have := Finite.one_lt_card (α := K.Carrier); omega) htwo odd_one
  have hdB := odd_dvd_hall_card _ ctx.hall (hodd.pow (n := 2)) hd
  rw [Nat.card_congr (subgroupOfEquivOfLe ctx.hall_le).toEquiv,hK] at hdB
  exact Nat.dvd_antisymm (ctx.hall_card_dvd_torus_square D n hn hF e hBB) hdB

/-- A containing original full torus equals the original Hall, with no choice of a new Hall. -/
theorem Context.hall_image_eq_full_torus
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (C : Subgroup G) (hBC : B.map H.subtype ≤ C)
    (hC : Nat.card C = (Nat.card F - 1)^2) : B.map H.subtype = C := by
  apply eq_of_le_of_card_ge hBC
  rw [card_map_of_injective H.subtype_injective,
    ctx.hall_card_eq_torus_square D n hn hF e mark hBB,hC]

end CFSG.Quasithin.Chapter10.MovingHall
