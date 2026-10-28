module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.HStarGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.OddFixedCenter
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleOddFixed
public import Stellmacher.ElementaryAbelianMaxJFixedIntersection
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OriginalFixedCenter
/-!
# Original fixed centers for all odd-order Hall elements

The original H-star omega-orbit has a single or exchanged natural source.
An odd-order nonidentity element has nontrivial action, because the seed
centralizer is its Sylow two-group. The genuine quotient coordinates and
Sylow exchanger show that its omega-center fixed points are exactly those
of H. Comparing with the original Hall fixed-center theorem eliminates the
original orbit's fixed center as well.

This discharges both fixed-center premises of the common block alternative.
Hall containment and the seed-centralizer identity remain earlier source
obligations of the moving-Hall assembly owner.
Source: Aschbacher–Smith E.2.3 and 10.2.3(4), printed pp.216–217 and746.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false in
theorem Context.hstar_intrinsic_odd_fixed_center
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype ctx.hstar.1.1.2 : Subgroup H))
    (b : H) (m : ℕ) (hm : Odd m) (hb : b^m = 1) (hne : b ≠ 1) :
    omegaOneCenterAmbient (T.subtype ctx.hstar.1.1.2 : Subgroup H) ⊓ centralizer ({b} : Set H) =
      omegaOneCenterAmbient (T.subtype ctx.hstar.1.1.2 : Subgroup H) ⊓ centralizer (⊤ : Subgroup H) := by
  let S := T.subtype ctx.hstar.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D ctx.hstar
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hP := source_hstar_minimal_parabolic_of_generation_gt_one D ctx.hstar ctx.large
  have hJ := ctx.hstar_thompson_moves_omega_orbit D n hn hF e
  have hZU : omegaOneCenterAmbient (S : Subgroup H) ≤ U := by
    rw [show U = normalClosure (omegaOneCenterAmbient (S : Subgroup H) : Set H) from
      source_hstar_omega_orbit_eq_normalClosure D ctx.hstar]
    exact subset_normalClosure
  have hbR : b ∈ pResidual 2 H := mem_pResidual_of_orderOf_coprime
    (hm.coprime_two_left.of_dvd_right (orderOf_dvd_of_pow_eq_one hb))
  let bR : pResidual 2 H := ⟨b,hbR⟩
  have hbRm : bR^m=1 := by
    apply Subtype.ext
    exact hb
  have hmove : b ∉ centralizer (U : Set H) := by
    intro hc
    have hbS : b ∈ (S : Subgroup H) := hCZ.le
      ((centralizer_le (subgroupOf_mono H (le_conjugateSpanBy _ _))) hc)
    let bS : (S : Subgroup H) := ⟨b,hbS⟩
    have hc := S.isPGroup'.orderOf_coprime hm.coprime_two_left bS
    have hbSm : bS^m = 1 := Subtype.ext hb
    have ho : orderOf bS = 1 := by
      apply Nat.dvd_one.mp
      rw [←hc.gcd_eq_one]
      exact Nat.dvd_gcd dvd_rfl (orderOf_dvd_of_pow_eq_one hbSm)
    exact hne (congrArg (S : Subgroup H).subtype (orderOf_eq_one_iff.mp ho))
  have heq : omegaOneCenterAmbient (S : Subgroup H) ⊓ centralizer ({b} : Set H) =
      omegaOneCenterAmbient (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H) := by
    rcases ctx.hstar_linear_alternatives_of_seed_centralizer D n hn hF e hCZ with
      ⟨hqs,c,K,hlinear⟩ | ⟨d,K,⟨c⟩,hexchange⟩
    · have hZa : omegaOneCenterAmbient (S : Subgroup H) ≤ thompsonAlpha (S : Subgroup H) :=
        omegaCenter_le_omegaCenter_maxJ (S : Subgroup H)
      have ha := (ctx.hstar_alpha_and_span D n hn hF e).1
      exact quasisimple_linear_odd_fixed_center S hP U hU hJ q hq hk hqs
        c.sectionData K hlinear (omegaOneCenterAmbient (S : Subgroup H))
        (hZa.trans (ha.le.trans (sup_le_sup inf_le_left inf_le_right))) bR m hm hbRm hmove
    · exact paired_source_odd_fixed_center S hP U hU hJ q hq hk d K c hexchange hZU bR m hm hbRm hmove
  rw [heq]
  apply le_antisymm
  · intro z hz
    refine ⟨hz.1,?_⟩
    have hR : pResidual 2 H ≤ centralizer ({z} : Set H) := by
      intro r hr x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact (hz.2 r hr).symm
    have hS : (S : Subgroup H) ≤ centralizer ({z} : Set H) := by
      intro t ht x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2 t ht).symm
    have htop : (⊤ : Subgroup H) ≤ centralizer ({z} : Set H) := by
      rw [←pResidual_sup_sylow_eq_top S]
      exact sup_le hR hS
    intro x hx
    exact (htop hx z (Set.mem_singleton _)).symm
  · exact inf_le_inf_left _ (centralizer_le le_top)


/-- Every nonidentity odd-order element in H* has precisely the H*-fixed original omega-center. -/
theorem Context.hstar_odd_fixed_center
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype ctx.hstar.1.1.2 : Subgroup H))
    (b : H) (m : ℕ) (hm : Odd m) (hb : b^m = 1) (hne : b ≠ 1) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer ({(b:G)} : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) := by
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
    fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hz : omegaOneCenterAmbient (T.subtype ctx.hstar.1.1.2 : Subgroup H) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (hZT.trans ctx.hstar.1.1.2)]
    congr 1
    exact map_subgroupOf_eq_of_le ctx.hstar.1.1.2
  have he := ctx.hstar_intrinsic_odd_fixed_center D n hn hF e hCZ b m hm hb hne
  rw [hz] at he
  apply le_antisymm
  · intro z hzin
    let zH : H := ⟨z,ctx.hstar.1.1.2 (hZT hzin.1)⟩
    have hzH : zH ∈ (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H ⊓
        centralizer ({b} : Set H) := by
      refine ⟨hzin.1,?_⟩
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact Subtype.ext (hzin.2 b (Set.mem_singleton _))
    have hfixed := (he.le hzH).2
    refine ⟨hzin.1,?_⟩
    intro x hx
    exact congrArg H.subtype (hfixed ⟨x,hx⟩ (mem_top _))
  · intro z hz
    exact ⟨hz.1,fun x hx => Set.mem_singleton_iff.mp hx ▸ hz.2 b b.property⟩


/-- The same original Hall now eliminates both local fixed centers. -/
theorem Context.original_fixed_centers_eq_bot
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype ctx.hstar.1.1.2 : Subgroup H)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥ := by
  obtain ⟨b,hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp ctx.hall_ne_bot
  have hne : (b:H) ≠ 1 := fun he => hb (Subtype.ext he)
  have hpow : (b:H) ^ Nat.card B = 1 := by
    exact congrArg B.subtype (pow_card_eq_one' (x := b))
  have hfixed := ctx.hstar_odd_fixed_center D n hn hF e hCZ b (Nat.card B)
    ctx.hall_odd hpow hne
  have horig := ctx.original_hall_fixed_center n hn hF e hBR
  refine ⟨bot_unique ?_,horig.2⟩
  rw [←horig.1,←horig.2,←hfixed]
  apply inf_le_inf_left
  apply centralizer_le
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  exact mem_map_of_mem H.subtype b.property

end CFSG.Quasithin.Chapter10.MovingHall
