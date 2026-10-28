module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarMixedF11
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarLeftCartanOvergroup
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBaumann
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarTwoPerfectOmega
public import Theory.GroupTheory.PCoreCoverEquiv
import all CFSG.Quasithin.Chapter6.Section01.SourceHStarLeftCartanOvergroup
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBaumann

/-!
# Left-family adapters for the mixed 6.1.5 pair

These are the checked local consequences used to instantiate the mixed
F.1.1 data in `SourceHStarMixedF11`.  They retain the natural fixed-quotient,
Hall, normalization and faithful-action premises instead of asserting the
missing F.1.12 recognition conclusion.

Source: Aschbacher--Smith 6.1.5, printed pp.666--669
(`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]

/-- The left Borel is `S ⊔ D` when `S` is Sylow in `L ⊔ S` and `D` is the
odd Hall subgroup of the literal local Borel. -/
theorem mixed_left_borel_of_sylow_and_hall
    (T : Sylow 2 G) (L S D : Subgroup G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hST : S ≤ (T : Subgroup G))
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ S))
    (hD : D ≤ RankOneGeneric.localBorel T L)
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (D.subgroupOf (RankOneGeneric.localBorel T L)))
    (hDS : D ≤ normalizer (S : Set G)) :
    ChapterF.Source.borel (L ⊔ S) S = S ⊔ D := by
  have hTLS : (T : Subgroup G) ⊓ L ≤ S := by
    have he := (Chapter1.isSylowIn_iff.mp hS).2.2
      ((T : Subgroup G) ⊓ (L ⊔ S)) (T.isPGroup'.to_le inf_le_left)
      (le_inf hST le_sup_right) inf_le_right
    exact (le_inf inf_le_left (inf_le_right.trans le_sup_left)).trans he.le
  have hSL : S ⊓ L = (T : Subgroup G) ⊓ L :=
    le_antisymm (inf_le_inf_right _ hST) (le_inf hTLS inf_le_right)
  have hB : ((T : Subgroup G) ⊓ L) ⊔ D = RankOneGeneric.localBorel T L := by
    obtain ⟨R, hR⟩ := RankOneGeneric.exists_sylow_localBorel T L hTL
    have he := congrArg (fun A : Subgroup (RankOneGeneric.localBorel T L) =>
      A.map (RankOneGeneric.localBorel T L).subtype)
      (OddHall.sylow_complement_of_hall R hHall).sup_eq_top
    simpa only [Subgroup.map_sup, hR, map_subgroupOf_eq_of_le hD,
      ← MonoidHom.range_eq_map, range_subtype] using he
  change (L ⊔ S) ⊓ normalizer ((S ⊓ (L ⊔ S) : Subgroup G) : Set G) = S ⊔ D
  rw [inf_eq_left.mpr (show S ≤ L ⊔ S from le_sup_right)]
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (L : Set G) * (S : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L S (hST.trans hTL)]
      exact hx.1
    obtain ⟨l, hl, s, hs, hls⟩ := hp
    have hlS : l ∈ normalizer (S : Set G) := by
      have he : l = x * s⁻¹ := eq_mul_inv_iff_mul_eq.mpr hls
      rw [he]
      exact (normalizer (S : Set G)).mul_mem hx.2
        ((normalizer (S : Set G)).inv_mem (S.le_normalizer hs))
    have hlB : l ∈ RankOneGeneric.localBorel T L := by
      refine ⟨hl, ?_⟩
      rw [← hSL]
      exact inf_normalizer_le_normalizer_inf ⟨hlS, L.le_normalizer hl⟩
    have hlSD : l ∈ S ⊔ D := (sup_le_sup_right hTLS D) (hB.symm ▸ hlB)
    rw [← hls]
    exact (S ⊔ D).mul_mem hlSD (mem_sup_left hs)
  · exact sup_le (le_inf le_sup_right S.le_normalizer)
      (le_inf ((hD.trans inf_le_left).trans le_sup_left) hDS)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611

open Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- A natural fixed quotient forces the Baumann subgroup to be Sylow in the
corresponding rank-one join. -/
theorem Input.baumann_sylow_of_natural_quotient
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (L ⊔ ChapterB.baumann (T : Subgroup G)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hZ : ¬ Z ≤ (center H).map H.subtype := by
    intro hc
    apply hZH
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz x hx
    obtain ⟨a,ha,rfl⟩ := hc hz
    exact congrArg H.subtype ((mem_center_iff.mp ha) ⟨x,hx⟩)
  have hLC : ¬ L ≤ omegaCentralizer T := fun hc =>
    natural_quotient_omega_not_fixed hm (le_centralizer_iff.mp hc)
  let hs := h.omega_span_input hLC
  have hj := hs.thompson_moves_of_noncentral_omega hH hZ
  let X := L ⊔ (T : Subgroup G)
  let U := (conjugateSpanBy Z L).subgroupOf X
  let R := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let := hs.reduced_internal.normal
  let := hs.reduced_internal.elementary
  have hSQ : IsSQTK KnownSimple.IsKnownSimple X := by
    have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer h.sylow_normalizes
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hXN)).mp
      ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup (X.subgroupOf (normalizer (L : Set G))))
  have hns : ¬ Group.IsSolvable X := by
    intro hsol
    let := hsol
    exact Chapter1.mem_L_not_isSolvable h.maximal_local.1
      (Group.isSolvable_of_isSolvable_injective
        (inclusion_injective (show L ≤ X from le_sup_left)))
  have hRm : (R : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hJm : (elementaryAbelianMaxJ (R : Subgroup X)).map X.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective, hRm]
  have hjR : ¬ elementaryAbelianMaxJ (R : Subgroup X) ≤ centralizer (U : Set X) := by
    intro hc
    apply hj
    rw [← hJm]
    rintro _ ⟨x,hx,rfl⟩ u hu
    exact congrArg X.subtype (hc hx ⟨u,hs.reduced.1 hu⟩ hu)
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  rcases ChapterE.ThompsonAction.source_nonsolvable_natural_factors
      hSQ R hs.local_minimal_parabolic U hs.reduced_internal hns hjR with
    ⟨hqs,c,hlin|hfive⟩ | ⟨d,_,_⟩
  · obtain ⟨F,hF⟩ := hlin
    have hb := (ChapterE.ThompsonAction.quasisimple_linear_baumann_of_section
      R hs.local_minimal_parabolic U hs.reduced_internal hjR q hq hk hqs c.sectionData F hF).1
    have hbm : (ChapterB.baumann (R : Subgroup X)).map X.subtype =
        ChapterB.baumann (T : Subgroup G) := by
      unfold ChapterB.baumann ChapterB.thompsonAlpha
      rw [baumann_map_injective X.subtype X.subtype_injective,hRm]
    have hout := (Chapter1.IsSylowIn.map_iff X.subtype X.subtype_injective).mpr hb
    have hr : (pResidual 2 X).map X.subtype = L := hs.local_residual_eq
    simpa only [Subgroup.map_sup,hbm,hr] using hout
  · obtain ⟨e⟩ := hfive
    have hf := ChapterE.ThompsonAction.quasisimple_five_source_marker
      R hs.local_minimal_parabolic U hs.reduced_internal hjR q hq hk hqs c.sectionData e
    obtain ⟨A,B,cA⟩ := exists_left_cartan_pair h
    have hb := hs.borel_fixes_omega_of_five_section (le_conjugateSpanBy Z L) hf
    have ha : A ≤ centralizer (Z : Set G) := cA.left_le.trans hb
    have hfaith := left_cartan_faithful_on_omega cA hm
    rw [inf_eq_left.mpr ha] at hfaith
    have hc := cA.left_card h.linear h.sylow_normalizes
    rw [hfaith] at hc
    have hpow : 4 ≤ 2^n := by
      calc 4 = 2^2 := by norm_num
           _ ≤ 2^n := Nat.pow_le_pow_right (by decide) (by have := h.exponent; omega)
    norm_num at hc
    omega
  · have hrank : primeRank 3 X ≤ 1 := by
      rw [←ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)]
      let e : (pResidual 2 X) ≃* L :=
        (equivMapOfInjective (pResidual 2 X) X.subtype X.subtype_injective).trans
          (MulEquiv.subgroupCongr h.local_residual_eq)
      rw [primeRank_congr 3 e]
      exact Chapter4.Section03.RankOneUniqueness.odd_primeRank_le_one h.linear (by decide)
    let P : Sylow 3 X := Classical.choice inferInstance
    have hr : primeRank 3 (X ⧸ C) ≤ 1 :=
      P.primeRank_quotient_le_one (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hrank) C
    have hy := (primeRank_subgroup_le 3 (offenderSubgroup α)).trans hr
    have hd := d.two_le_three_rank
    change 2 ≤ primeRank 3 (offenderSubgroup α) at hd
    omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The natural quotient also gives the Baumann cover and its normalization
by the literal local Borel. -/
theorem Input.baumann_cover_of_natural_quotient
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    ChapterB.baumann (T : Subgroup G) ≤
      ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    localBorel T L ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hZ : ¬ Z ≤ (center H).map H.subtype := by
    intro hc
    apply hZH
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz x hx
    obtain ⟨a,ha,rfl⟩ := hc hz
    exact congrArg H.subtype ((mem_center_iff.mp ha) ⟨x,hx⟩)
  have hLC : ¬ L ≤ omegaCentralizer T := fun hc =>
    natural_quotient_omega_not_fixed hm (le_centralizer_iff.mp hc)
  let hs := h.omega_span_input hLC
  have hj := hs.thompson_moves_of_noncentral_omega hH hZ
  have hb := h.thompson_le_left_sylow_core_of_natural_quotient hH hm hZH
  refine ⟨?_, hs.borel_normalizes_baumann_of_thompson_bound hj hb⟩
  let X := L ⊔ (T : Subgroup G)
  let U := (conjugateSpanBy Z L).subgroupOf X
  let R := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let Q := ((T : Subgroup G) ⊓ L) ⊔ X.pCoreIn 2
  let := hs.reduced_internal.normal
  let := hs.reduced_internal.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hk : q.ker = pCore 2 X :=
    (QuotientGroup.ker_mk' C).trans hs.baumann_reduced_centralizer_core
  have hSQ : IsSQTK KnownSimple.IsKnownSimple X := by
    have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer h.sylow_normalizes
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hXN)).mp
      ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup (X.subgroupOf (normalizer (L : Set G))))
  have hRm : (R : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hJm : (elementaryAbelianMaxJ (R : Subgroup X)).map X.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hRm]
  have hBm : (ChapterB.baumann (R : Subgroup X)).map X.subtype =
      ChapterB.baumann (T : Subgroup G) := by
    unfold ChapterB.baumann ChapterB.thompsonAlpha
    rw [baumann_map_injective X.subtype X.subtype_injective,hRm]
  have hjR : ¬ elementaryAbelianMaxJ (R : Subgroup X) ≤ centralizer (U : Set X) := by
    intro hc
    apply hj
    rw [←hJm]
    rintro _ ⟨x,hx,rfl⟩ u hu
    exact congrArg X.subtype (hc hx ⟨u,hs.reduced.1 hu⟩ hu)
  have hi := ChapterE.ThompsonAction.source_thompson_baumann_image hSQ R
    hs.local_minimal_parabolic U hs.reduced_internal hjR
  rw [←hBm]
  rintro _ ⟨x,hx,rfl⟩
  have hxq : q x ∈ (elementaryAbelianMaxJ (R : Subgroup X)).map q := by
    rw [hi]
    exact mem_map_of_mem q hx
  obtain ⟨y,hy,he⟩ := hxq
  have hdiff : y⁻¹*x ∈ pCore 2 X := by
    rw [←hk]
    change q (y⁻¹*x) = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hyQ : (y : G) ∈ Q := hb (hJm ▸ mem_map_of_mem X.subtype hy)
  have hzQ : ((y⁻¹*x : X) : G) ∈ Q :=
    mem_sup_right (mem_map_of_mem X.subtype hdiff)
  have hh := Q.mul_mem hyQ hzQ
  change X.subtype (y * (y⁻¹*x)) ∈ Q at hh
  simpa only [mul_inv_cancel_left] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

