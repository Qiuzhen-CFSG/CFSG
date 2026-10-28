module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarCartanOvergroup
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.SylowActors
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldQrc

/-!
# A single left Hall subgroup for the source H-star join

Source 6.1.5 chooses an odd Hall subgroup A of N_L(T ∩ L), without
choosing a Hall subgroup of N_G(L) ∩ H. We construct the needed left
Hall using an auxiliary compatible pair with right ambient subgroup T.
That right ambient is a solvable two-group, so the construction requires
no generation-greater-than-one or overlap-solvability hypothesis on H.

The natural quotient makes A ∩ C_G(Ω₁(Z(T))) trivial. The left-only
Cartan and common-normal arguments then show that A ∨ H belongs to H(T),
while the local Borel gives AT = TA. The final consumer applies B.5.6
to the actual enlarged omega orbit and its centralizer quotient.

The natural fixed quotient remains the earlier source input; the
centralizer equality and final contradiction are subsequent source steps.
The private Cartan imports reuse the checked natural-quotient argument
without changing its existing public interfaces.

Source: Aschbacher--Smith 5.1.7(2)(iii), 6.1.5, printed pp.632--634,
666--667 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sylow_normalizes_left_borel {T : Sylow 2 G} {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) := by
  let U := (T : Subgroup G) ⊓ L
  exact (le_inf hTL
    ((le_inf (T : Subgroup G).le_normalizer hTL).trans
      inf_normalizer_le_normalizer_inf |>.trans (normalizer (U : Set G)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf

private theorem exists_left_cartan_pair {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    ∃ A B : Subgroup G, CartanPair T L (T : Subgroup G) A B := by
  have hTsol : Group.IsSolvable (T : Subgroup G) :=
    @IsNilpotent.to_isSolvable _ _ T.isPGroup'.isNilpotent
  have he : normalizer (L : Set G) ⊓ (T : Subgroup G) = (T : Subgroup G) :=
    inf_eq_right.mpr h.sylow_normalizes
  have hp : CartanPreparation T L (T : Subgroup G) := {
    borel_solvable := localBorel_isSolvable h.exponent h.linear h.sylow_normalizes
    intersection_solvable := he.symm ▸ hTsol
    intersection_normalizes := he.symm ▸ sylow_normalizes_left_borel h.sylow_normalizes }
  exact hp.exists_cartanPair

private theorem left_cartan_residual_normalized
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L (T : Subgroup G) A B)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    H ⊓ normalizer (L : Set G) ≤ normalizer (residual (A ⊔ (T : Subgroup G)) : Set G) := by
  let C := localBorel T L
  let J := C ⊔ (T : Subgroup G)
  have hLH : ¬ L ≤ H := by
    intro hl
    have hAH : A ≤ H := c.left_le.trans (inf_le_left.trans hl)
    exact hH.1.1.1 (by simpa only [sup_eq_right.mpr hAH] using hz)
  have hHN : normalizer (L : Set G) ⊓ H ≤ normalizer (C : Set G) :=
    intersection_normalizes_localBorel h.linear h.sylow_normalizes hH.1.1.2 hLH
  have hTN : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    sylow_normalizes_left_borel h.sylow_normalizes
  have he : J = A ⊔ (T : Subgroup G) := by
    change C ⊔ (T : Subgroup G) = A ⊔ (T : Subgroup G)
    rw [show C = ((T : Subgroup G) ⊓ L) ⊔ A from
      (c.left_sup_intersection h.sylow_normalizes).symm]
    exact le_antisymm (sup_le (sup_le (inf_le_left.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  let : (C.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le C.le_normalizer hTN)
  have hr := pResidual_of_normal_pGroup_supplement 2 (C.subgroupOf J)
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype
    (by rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])
  have hm := congrArg (map J.subtype) hr
  rw [map_embedded_pResidual,map_subgroupOf_eq_of_le le_sup_left] at hm
  have hr' : residual (A ⊔ (T : Subgroup G)) = residual C := by
    change residual C = residual J at hm
    exact he ▸ hm.symm
  rw [hr',inf_comm]
  exact hHN.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))

private theorem left_cartan_qrc_hypotheses
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L (T : Subgroup G) A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    Chapter3.QrcHypotheses T (normalizer (L : Set G))
      (A ⊔ (T : Subgroup G)) H
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let X := conjugateSpanBy Z A
  let J := A ⊔ (T : Subgroup G)
  have hg := h.natural_quotient_cartan_span c hm
  have hr := h.natural_quotient_cartan_span_reduced c hm
  let := hr.2.1
  have hJN : J ≤ normalizer (X : Set G) := reduced_normalizes hr
  have hcore := reduced_torus_centralizer hr
    (torus_join_card c h.sylow_normalizes h.linear le_rfl) hg.2.1
  refine ⟨le_sup_right,
    sup_le (c.left_le.trans (inf_le_left.trans L.le_normalizer)) h.sylow_normalizes,
    hH,hr.1,hJN,hr.2.1,?_,hcore,Or.inl (left_cartan_residual_normalized h hH c hz)⟩
  exact Chapter3.Section02.internalActionImage_core_of_reduced J X hr.1 hJN
    (show IsPReduced 2 (X.subgroupOf J) from
      ⟨hr.2.2.choose,IsElementaryAbelian.subgroupOf hr.1,hr.2.2.choose_spec⟩)

private theorem left_borel_thompson_of_noncentral_omega
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L (T : Subgroup G) A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    localBorel T L ⊔ (T : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hLC : ¬ L ≤ omegaCentralizer T := fun hc =>
    natural_quotient_omega_not_fixed hm (le_centralizer_iff.mp hc)
  let hs := h.omega_span_input hLC
  rcases hs.borel_thompson_or_five_section
      (hs.thompson_moves_of_noncentral_omega hH hZ) with hJN | hf
  · exact hJN.2
  have hb := hs.borel_fixes_omega_of_five_section (le_conjugateSpanBy Z L) hf
  have ha : A ≤ centralizer (Z : Set G) := c.left_le.trans hb
  have he : conjugateSpanBy Z A = Z := le_antisymm
    (conjugateSpanBy_le le_rfl (ha.trans (Subgroup.centralizer_le_normalizer _)))
    (le_conjugateSpanBy Z A)
  have hfaith := (h.natural_quotient_cartan_span c hm).2.1
  rw [he,inf_eq_left.mpr ha] at hfaith
  have hc := c.left_card h.linear h.sylow_normalizes
  rw [hfaith] at hc
  have hpow : 4 ≤ 2^n := by
    calc 4 = 2^2 := by norm_num
         _ ≤ 2^n := Nat.pow_le_pow_right (by decide) (by have := h.exponent; omega)
  norm_num at hc
  omega

private theorem left_cartan_join_core_ne_bot
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L (T : Subgroup G) A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    (A ⊔ H).pCoreIn 2 ≠ ⊥ := by
  intro hz
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    intro hc
    apply hZH
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz x hx
    obtain ⟨a,ha,rfl⟩ := hc hz
    exact congrArg H.subtype ((mem_center_iff.mp ha) ⟨x,hx⟩)
  have hJN := left_borel_thompson_of_noncentral_omega h hH c hm hZ
  let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A
  let J := A ⊔ (T : Subgroup G)
  let hq := left_cartan_qrc_hypotheses h hH c hm hz
  have hnocommon : ¬ ∃ N : Subgroup G, N ≤ J.pCoreIn 2 ∧ N ≠ ⊥ ∧
      Chapter3.NormalIn N (Chapter3.generated J H) := by
    rintro ⟨N,hNc,hN,hn⟩
    have hNT : N ≤ (T : Subgroup G) := hNc.trans (hq.core_eq_centralizer ▸ inf_le_left)
    have hgen : Chapter3.generated J H = A ⊔ H := by
      dsimp only [J]
      rw [Chapter3.generated_eq_sup,sup_assoc,sup_eq_right.mpr hTH]
    have hnorm : A ⊔ H ≤ normalizer (N : Set G) := by
      simpa only [hgen] using (Chapter3.normalIn_iff_le_normalizer.mp hn).2
    have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hNT)
      (hNT.trans (hTH.trans le_sup_right)) hnorm
    exact hN (bot_unique (hz ▸ hcore))
  let d := hq.toQRCConfiguration hnocommon
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hE => hE.1
  have hJcore : elementaryAbelianMaxJ (T : Subgroup G) ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT) (hJT.trans le_sup_right)
      ((sup_le_sup_right c.left_le _).trans hJN)
  have hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (X : Set G) :=
    hJcore.trans (hq.core_eq_centralizer ▸ inf_le_right)
  have hRne : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hX : X = ⊥ := bot_unique (d.module_le_core.trans_eq he)
    exact (h.natural_quotient_cartan_span c hm).2.2 hX
  obtain ⟨N,hNR,hN,hnN⟩ := hq.common_normal_of_residual_sylow
    (Chapter3.source_common_normal_knownSimple h.qtke T) hRne
    (residual_sylow_of_reduced_module hq h.qtke (h.hstar_minimal_parabolic hH) hJ _
      (h.hstar_omega_orbit_reduced hH) (h.hstar_thompson_moves_omega_orbit hH hZH))
  exact hnocommon ⟨N,hNR,hN,hnN⟩

omit [Finite G] in
private theorem left_cartan_faithful_on_omega
    {T : Sylow 2 G} {L A B : Subgroup G} {n : ℕ}
    (c : CartanPair T L (T : Subgroup G) A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) :
    A ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  obtain ⟨z,hz,hzC⟩ := Set.not_subset.mp (natural_quotient_omega_not_fixed hm)
  apply _root_.eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have ho : Odd (orderOf x) := hoA.of_dvd_nat (by
    rw [←Subgroup.orderOf_mk x hx.1]
    exact orderOf_dvd_natCard _)
  exact natural_quotient_odd_point_stabilizer hm (c.left_le hx.1).1 ho
    (le_conjugateSpanBy Z L hz) hzC
    (mul_inv_eq_iff_eq_mul.mpr ((hx.2 z hz).symm))

/-- The chosen left Hall permutes with T, has trivial omega-centralizer,
and generates an H(T)-member with the actual H-star subgroup. -/
theorem Input.exists_hstar_left_cartan_overgroup_of_natural_quotient
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    ∃ A : Subgroup G, A ≤ localBorel T L ∧
      IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (localBorel T L)) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      A ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ ∧
      A ⊔ H ∈ Chapter1.HOver G (T : Set G) := by
  obtain ⟨A,B,c⟩ := exists_left_cartan_pair h
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  exact ⟨A,c.left_le,c.left_hall,c.left_permutes_sylow h.sylow_normalizes,
    left_cartan_faithful_on_omega c hm,left_cartan_join_core_ne_bot h hH c hm hZH,
    hTH.trans le_sup_right⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The original 6.1.5 hypotheses supply the left Hall and its actual join,
without a right Hall or overlap-solvability premise. -/
theorem exists_hstar_left_cartan_overgroup
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    ∃ A : Subgroup G, A ≤ RankOneGeneric.localBorel T L ∧
      IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (RankOneGeneric.localBorel T L)) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      A ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ ∧
      A ⊔ H ∈ Chapter1.HOver G (T : Set G) := by
  exact (h.rankOneInput hout).exists_hstar_left_cartan_overgroup_of_natural_quotient
    (h.maximal_eq_normalizer_L ▸ hH) hm hZH

/-- Apply B.5.6 to the constructed join and its literal omega-orbit quotient. -/
theorem exists_hstar_left_cartan_offender_classification
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    ∃ (A : Subgroup G) (hX : A ⊔ H ∈ Chapter1.HOver G (T : Set G)),
      A ≤ RankOneGeneric.localBorel T L ∧
      IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (RankOneGeneric.localBorel T L)) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      A ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ ∧
      (let X := A ⊔ H
       let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
       letI : U.Normal := (h.overgroup_omega_orbit_reduced hX).normal
       letI : IsElementaryAbelian 2 U := (h.overgroup_omega_orbit_reduced hX).elementary
       let C := centralizer (U : Set X)
       let q := QuotientGroup.mk' C
       let ρ : Representation (ZMod 2) (X ⧸ C) (Additive U) :=
         NormalElementaryQuotient.representation U q
           (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
       Representation.BinaryOffender.IsFFModule ρ ∧
         ChapterB.SourceInduction.NontrivialAdequateAlternative
           (ρ.comp (Representation.BinaryOffender.offenderSubgroup ρ).subtype)) := by
  obtain ⟨A,hA,hHall,hperm,hfaith,hX⟩ := h.exists_hstar_left_cartan_overgroup hout hH hm hZH
  exact ⟨A,hX,hA,hHall,hperm,hfaith,
    h.hstar_overgroup_offender_classification hout hH hZH le_sup_right hX⟩

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
