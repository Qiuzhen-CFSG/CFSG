module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.ExceptionalSixGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.Restriction
public import Theory.Representation.CentralFixedPointCohomology


/-!
# The second-choice Â₆ exclusion in original15.3.21

The central cubic quadratic relation kills first cohomology of the actual
U module. Correcting an omega-center element by U makes it centralize L.
When the original Y₊ fixes that element, the correction is Y₊-fixed, hence
trivial by the proved rank-two cubic-center argument. Thus the original
first plane centralizes L, contradicting its source11 normalizer bound.

The final consumer retains the original hypotheses and the actual second
choice of15.3.10; every local containment, correction and quotient map is
constructed. Source: Aschbacher–Smith15.3.21,p.1127 andC.1.22,p.129.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC ChapterC.ExceptionalRestrictions
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

theorem exceptionalSix_of_equiv (e : A ≃* B) (h : IsExceptionalAhat6Block A) :
    IsExceptionalAhat6Block B := by
  let a := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := h.2.1
  have hz : (center (A ⧸ pCore 2 A)).map a.toMonoidHom = center (B ⧸ pCore 2 B) := by
    ext b
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (centerCongr a ⟨x,hx⟩).property
    · intro hb
      exact ⟨a.symm b,(centerCongr a.symm ⟨b,hb⟩).property,a.apply_symm_apply b⟩
  obtain ⟨b⟩ := h.2.2.2.1
  refine ⟨RankOne.Solvable.isShort_of_equiv e h.1,IsQuasisimple.of_mulEquiv a,
    (Nat.card_congr (centerCongr a).toEquiv).symm.trans h.2.2.1,
    ⟨(QuotientGroup.congr _ _ a hz).symm.trans b⟩,?_,?_⟩
  · rw [←RankOne.Solvable.blockU_map_equiv e,card_map_of_injective e.injective]
    exact h.2.2.2.2.1
  · rw [←RankOne.Solvable.blockU_map_equiv e,←Theory.Quasithin.map_centralizer e,
      h.2.2.2.2.2,pCore_map_iso]

private theorem binary_add_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (v : V) : v + v = 0 := by
  have h := @two_smul (ZMod 2) V _ _ _ v
  rw [show (2 : ZMod 2) = 0 by decide,zero_smul] at h
  exact h.symm

theorem exceptionalSix_u_H1_subsingleton (h : IsExceptionalAhat6Block A) :
    letI := h.1.elementary
    Subsingleton (H1 (uRepresentation h.1)) := by
  let := h.1.elementary
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (A ⧸ pCore 2 A)) 3
    (by rw [h.2.2.1])
  have hz1 : (z : A ⧸ pCore 2 A) ≠ 1 := by
    intro he
    have hh : z = 1 := Subtype.ext he
    rw [hh,orderOf_one] at hz
    contradiction
  have hz3 : (z : A ⧸ pCore 2 A) ^ 3 = 1 := congrArg Subtype.val (hz ▸ pow_orderOf_eq_one z)
  let ρ := uRepresentation h.1
  have hfix (v : Additive (blockU A)) (hv : ρ z v = v) : v = 0 := by
    have hzero := LinearMap.congr_fun (central_cubic_quadratic h z z.property hz1 hz3) v
    change ρ z (ρ z v) + ρ z v + v = 0 at hzero
    rw [hv,hv,binary_add_self,zero_add] at hzero
    exact hzero
  let T := ρ z - 1
  have hi : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro v hv
    exact hfix v (sub_eq_zero.mp hv)
  apply subsingleton_H1_of_central_fixedPointFree ρ z z.property hfix
  intro v
  obtain ⟨w,hw⟩ := LinearMap.surjective_of_injective hi v
  exact ⟨w,hw⟩

variable {G : Type*} [Group G] [Finite G]

theorem exceptionalSix_fixed_correction
    (L : Subgroup G) (hL : IsBlock L) (hm : IsExceptionalAhat6Block L)
    (Q : Subgroup G) (hQ : Q ≤ pCore 2 G)
    (hc : Q ≤ centralizer (pCore 2 G : Set G)) (x : Q) :
    ∃ u : (blockU L).map L.subtype, (u : G)⁻¹ * x ∈ centralizer (L : Set G) := by
  let := hm.1.elementary
  let := exceptionalSix_u_H1_subsingleton hm
  let π := QuotientGroup.mk' (pCore 2 L)
  have hcomm : ⁅L,Q⁆ ≤ (blockU L).map L.subtype := by
    rw [commutator_comm]
    exact (commutator_mono hQ le_rfl).trans
      (commutator_le_core_commutator_of_isSubnormal L (pCore 2 G)
        hL.subnormal hL.short.twoPerfect pCore_isPGroup le_normalizer_of_normal)
  have hker : ∀ l ∈ π.ker, ∀ y ∈ Q, ⁅(l : G),y⁆ ∈ (⊥ : Subgroup G) := by
    intro l hl y hy
    have hl' : l ∈ pCore 2 L := by simpa only [π,QuotientGroup.ker_mk'] using hl
    have hc' := hc hy (l : G)
      (pCoreIn_le_of_subnormal 2 hL.subnormal (mem_map_of_mem L.subtype hl'))
    exact commutatorElement_eq_one_iff_mul_comm.mpr hc'
  obtain ⟨u,hu⟩ := (RankOne.ExceptionalSevenControl.blockSection L hm.1).exists_fixed_mod_kernel
    π (QuotientGroup.mk'_surjective _) Q hcomm hker x
  refine ⟨u,fun l hl => ?_⟩
  exact commutatorElement_eq_one_iff_mul_comm.mp (hu ⟨l,hl⟩)

theorem exceptionalSix_core_fixed_centralizes
    (L : Subgroup G) (hL : IsBlock L) (hm : IsExceptionalAhat6Block L)
    (hrL : primeRank 3 L ≤ 2)
    (H : Subgroup G) (hHL : H ≤ L) (hr : primeRank 3 H = 2)
    (x : G) (hx : x ∈ pCore 2 G)
    (hxc : x ∈ centralizer (pCore 2 G : Set G))
    (hxh : x ∈ centralizer (H : Set G)) : x ∈ centralizer (L : Set G) := by
  let Q := pCore 2 G ⊓ centralizer (pCore 2 G : Set G)
  obtain ⟨u,hu⟩ := exceptionalSix_fixed_correction L hL hm Q
    inf_le_left inf_le_right ⟨x,hx,hxc⟩
  let c : G := (u : G)⁻¹ * x
  have hch : c ∈ centralizer (H : Set G) := centralizer_le hHL hu
  have huh : (u : G) ∈ centralizer (H : Set G) := by
    have h := (centralizer (H : Set G)).mul_mem hxh
      ((centralizer (H : Set G)).inv_mem hch)
    simpa only [c,mul_inv_rev,inv_inv,mul_inv_cancel_left] using h
  obtain ⟨v,hv,hvU⟩ := u.property
  change (v : G) = (u : G) at hvU
  let w : blockU L := ⟨v,hv⟩
  have hw : (w : L) ∈ centralizer (H.subgroupOf L : Set L) := by
    intro y hy
    apply Subtype.ext
    change (y : G) * (v : G) = (v : G) * (y : G)
    rw [hvU]
    exact huh y hy
  have hrH : primeRank 3 (H.subgroupOf L) = 2 := by
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hHL),hr]
  have hw1 := exceptionalSix_fixed_vector_eq_one hm hrL (H.subgroupOf L) hrH w hw
  have hu1 : (u : G) = 1 := by
    rw [←hvU]
    exact congrArg (fun w : blockU L => ((w : L) : G)) hw1
  simpa only [hu1,inv_one,one_mul] using hu

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G]

/-- The second choice is incompatible with an exceptional Â₆ block: cubic
correction makes the original marked fixed plane centralize the block. -/
theorem source_15_3_21_exceptionalSix_secondChoice
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (htwo : OutsideStructure.RankTwoCase d I) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hm : IsExceptionalAhat6Block c.L)
    (hsecond : OutsideStructure.SecondChoice d) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hYL := source_15_3_17_exceptionalSix_containment hG d hempty hM hu hmany hI c hm
  have hrank := OutsideStructure.rankTwoCase_three_rank hG d hI htwo
  have hinput := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hVW := RankTwoElimination.OriginalSource.component_seed_le_starV
    d hinput htwo.2.2.2.2.1
  let J := c.L ⊔ d.R
  let K := c.L.subgroupOf J
  let H := d.Yplus.subgroupOf J
  let V := d.V.subgroupOf J
  have hLJ : c.L ≤ J := le_sup_left
  have hYJ : d.Yplus ≤ J := hYL.trans hLJ
  have hVJ : d.V ≤ J := hVW.trans (map_subtype_le _)
  let hnormal : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le c.L.le_normalizer hinput.normalizes)
  have hmK : IsExceptionalAhat6Block K := exceptionalSix_of_equiv
    (subgroupOfEquivOfLe hLJ).symm hm
  have hbK : IsBlock K := ⟨inferInstance,hmK.1,hnormal.isSubnormal⟩
  have hHK : H ≤ K := comap_mono hYL
  have hrH : primeRank 3 H = 2 := by
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hYJ),hrank]
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hrK : primeRank 3 K ≤ 2 := by
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hLJ)]
    exact (_root_.primeRank_le_of_injective 3 (inclusion (component_le c))
      (inclusion_injective _)).trans hrI
  have hVstar : V ≤ starV c.L d.R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hVW hx
    exact (show y = x from Subtype.ext he) ▸ hy
  have hVcore : V ≤ pCore 2 J := hVstar.trans (map_subtype_le _)
  have hVC : V ≤ centralizer (pCore 2 J : Set J) :=
    hVstar.trans (le_centralizer_iff.mp (core_le_starKernel c.L d.R))
  have hYC : d.Yplus ≤ centralizer (d.V₁ : Set G) := by
    rw [hsecond.2]
    exact (map_subtype_le _).trans inf_le_right
  have hplane : d.V₁ ≤ centralizer (c.L : Set G) := by
    intro x hx
    have hxV : x ∈ d.V := d.action.plane_le 1 hx
    let xJ : J := ⟨x,hVJ hxV⟩
    have hxJ : xJ ∈ V := hxV
    have hxcH : xJ ∈ centralizer (H : Set J) := by
      intro y hy
      apply Subtype.ext
      exact (hYC hy x hx).symm
    have hc := exceptionalSix_core_fixed_centralizes K hbK hmK hrK H hHK hrH
      xJ (hVcore hxJ) (hVC hxJ) hxcH
    intro l hl
    exact congrArg Subtype.val (hc ⟨l,hLJ hl⟩ hl)
  have hLN : c.L ≤ normalizer (d.V₁ : Set G) :=
    (le_centralizer_iff.mp hplane).trans (Subgroup.centralizer_le_normalizer _)
  exact c.outside (hLN.trans (h11.second_choice hsecond).2.1)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
