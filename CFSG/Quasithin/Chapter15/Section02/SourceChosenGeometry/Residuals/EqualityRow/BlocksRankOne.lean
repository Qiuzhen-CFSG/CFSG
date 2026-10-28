module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.BlocksGeometry
public import Theory.GroupTheory.PrimeRankNormalIntersection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicOrbit
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Theory.GroupTheory.PrimeRankWitness
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ChiSieve

/-!
# The literal rank-one chi-block cases in the equality row

The cubic rank-two wreath residual meets each chi-block in a nontrivial
odd subgroup. In an L₂ block its actual natural action makes the original
plane centralize the block, contradicting equality-row cubic escape. An
A₃ block and its two-core centralize the plane; its normal A₄ or A₄×A₄
Sylow orbit cannot centralize the Sylow omega center. Both singleton and
paired block orbits retain their original embeddings.

Source: Aschbacher--Smith, preliminary 15.2.23, printed p.1115,
refs/quasithin.pdf. No partner residual identity is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem chi_normalized_by_twoPerfect
    (hf : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    {X : Subgroup G} (hX : ChapterC.IsChiBlockIn X)
    (K : Subgroup G) (hp : IsPPerfect 2 K) : K ≤ normalizer (X : Set G) := by
  rcases ChapterC.RankOne.ChiProduct.normal_or_index_two hf hr hX with hn | hi
  · let := hn
    rw [normalizer_eq_top]
    exact le_top
  · let N := normalizer (X : Set G)
    let : N.Normal := N.normal_of_index_eq_two hi
    have hquot : IsPGroup 2 (G ⧸ N) := IsPGroup.of_card (n := 1) (by
      simpa only [← index_eq_card,pow_one] using hi)
    exact (le_pResidual_of_isPPerfect K hp).trans (sInf_le ⟨inferInstance,hquot⟩)

private theorem odd_intersection_of_chi
    (hf : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    {X : Subgroup G} (hX : ChapterC.IsChiBlockIn X)
    (K : Subgroup G) (hp : IsPPerfect 2 K) (hk : 2 ≤ primeRank 3 K) :
    ∃ D : Subgroup G, D ≤ X ∧ D ≤ K ∧ Odd (Nat.card D) ∧ D ≠ ⊥ := by
  have hn := chi_normalized_by_twoPerfect hf hr hX K hp
  have hkr : primeRank 3 K = 2 := by
    have hh := (primeRank_subgroup_le 3 K).trans hr
    omega
  obtain ⟨E,hE,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hE
  let E' := E.map K.subtype
  let : IsElementaryAbelian 3 E' := IsElementaryAbelian.map_subtype
  have hc : Nat.card E' = 3^2 := by
    rw [card_map_of_injective K.subtype_injective,hcard,hkr]
  let D := E' ⊓ X
  have hd : D ≠ ⊥ := E'.inf_ne_bot_of_elementary_plane X ((map_subtype_le _).trans hn)
    (ChapterC.RankOne.ChiProduct.three_dvd_card_of_chi hX.2) hc hr
  have hodd : Odd (Nat.card D) := by
    obtain ⟨n,he⟩ := ((IsElementaryAbelian.isPGroup 3 E').to_le
      (show D ≤ E' from inf_le_left)).exists_card_eq
    rw [he]
    exact (by decide : Odd 3).pow
  exact ⟨D,inf_le_right,inf_le_left.trans (map_subtype_le _),hodd,hd⟩

private theorem a3_core_sup_odd_eq_top {A : Type*} [Group A] [Finite A]
    (ha : ChapterC.IsAlternatingBlock A 3) (D : Subgroup A)
    (ho : Odd (Nat.card D)) (hd : D ≠ ⊥) : pCore 2 A ⊔ D = ⊤ := by
  have hi : (pCore 2 A).index = 3 := by
    rw [index_eq_card]
    obtain ⟨e⟩ := ha.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hnot : ¬ D ≤ pCore 2 A := by
    intro hle
    obtain ⟨n,he⟩ := (pCore_isPGroup.to_le hle).exists_card_eq
    have hn : n = 0 := by
      by_contra hn
      exact ho.not_two_dvd_nat (he ▸ dvd_pow_self 2 hn)
    exact hd (card_eq_one.mp (by simpa only [hn,pow_zero] using he))
  exact (isCoatom_of_index_three _ hi).2 _
    (lt_of_le_of_ne le_sup_left (fun he => hnot (le_sup_right.trans_eq he.symm)))

private theorem cubic_orbit_not_centralizing_omega
    (S : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hm : Nonempty (N ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (N ≃* AlternatingFourPair.Model)) :
    ¬ N ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) := by
  have hz : center N = ⊥ := by
    apply card_eq_one.mp
    rcases hm with he | he
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr (centerCongr e).toEquiv,
        alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 4)),card_bot]
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr (centerCongr e).toEquiv,AlternatingFourPair.center_eq_bot,card_bot]
  have hcore : pCore 2 N ≠ ⊥ := by
    intro he
    have hh := card_eq_one.mpr he
    rcases hm with he | he
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr (e.subgroupMap (pCore 2 N)).toEquiv] at hh
      change Nat.card ((pCore 2 N).map e.toMonoidHom) = 1 at hh
      rw [pCore_map_iso,
        AlternatingFourPair.twoCore_eq_kleinFour,
        alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)] at hh
      omega
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr (e.subgroupMap (pCore 2 N)).toEquiv] at hh
      change Nat.card ((pCore 2 N).map e.toMonoidHom) = 1 at hh
      rw [pCore_map_iso,
        AlternatingFourPair.card_twoCore] at hh
      omega
  let Q := N.pCoreIn 2
  let : Q.Normal := inferInstanceAs ((pCore 2 N).map N.subtype).Normal
  have hQ : Q ≠ ⊥ := by
    intro he
    exact hcore ((map_eq_bot_iff_of_injective _ N.subtype_injective).mp he)
  have hQS : Q ≤ (S : Subgroup G) := (isPGroup_pCoreIn 2 N).le_sylow_of_normal S
  have hne := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup Q (S : Subgroup G)
    hQS S.isPGroup' (by rw [normalizer_eq_top]; exact le_top) hQ
  intro hc
  apply hne
  apply bot_unique
  intro x hx
  have hn : x ∈ N := (pCoreIn_le 2 N) hx.1
  have hc' : x ∈ centralizer (N : Set G) :=
    le_centralizer_iff.mp hc hx.2
  have hh : (⟨x,hn⟩ : N) ∈ center N :=
    mem_center_iff.mpr (fun n => Subtype.ext (hc' n n.property))
  rw [hz,mem_bot] at hh
  exact mem_bot.mpr (congrArg N.subtype hh)

variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
include r

/-- The rank intersection constructs an odd subgroup in the original K and X. -/
theorem chi_block_odd_intersection
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsChiBlockIn X) :
    ∃ D : Subgroup I, D ≤ X ∧ Odd (Nat.card D) ∧ D ≠ ⊥ ∧
      D.map I.subtype ≤ (pResidual 2 H).map H.subtype := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I := le_sup_left.trans ((r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right)
  let K' := K.subgroupOf I
  let e : (pResidual 2 H) ≃* K' :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (subgroupOfEquivOfLe hKI).symm
  have hp : IsPPerfect 2 K' := (isPPerfect_pResidual 2 (G := H)).of_surjective
    e.toMonoidHom e.surjective
  have hr : 2 ≤ primeRank 3 K' := by
    rw [← primeRank_congr 3 e]
    exact r.residual_threeRank_ge_two
  have hIr := (Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
    3 (by decide) (by decide)
  obtain ⟨D,hDX,hDK,ho,hd⟩ := odd_intersection_of_chi hfit hIr hX K' hp hr
  refine ⟨D,hDX,ho,hd,?_⟩
  exact (map_mono hDK).trans_eq (map_subgroupOf_eq_of_le hKI)

theorem l2_block_le_partner_of_odd_fixed
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I)
    (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    {n : ℕ} (hn : ChapterC.IsL2EvenBlock X n)
    (D : Subgroup I) (hDX : D ≤ X)
    (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥)
    (hDK : D ≤ ((pResidual 2 H).map H.subtype).subgroupOf I) :
    X.map I.subtype ≤ Mc := by
  obtain ⟨R,hR⟩ := r.sylow_in_escape_for_blocks hI
  have hZI : (⁅V,B⁆ : Subgroup G) ≤ I := r.plane_le_escape_for_blocks hI
  have hZX : (⁅V,B⁆ : Subgroup G) ≤ centralizer (X.map I.subtype : Set G) := by
    intro z hz
    have hzS := (mem_omegaOneCenterAmbient_iff _ _).mp (r.plane_omega_for_blocks ▸ hz)
    have hzR : (⟨z,hZI hz⟩ : I) ∈ centralizer (R : Set I) := by
      intro r hr
      exact Subtype.ext (hzS.2.2 r (hR ▸ mem_map_of_mem I.subtype hr))
    have hzD : (⟨z,hZI hz⟩ : I) ∈ centralizer (D : Set I) := by
      intro a ha
      exact Subtype.ext ((r.residual_centralizes_plane (hDK ha)) z hz).symm
    have hzX := hn.centralizes_of_sylow_and_odd_fixed R hfit X hX D hDX hodd hD
      ⟨z,hZI hz⟩ (Subtype.ext hzS.2.1) hzR hzD
    rintro x ⟨x,hx,rfl⟩
    exact congrArg I.subtype (hzX x hx)
  exact (le_centralizer_iff.mp hZX).trans ((r.plane_centralizer_le_intersection hI).trans inf_le_left)

/-- The actual natural-block action puts X inside the partner centralizer. -/
theorem l2_block_le_partner
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X) {n : ℕ}
    (hb : ChapterC.IsL2EvenBlock X n) : X.map I.subtype ≤ Mc := by
  obtain ⟨D,hDX,ho,hd,hDK⟩ := r.chi_block_odd_intersection hI hfit ⟨hX,Or.inl ⟨n,hb⟩⟩
  exact r.l2_block_le_partner_of_odd_fixed hI hfit hX hb D hDX ho hd (fun x hx => hDK (mem_map_of_mem I.subtype hx))

/-- An A₃ block contradicts the original Sylow omega-center, also for paired orbits. -/
theorem a3_block_false
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 3) : False := by
  obtain ⟨D,hDX,ho,hd,hDK⟩ := r.chi_block_odd_intersection hI hfit
    ⟨hX,Or.inr ⟨3,by decide,hb⟩⟩
  obtain ⟨R,hR⟩ := r.sylow_in_escape_for_blocks hI
  have hZI : (⁅V,B⁆ : Subgroup G) ≤ I := r.plane_le_escape_for_blocks hI
  let W := (⁅V,B⁆ : Subgroup G).subgroupOf I
  have hW : W = omegaOneCenterAmbient (R : Subgroup I) := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hZI,← omegaOneCenterAmbient_map_injective _ I.subtype_injective,
      hR,← r.plane_omega_for_blocks]
  have hZX : W ≤ centralizer (X : Set I) := by
    have ho' : Odd (Nat.card (D.subgroupOf X)) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hDX).toEquiv]
    have hd' : D.subgroupOf X ≠ ⊥ := by
      intro he
      apply hd
      have hh := congrArg (map X.subtype) he
      simpa only [map_subgroupOf_eq_of_le hDX,Subgroup.map_bot] using hh
    have hg := a3_core_sup_odd_eq_top hb (D.subgroupOf X) ho' hd'
    have hgen : X.pCoreIn 2 ⊔ D = X := by
      change (pCore 2 X).map X.subtype ⊔ D = X
      have hh := congrArg (map X.subtype) hg
      simpa only [Subgroup.map_sup,map_subgroupOf_eq_of_le hDX,← MonoidHom.range_eq_map,range_subtype] using hh
    have hQR : X.pCoreIn 2 ≤ (R : Subgroup I) :=
      (pCoreIn_le_of_subnormal 2 hX.subnormal).trans
        (pCore_isPGroup.le_sylow_of_normal R)
    have hWC : W ≤ centralizer (R : Set I) := by
      rw [hW]
      intro w hw r hr
      exact (mem_omegaOneCenterAmbient_iff _ _).mp hw |>.2.2 r hr
    have hWD : W ≤ centralizer (D : Set I) := by
      intro w hw a ha
      exact Subtype.ext ((r.residual_centralizes_plane (hDK (mem_map_of_mem I.subtype ha))) w hw).symm
    intro w hw x hx
    have hc : X ≤ centralizer ({w} : Set I) := by
      rw [←hgen]
      apply sup_le
      · intro q hq
        exact mem_centralizer_singleton_iff.mpr (hWC hw q (hQR hq))
      · intro a ha
        exact mem_centralizer_singleton_iff.mpr (hWD hw a ha)
    exact mem_centralizer_singleton_iff.mp (hc hx)
  let N := conjugateSpanBy X (R : Subgroup I)
  have hIr := (Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
    3 (by decide) (by decide)
  obtain ⟨hn,hm⟩ := ChapterC.RankOne.ChiProduct.cubic_orbit_models hfit hIr R X hX hb
  let : N.Normal := hn
  apply cubic_orbit_not_centralizing_omega R N hm
  rw [←hW]
  apply conjugateSpanBy_le (le_centralizer_iff.mp hZX)
  have hRW : (R : Subgroup I) ≤ centralizer (W : Set I) := by
    rw [hW]
    apply le_centralizer_iff.mp
    intro w hw r hr
    exact (mem_omegaOneCenterAmbient_iff _ _).mp hw |>.2.2 r hr
  exact hRW.trans (centralizer (W : Set I)).le_normalizer

/-- The natural L₂ action and equality-row cubic escape exclude the block. -/
theorem l2_block_false_of_eq (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X) {n : ℕ}
    (hb : ChapterC.IsL2EvenBlock X n) : False :=
  r.l2_block_not_le_partner_of_eq he hb (r.l2_block_le_partner hI hfit hX hb)

/-- The complete required rank-one exclusion leaves precisely A₅ or A₇. -/
theorem chi_block_alternating_five_or_seven_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsChiBlockIn X) :
    ChapterC.IsAlternatingBlock X 5 ∨ ChapterC.IsAlternatingBlock X 7 := by
  have hs := (Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
  rcases ChapterC.LocalC129.chi_zero_or_alternating_seven (hs.subgroup X) hX.2 with hz | h7
  · rcases hz with ⟨n,hb⟩ | h3 | h5
    · exact (r.l2_block_false_of_eq he hI hfit hX.1 hb).elim
    · exact (r.a3_block_false hI hfit hX.1 h3).elim
    · exact Or.inl h5
  · exact Or.inr h7

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
