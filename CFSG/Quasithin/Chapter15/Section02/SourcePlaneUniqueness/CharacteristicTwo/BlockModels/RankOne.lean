module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.Orbits
public import Theory.GroupTheory.PrimeRankNormalIntersection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicOrbit
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankWitness
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ChiSieve

/-!
# The complete rank-one block exclusions in the escaping-plane argument

The original S₃ wreath C₂ quotient of H gives O²(H) three-rank two.
Its image normalizes every chi-block, since their normalizer indices are
at most two. An elementary nine in this image therefore meets the block
nontrivially, supplying the actual odd subgroup D ≤ K ∩ X.

For an A₃ block, its two-core and D generate X and thus centralize ZS.
Its full Sylow orbit is A₄ or A₄ × A₄. The normal two-core of this
centerless orbit meets Ω₁Z(S) nontrivially, a contradiction. For an L₂
block, the natural-module fixed-point theorem gives X ≤ Mc. Its Sylow
orbit is perfect with nontrivial signalizer module and equals its
prime-to-three residual, so the proved normal-perfect preliminary excludes
it. This covers singleton and exchanged two-block orbits without identifying
the solvable span of K ∩ X with the whole block orbit.

The final consumer leaves precisely the actual A₅ and A₇ block types.
The only additional source premise is the earlier Kc orbit alternative,
produced by qt-e-152-plane-geometry / qt-e-152-small-parabolic and discharged
by qt-e-152-plane-characteristic-two. No odd-subgroup, fixed-space or
noncentrality callback remains in these rank-one exclusions.

Source: Aschbacher--Smith, preliminary 15.2.23, printed pp.1114--1115;
C.1.28, printed pp.133--134; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private def cubicPermutation : Multiplicative (ZMod 3) →* Equiv.Perm (Fin 3) where
  toFun a := (Equiv.swap 0 1 * Equiv.swap 1 2) ^ a.toAdd.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem cubicPermutation_injective : Function.Injective cubicPermutation := by decide +kernel

private theorem symmetricThree_wreath_threeRank_ge_two :
    2 ≤ primeRank 3 (RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  let E := Multiplicative (ZMod 2) → Multiplicative (ZMod 3)
  let f : E →* RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)) :=
    { toFun := fun a => ⟨fun i => cubicPermutation (a i),1⟩
      map_one' := by
        apply RegularWreathProduct.ext
        · funext i
          exact cubicPermutation.map_one
        · rfl
      map_mul' := by
        intro a b
        apply RegularWreathProduct.ext
        · funext i
          change cubicPermutation (a i * b i) =
            cubicPermutation (a i) * cubicPermutation (b (1⁻¹ * i))
          simp only [inv_one,one_mul,map_mul]
        · rfl }
  apply primeRank_ge_of_elementary_embedding (p := 3) (e := 2) ?_ ?_ f ?_
  · intro a
    funext i
    exact (show ∀ z : Multiplicative (ZMod 3), z^3=1 by decide +kernel) (a i)
  · norm_num [E,Nat.card_eq_fintype_card]
  · intro a b he
    funext i
    exact cubicPermutation_injective (congrArg (fun z => z.left i) he)

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

namespace PlaneUniquenessPreceding
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The actual S₃ wreath C₂ quotient gives the original residual its cubic plane. -/
theorem residual_threeRank_ge_two : 2 ≤ primeRank 3 (pResidual 2 H) := by
  rw [ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)]
  obtain ⟨e⟩ := d.geometry.quotient
  have hh := primeRank_quotient_le_of_isTwoGroup 3 (by decide : Odd 3)
    (pCore 2 H) pCore_isPGroup
  rw [primeRank_equiv 3 e] at hh
  exact symmetricThree_wreath_threeRank_ge_two.trans hh

/-- The rank intersection constructs an odd subgroup in the original K and X. -/
theorem chi_block_odd_intersection
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsChiBlockIn X) :
    ∃ D : Subgroup I, D ≤ X ∧ Odd (Nat.card D) ∧ D ≠ ⊥ ∧
      D.map I.subtype ≤ (pResidual 2 H).map H.subtype := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I := le_sup_left.trans ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  let K' := K.subgroupOf I
  let e : (pResidual 2 H) ≃* K' :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (subgroupOfEquivOfLe hKI).symm
  have hp : IsPPerfect 2 K' := (isPPerfect_pResidual 2 (G := H)).of_surjective
    e.toMonoidHom e.surjective
  have hr : 2 ≤ primeRank 3 K' := by
    rw [← primeRank_congr 3 e]
    exact d.residual_threeRank_ge_two
  have hIr := (Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
    3 (by decide) (by decide)
  obtain ⟨D,hDX,hDK,ho,hd⟩ := odd_intersection_of_chi hfit hIr hX K' hp hr
  refine ⟨D,hDX,ho,hd,?_⟩
  exact (map_mono hDK).trans_eq (map_subgroupOf_eq_of_le hKI)

/-- The actual natural-block action puts X inside the partner centralizer. -/
theorem l2_block_le_partner
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X) {n : ℕ}
    (hb : ChapterC.IsL2EvenBlock X n) : X.map I.subtype ≤ Mc := by
  obtain ⟨D,hDX,ho,hd,hDK⟩ := d.chi_block_odd_intersection hI hfit ⟨hX,Or.inl ⟨n,hb⟩⟩
  exact d.l2_block_le_partner_of_odd_fixed hI hfit hX hb D hDX ho hd (fun x hx => hDK (mem_map_of_mem I.subtype hx))

/-- An A₃ block contradicts the original Sylow omega-center, also for paired orbits. -/
theorem a3_block_false
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 3) : False := by
  obtain ⟨D,hDX,ho,hd,hDK⟩ := d.chi_block_odd_intersection hI hfit
    ⟨hX,Or.inr ⟨3,by decide,hb⟩⟩
  obtain ⟨R,hR⟩ := d.sylow_in_escape hI
  have hZI : ZS ≤ I := d.plane_le_centralizer.trans
    ((d.centralizer_le_intersection hI).trans inf_le_right)
  let W := ZS.subgroupOf I
  have hW : W = omegaOneCenterAmbient (R : Subgroup I) := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hZI,← omegaOneCenterAmbient_map_injective _ I.subtype_injective,
      hR,← d.omega_center]
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
      exact Subtype.ext ((d.residual_centralizes (hDK (mem_map_of_mem I.subtype ha))) w hw).symm
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

/-- Both singleton and paired L₂ orbits are excluded by the normal-perfect preliminary. -/
theorem l2_block_false
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X) {n : ℕ}
    (hb : ChapterC.IsL2EvenBlock X n) : False := by
  apply d.l2_blockOrbit_not_le_partner horbit hI hfit hX hb
  apply conjugateSpanBy_le (d.l2_block_le_partner hI hfit hX hb)
  exact ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_left).trans
    Mc.le_normalizer

/-- After the complete rank-one exclusion, only the actual A₅ and A₇ actions remain. -/
theorem chi_block_alternating_five_or_seven
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsChiBlockIn X) :
    ChapterC.IsAlternatingBlock X 5 ∨ ChapterC.IsAlternatingBlock X 7 := by
  have hs := (Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
  rcases ChapterC.LocalC129.chi_zero_or_alternating_seven (hs.subgroup X) hX.2 with hz | h7
  · rcases hz with ⟨n,hb⟩ | h3 | h5
    · exact (d.l2_block_false horbit hI hfit hX.1 hb).elim
    · exact (d.a3_block_false hI hfit hX.1 h3).elim
    · exact Or.inl h5
  · exact Or.inr h7

end PlaneUniquenessPreceding
end CFSG.Quasithin.Chapter15.Section02
