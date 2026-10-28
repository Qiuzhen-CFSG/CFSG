module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.ExceptionalSixGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.RankTwoRank
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The cubic center is fixed by the original two-radical action

In the rank-two outside case, the image of `Yplus` in `L/O₂(L)` has
three-rank two. The ambient strongly quasithin bound gives three-rank at
most two for this quotient, so its cubic center lies in that image. If an
element of the actual two-radical `R` moves a lift in `Yplus`, the difference
lies in `R` and still maps into the cubic center. The image of `R` is a
two-group, hence has trivial intersection with this three-group. This proves
pointwise fixation of the actual cubic center without asserting that `R`
fixes the entire image of `Yplus`. Inner conjugation by `L` fixes this center
as well, so the fixed-center subgroup contains the entire join `L ⊔ R`.

The source consumer obtains `R ≤ N(L)` from the selected original local
input. The additional premises `Yplus ≤ L` and a cubic core center are
retained explicitly for the component-specific assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.21,
printed p.1127.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
variable {G : Type*} [Group G] [Finite G]

/-- The actual cubic center is contained in the image of `Yplus` in the
component core quotient. -/
theorem source_rankTwo_cubic_center_le_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3) :
    center (c.L ⧸ pCore 2 c.L) ≤
      (d.Yplus.subgroupOf c.L).map (QuotientGroup.mk' (pCore 2 c.L)) := by
  let q := QuotientGroup.mk' (pCore 2 c.L)
  have hk : IsPGroup 2 q.ker := by
    rw [show q = QuotientGroup.mk' (pCore 2 c.L) from rfl, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hrB : primeRank 3 ((d.Yplus.subgroupOf c.L).map q) = 2 := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hk,
      primeRank_congr 3 (subgroupOfEquivOfLe hYL)]
    exact OutsideStructure.rankTwoCase_three_rank hG d hI htwo
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hrL : primeRank 3 c.L ≤ 2 :=
    (_root_.primeRank_le_of_injective 3 (inclusion (component_le c))
      (inclusion_injective _)).trans hrI
  have hrQ : primeRank 3 (c.L ⧸ pCore 2 c.L) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact hrL
  exact cubic_center_le_of_rank_two _ hrB.ge hrQ hc

/-- Every actual element of `R` fixes the cubic center in the core quotient.
The element is kept in the actual normalizer of `L`, so this is the literal
conjugation action used by source consumers. -/
theorem source_rankTwo_radical_fixes_core_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3)
    (r : normalizer (c.L : Set G)) (hr : (r : G) ∈ d.R)
    (z : c.L ⧸ pCore 2 c.L) (hz : z ∈ center (c.L ⧸ pCore 2 c.L)) :
    quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom r) z = z := by
  let q := QuotientGroup.mk' (pCore 2 c.L)
  let a := c.L.normalizerMonoidHom r
  let b := quotientAut (pCore 2 c.L) a
  obtain ⟨y, hy, hyz⟩ := source_rankTwo_cubic_center_le_image hG d hI htwo c hYL hc hz
  change q y = z at hyz
  have hYR : d.Yplus ≤ normalizer (d.R : Set G) :=
    le_sup_left.trans ((d.Yplus ⊔ d.S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (d.Yplus ⊔ d.S) (pCore 2 _)))
  let t : c.L := a y * y⁻¹
  have htR : t ∈ d.R.subgroupOf c.L := by
    change ⁅(r : G), (y : G)⁆ ∈ d.R
    exact le_normalizer_iff_commutator_le_left.mp hYR (commutator_mem_commutator hr hy)
  have hqt : q t = b z * z⁻¹ := by
    change q (a y * y⁻¹) = b z * z⁻¹
    rw [map_mul, map_inv]
    rw [← quotientAut_apply_mk, hyz]
  have hcenter : q t ∈ center (c.L ⧸ pCore 2 c.L) := by
    rw [hqt]
    exact (center _).mul_mem (centerCongr b ⟨z, hz⟩).property ((center _).inv_mem hz)
  have htwoImage : IsPGroup 2 ((d.R.subgroupOf c.L).map q) :=
    ((isPGroup_pCoreIn 2 (d.Yplus ⊔ d.S)).comap_subtype).map q
  have hthreeCenter : IsPGroup 3 (center (c.L ⧸ pCore 2 c.L)) :=
    IsPGroup.of_card (n := 1) (by simpa using hc)
  have hdis := htwoImage.disjoint_of_coprime hthreeCenter (by decide)
  have he : q t = 1 := disjoint_def.mp hdis ⟨t, htR, rfl⟩ hcenter
  rw [hqt, mul_inv_eq_one] at he
  exact he

/-- Every element of the actual join `L ⊔ R` fixes the cubic core center,
since both generating subgroups act trivially on it. -/
theorem source_rankTwo_join_fixes_core_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (r : normalizer (c.L : Set G)) (hr : (r : G) ∈ c.L ⊔ d.R)
    (z : c.L ⧸ pCore 2 c.L) (hz : z ∈ center (c.L ⧸ pCore 2 c.L)) :
    quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom r) z = z := by
  let N := normalizer (c.L : Set G)
  let q := QuotientGroup.mk' (pCore 2 c.L)
  let a := (quotientAut (pCore 2 c.L)).comp c.L.normalizerMonoidHom
  let F : Subgroup N :=
    { carrier := {r | ∀ z, z ∈ center (c.L ⧸ pCore 2 c.L) → a r z = z}
      one_mem' := by intro z hz; simp
      mul_mem' := by
        intro r s hr hs z hz
        rw [map_mul, MulAut.mul_apply, hs z hz, hr z hz]
      inv_mem' := by
        intro r hr z hz
        rw [map_inv]
        exact (show (a r).symm z = z by
          simpa only [MulEquiv.symm_apply_apply] using (congrArg (a r).symm (hr z hz)).symm) }
  have hL : c.L ≤ F.map N.subtype := by
    intro x hx
    let r : N := ⟨x, c.L.le_normalizer hx⟩
    refine ⟨r, ?_, rfl⟩
    intro z hz
    change quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom r) z = z
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (pCore 2 c.L) z
    rw [← hy, quotientAut_apply_mk]
    have ha : c.L.normalizerMonoidHom r y = (⟨x, hx⟩ : c.L) * y * (⟨x, hx⟩ : c.L)⁻¹ := by
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [ha, map_mul, map_mul, map_inv, hy, mem_center_iff.mp hz]
    simp
  have hRad : d.R ≤ F.map N.subtype := by
    intro x hx
    let r : N := ⟨x, hR hx⟩
    refine ⟨r, ?_, rfl⟩
    intro z hz
    exact source_rankTwo_radical_fixes_core_center hG d hI htwo c hYL hc r hx z hz
  obtain ⟨s, hs, hsr⟩ := (sup_le hL hRad) hr
  have he : s = r := Subtype.ext hsr
  subst s
  exact hs z hz


/-- Literal original-input consumer: the selected local setup supplies the
normalization of `L` by `R`, leaving only the component-specific cubic data. -/
theorem source_rankTwo_core_center_action_consumer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hYL : d.Yplus ≤ c.L) (hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3) :
    ∃ hn : d.R ≤ normalizer (c.L : Set G),
      ∀ (r : d.R) (z : c.L ⧸ pCore 2 c.L), z ∈ center (c.L ⧸ pCore 2 c.L) →
        quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom (inclusion hn r)) z = z := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  refine ⟨h.normalizes, ?_⟩
  intro r z hz
  exact source_rankTwo_radical_fixes_core_center hG d hI htwo c hYL hc
    (inclusion h.normalizes r) r.property z hz

/-- The original selected input supplies normalization for the full `L ⊔ R`
action, and this literal action fixes the cubic center pointwise. -/
theorem source_rankTwo_join_center_action_consumer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hYL : d.Yplus ≤ c.L) (hc : Nat.card (center (c.L ⧸ pCore 2 c.L)) = 3) :
    ∃ hn : c.L ⊔ d.R ≤ normalizer (c.L : Set G),
      ∀ (r : (c.L ⊔ d.R : Subgroup G)) (z : c.L ⧸ pCore 2 c.L), z ∈ center (c.L ⧸ pCore 2 c.L) →
        quotientAut (pCore 2 c.L) (c.L.normalizerMonoidHom (inclusion hn r)) z = z := by
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hn := sup_le c.L.le_normalizer h.normalizes
  refine ⟨hn,?_⟩
  intro r z hz
  exact source_rankTwo_join_fixes_core_center hG d hI htwo c hYL hc h.normalizes
    (inclusion hn r) r.property z hz

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
