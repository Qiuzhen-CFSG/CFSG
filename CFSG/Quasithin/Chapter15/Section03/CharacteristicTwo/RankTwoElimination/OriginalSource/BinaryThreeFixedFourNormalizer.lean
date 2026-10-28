module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeFixedFactorBound
public import Theory.GroupTheory.FourGroupTwoGroupAction
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalDisplacement

/-!
# The full normalizer of the original component-fixed four

The actual four F is normalized by Yplus S and centralized by L. Its full
normalizer is therefore in the same original outside family, with the same
Sylow S. The residual Y_C has no fixed point on F and is two-perfect; the
S-action is nontrivial. These two actions force the normalizer to induce
all six automorphisms of F. In particular its full pointwise centralizer
has index six, and all three nonidentity points of F fuse in that normalizer.

This retains the original component and outside family. It does not assert
that the four-normalizer has characteristic two, or that the original S
centralizes F. Source: Aschbacher--Smith15.3.6,15.3.11--12,15.3.23,
pp.1122--1129.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.CoreActions LinearThree.Extension.SourceCases
open LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem full_four_action (F S Y : Subgroup G) [IsKleinFour F]
    (hS : IsPGroup 2 S) (hSN : S ≤ normalizer (F : Set G))
    (hSmove : ¬ S ≤ centralizer (F : Set G))
    (hY : IsPPerfect 2 Y) (hYN : Y ≤ normalizer (F : Set G))
    (hYmove : ¬ Y ≤ centralizer (F : Set G)) :
    Function.Surjective F.normalizerMonoidHom := by
  let f := F.normalizerMonoidHom
  let s := f.comp (inclusion hSN)
  have hsne : s.range ≠ ⊥ := by
    intro hz
    apply hSmove
    intro x hx
    have hh : s ⟨x,hx⟩ = 1 := hz.le ⟨⟨x,hx⟩,rfl⟩
    have hk : inclusion hSN ⟨x,hx⟩ ∈ f.ker := hh
    rwa [normalizerMonoidHom_ker] at hk
  have hscard : Nat.card s.range = 2 := by
    have hle := four_twoGroup_action_card F S hS hSN
    have hpos : 0 < Nat.card s.range := Nat.card_pos
    have hne : Nat.card s.range ≠ 1 := fun hc => hsne (card_eq_one.mp hc)
    change Nat.card s.range ≤ 2 at hle
    omega
  have hsle : s.range ≤ f.range := by
    rintro a ⟨x,rfl⟩
    exact ⟨inclusion hSN x,rfl⟩
  have htwo : 2 ∣ Nat.card f.range := hscard ▸ card_dvd_of_le hsle
  have hdiv : Nat.card f.range ∣ 6 := by
    rw [←IsKleinFour.card_mulAut F]
    exact f.range.card_subgroup_dvd_card
  have hcard : Nat.card f.range = 6 := by
    have hbound := Nat.le_of_dvd (by decide : 0 < 6) hdiv
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    have hne2 : Nat.card f.range ≠ 2 := by
      intro hc
      have hp : IsPGroup 2 f.range := IsPGroup.of_card (n := 1) (by simpa using hc)
      let y : Y →* f.range := f.rangeRestrict.comp (inclusion hYN)
      have hy := hY.hom_eq_one_of_isPGroup hp y
      apply hYmove
      intro a ha
      have hh' := DFunLike.congr_fun hy ⟨a,ha⟩
      have hh : f (inclusion hYN ⟨a,ha⟩) = 1 := by
        simpa only [y,MonoidHom.comp_apply,MonoidHom.coe_rangeRestrict,
          MonoidHom.one_apply,OneMemClass.coe_one] using congrArg Subtype.val hh'
      have hk : inclusion hYN ⟨a,ha⟩ ∈ f.ker := hh
      rwa [normalizerMonoidHom_ker] at hk
    have hne4 : Nat.card f.range ≠ 4 := by
      intro hc
      rw [hc] at hdiv
      norm_num at hdiv
    omega
  have htop : f.range = ⊤ := eq_of_le_of_card_ge le_top (by
    rw [card_top,IsKleinFour.card_mulAut F,hcard])
  exact MonoidHom.range_eq_top.mp htop

/-- The original whole fixed four has a full six-element automizer, inside
an actual member of the same outside family with the original Sylow S. -/
theorem binary_three_large_distance_fixed_four_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical) :
    let F := coreFixed c.L
    let N := normalizer (F : Set G)
    N ∈ d.Hplus ∧ IsSQTK KnownSimple.IsKnownSimple N ∧
      (∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype = d.S) ∧
      Function.Surjective F.normalizerMonoidHom ∧
      (centralizer (F : Set G)).relIndex N = 6 ∧
      N.pCoreIn 2 ≤ centralizer (F : Set G) ∧
      N.pCoreIn 2 < (c.L ⊔ d.S).pCoreIn 2 ∧
      ∀ u ∈ F, u ≠ 1 → ∀ v ∈ F, v ≠ 1 →
        ∃ n ∈ N, n * u * n⁻¹ = v := by
  classical
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨hcard,heq,_,_⟩ := binary_three_large_distance_fixed_factor_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  let F := coreFixed c.L
  let N := normalizer (F : Set G)
  let := coreFixed_elementary_of_MS93 d c.L b t common earlier
  let : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by change 1 < Nat.card (coreFixed c.L); omega)
  let : IsKleinFour F := ⟨hcard,IsElementaryAbelian.exponent_eq_prime⟩
  have hFN : IsTwoLocal N := ⟨F,(nontrivial_iff_ne_bot _).mp inferInstance,
    IsElementaryAbelian.isPGroup 2 _,rfl⟩
  have hYSN : d.Yplus ⊔ d.S ≤ N :=
    (sup_le h.normalizes_component hg.component_normalized).trans
      (FixedFour.coreFixed_normalized c.L)
  have hLN : c.L ≤ N := c.L.le_normalizer.trans (FixedFour.coreFixed_normalized c.L)
  have hNF : N ∈ d.Hplus :=
    ⟨⟨Chapter1.mem_H_of_isTwoLocal hFN,hYSN⟩,fun hn => c.outside (hLN.trans hn)⟩
  have hSmove : ¬ d.S ≤ centralizer (F : Set G) := by
    intro hs
    have hh : F ⊓ centralizer (d.S : Set G) = F :=
      inf_eq_left.mpr (le_centralizer_iff.mp hs)
    have ht := (coreFixed_original_sylow_fixed_line d c.L eSL h hg b t common earlier).2
    change Nat.card (F ⊓ centralizer (d.S : Set G) : Subgroup G) = 2 at ht
    rw [hh] at ht
    change Nat.card (coreFixed c.L) = 2 at ht
    omega
  have hYmove : ¬ YC d c.L ≤ centralizer (F : Set G) := by
    intro hy
    have hh : F ⊓ centralizer (YC d c.L : Set G) = F :=
      inf_eq_left.mpr (le_centralizer_iff.mp hy)
    have hz := coreFixed_opposite_residual_fixed_eq_bot d c.L eSL h hg b t common earlier
    rw [hh] at hz
    exact ((nontrivial_iff_ne_bot F).mp inferInstance) hz
  have hsurj := full_four_action F d.S (YC d c.L)
    (d.T.isPGroup'.to_le inf_le_left) (le_sup_right.trans hYSN) hSmove
    (ComponentIntersection.centralizerResidual_isPPerfect _ _)
    ((((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_left).trans le_sup_left).trans hYSN)
    hYmove
  have hSyl := (OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany N hNF).sylow
  have hfix : N.pCoreIn 2 ≤ centralizer (F : Set G) := by
    have hk := IsKleinFour.twoCore_le_ker_of_surjective F F.normalizerMonoidHom hsurj
    rw [normalizerMonoidHom_ker] at hk
    rintro x ⟨y,hy,rfl⟩
    exact hk hy
  have hcorele : N.pCoreIn 2 ≤ (c.L ⊔ d.S).pCoreIn 2 := by
    obtain ⟨P,hP⟩ := hSyl
    have hNS : N.pCoreIn 2 ≤ d.S := hP ▸ pCoreIn_le_sylow N P
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 N) (hNS.trans le_sup_right)
      ((sup_le hLN (le_sup_right.trans hYSN)).trans (N.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image N (pCore 2 N))))
  have hstrict : N.pCoreIn 2 < (c.L ⊔ d.S).pCoreIn 2 := by
    apply lt_of_le_of_ne hcorele
    intro hh
    have hzero : ⁅F,(c.L ⊔ d.S).pCoreIn 2⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (hh ▸ hfix)
    have htwo := (binary_three_source_original_displacement_eq_fixedLine
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier).2
    rw [←heq] at htwo
    rw [hzero,card_bot] at htwo
    omega
  refine ⟨hNF,hG.twoLocal_sqtk hFN,hSyl,hsurj,?_,hfix,hstrict,?_⟩
  · change ((centralizer (F : Set G)).subgroupOf N).index = 6
    rw [←F.normalizerMonoidHom_ker,index_ker,
      MonoidHom.range_eq_top.mpr hsurj,card_top,IsKleinFour.card_mulAut]
  · intro u huF hu1 v hvF hv1
    let u' : F := ⟨u,huF⟩
    let v' : F := ⟨v,hvF⟩
    have hu' : u' ≠ 1 := fun hh => hu1 (congrArg Subtype.val hh)
    have hv' : v' ≠ 1 := fun hh => hv1 (congrArg Subtype.val hh)
    let a : MulAut F := IsKleinFour.mulEquiv (Equiv.swap u' v') (by
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hu') (Ne.symm hv'))
    obtain ⟨n,hn⟩ := hsurj a
    refine ⟨n,n.property,?_⟩
    have he := congrArg (fun f : MulAut F => (f u' : G)) hn
    change (n : G) * u * (n : G)⁻¹ = ((Equiv.swap u' v') u' : F) at he
    simpa only [Equiv.swap_apply_left] using he

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
