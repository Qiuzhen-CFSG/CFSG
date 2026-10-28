module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointOriginalMarkedParabolic
public import Theory.GroupAction.ElementaryFiveMarkedParabolic

/-!
# Intermediate original subgroups induce the full marked 2+3 parabolic

The image of the original core Q is the full radical at the original H.
The original component supplies a nontrivial perfect subgroup, while the original Sylow subgroup and opposite residual induce all
automorphisms of H inside any intermediate subgroup containing them. These
recognize its literal image on U as the full stabilizer of the same marked H.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.CoreActions LinearThree.Extension.SourceCases
open LinearThree.OriginalSource ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem full_four_action_in_intermediate (F S Y I : Subgroup G) [IsKleinFour F]
    (hS : IsPGroup 2 S) (hSN : S ≤ normalizer (F : Set G))
    (hSmove : ¬ S ≤ centralizer (F : Set G))
    (hY : IsPPerfect 2 Y) (hYN : Y ≤ normalizer (F : Set G))
    (hYmove : ¬ Y ≤ centralizer (F : Set G))
    (hSI : S ≤ I) (hYI : Y ≤ I) (hIF : I ≤ normalizer (F : Set G)) :
    Function.Surjective (F.normalizerMonoidHom.comp (inclusion hIF)) := by
  let f := F.normalizerMonoidHom.comp (inclusion hIF)
  let s := f.comp (inclusion hSI)
  have hsne : s.range ≠ ⊥ := by
    intro hz
    apply hSmove
    intro x hx
    have hh : s ⟨x,hx⟩ = 1 := hz.le ⟨⟨x,hx⟩,rfl⟩
    have hk : inclusion hSN ⟨x,hx⟩ ∈ F.normalizerMonoidHom.ker := hh
    rwa [normalizerMonoidHom_ker] at hk
  have hscard : Nat.card s.range = 2 := by
    have hle := four_twoGroup_action_card F S hS hSN
    have hpos : 0 < Nat.card s.range := Nat.card_pos
    have hne : Nat.card s.range ≠ 1 := fun hc => hsne (card_eq_one.mp hc)
    change Nat.card s.range ≤ 2 at hle
    omega
  have hsle : s.range ≤ f.range := by
    rintro a ⟨x,rfl⟩
    exact ⟨inclusion hSI x,rfl⟩
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
      let y : Y →* f.range := f.rangeRestrict.comp (inclusion hYI)
      have hy := hY.hom_eq_one_of_isPGroup hp y
      apply hYmove
      intro a ha
      have hh' := DFunLike.congr_fun hy ⟨a,ha⟩
      have hh : f (inclusion hYI ⟨a,ha⟩) = 1 := by
        simpa only [y,MonoidHom.comp_apply,MonoidHom.coe_rangeRestrict,
          MonoidHom.one_apply,OneMemClass.coe_one] using congrArg Subtype.val hh'
      have hk : inclusion hYN ⟨a,ha⟩ ∈ F.normalizerMonoidHom.ker := hh
      rwa [normalizerMonoidHom_ker] at hk
    have hne4 : Nat.card f.range ≠ 4 := by
      intro hc
      rw [hc] at hdiv
      norm_num at hdiv
    omega
  have htop : f.range = ⊤ := eq_of_le_of_card_ge le_top (by
    rw [card_top,IsKleinFour.card_mulAut F,hcard])
  exact MonoidHom.range_eq_top.mp htop

/-- Every original intermediate subgroup containing L, Yplus and S induces
the full stabilizer of the unchanged marked H on the unchanged U. -/
theorem binary_three_source_intermediate_marked_parabolic
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
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G)))
    (hK : K.IsCComponent) (hKn : K.Normal)
    (hLK : c.L.subgroupOf (centralizer ({z} : Set G)) ≤ K)
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))]
    (eB : (((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) ⧸
      pCore 2 ((c.L.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) ≃* PSL(3,ZMod 2))
    (hrX : primeRank 3 (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))) = 2)
    (hrB : primeRank 3 (normalizer ((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) ≤ 1)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) 4 2)
    (T : Subgroup G) (hTI : T ≤ I) (hLT : c.L ≤ T)
    (hYT : d.Yplus ≤ T) (hST : d.S ≤ T) :
    let H := intrinsicFour c.L
    let U := conjugateSpanBy H (centralizer ({z} : Set G))
    ∃ hTU : T ≤ normalizer (U : Set G),
      T ≤ normalizer (H : Set G) ∧
      ∀ f : MulAut U,
        f ∈ (U.normalizerMonoidHom.comp (inclusion hTU)).range ↔
          ∀ x : U, (f x : G) ∈ H ↔ (x : G) ∈ H := by
  let H := intrinsicFour c.L
  let U := conjugateSpanBy H (centralizer ({z} : Set G))
  let Q := LinearThree.commutatorCore c.L
  obtain ⟨hIU,hIH,hQU,_,hQcard,_,hQrad,_⟩ :=
    binary_three_source_fixed_span_marked_radical
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  have hTU : T ≤ normalizer (U : Set G) := hTI.trans hIU
  have hTH : T ≤ normalizer (H : Set G) := hTI.trans hIH
  have hHsurj : Function.Surjective (H.normalizerMonoidHom.comp (inclusion hTH)) := by
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
    have hFH : coreFixed c.L = H := heq
    have hHcard : Nat.card H = 4 := by rw [←hFH]; exact hcard
    let : IsElementaryAbelian 2 H := (intrinsicFour_properties_of_MS93 d c.L b t common earlier).1
    let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hHcard]; decide)
    let : IsKleinFour H := ⟨hHcard,IsElementaryAbelian.exponent_eq_prime⟩
    have hYCT : YC d c.L ≤ T := ((ComponentIntersection.centralizerResidual_le _ _).trans
      inf_le_left).trans hYT
    have hSmove : ¬ d.S ≤ centralizer (H : Set G) := by
      intro hs
      have hh : H ⊓ centralizer (d.S : Set G) = H :=
        inf_eq_left.mpr (le_centralizer_iff.mp hs)
      have ht := (coreFixed_original_sylow_fixed_line d c.L eSL h hg b t common earlier).2
      change Nat.card (coreFixed c.L ⊓ centralizer (d.S : Set G) : Subgroup G) = 2 at ht
      rw [hFH,hh,hHcard] at ht
      norm_num at ht
    have hYmove : ¬ YC d c.L ≤ centralizer (H : Set G) := by
      intro hy
      have hh : H ⊓ centralizer (YC d c.L : Set G) = H :=
        inf_eq_left.mpr (le_centralizer_iff.mp hy)
      have hz := coreFixed_opposite_residual_fixed_eq_bot d c.L eSL h hg b t common earlier
      rw [hFH,hh] at hz
      exact ((nontrivial_iff_ne_bot H).mp inferInstance) hz
    exact full_four_action_in_intermediate H d.S (YC d c.L) T
      (d.T.isPGroup'.to_le inf_le_left) (hST.trans hTH) hSmove
      (ComponentIntersection.centralizerResidual_isPPerfect _ _) (hYCT.trans hTH) hYmove
      hST hYCT hTH
  let a : T →* MulAut U := U.normalizerMonoidHom.comp (inclusion hTU)
  let q : Q →* MulAut U := U.normalizerMonoidHom.comp (inclusion hQU)
  have hQL : Q ≤ c.L := (LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)
  have hQT : Q ≤ T := hQL.trans hLT
  let l : c.L →* MulAut U := a.comp (inclusion hLT)
  let : Group.IsPerfect (c.L.subgroupOf (c.L ⊔ d.S)) := b.component.perfect
  let iL := subgroupOfEquivOfLe (show c.L ≤ c.L ⊔ d.S from le_sup_left)
  let : Group.IsPerfect c.L := Group.IsPerfect.ofSurjective
    (f := iL.toMonoidHom) iL.surjective
  let : Group.IsPerfect l.range := Group.IsPerfect.range l
  have hqa : q.range ≤ a.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion hQT x,rfl⟩
  have hql : q.range ≤ l.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion hQL x,rfl⟩
  have hlne : l.range ≠ ⊥ := by
    intro hh
    have hz : q.range = ⊥ := le_antisymm (hh ▸ hql) bot_le
    have hcard : Nat.card q.range = 64 := hQcard
    rw [hz,card_bot] at hcard
    norm_num at hcard
  have hla : l.range ≤ a.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion hLT x,rfl⟩
  have hHU : H ≤ U := le_conjugateSpanBy H _
  let k : H.subgroupOf U ≃* H := subgroupOfEquivOfLe hHU
  let : IsElementaryAbelian 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  have hUcard : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hHcard : Nat.card (H.subgroupOf U) = 4 :=
    (Nat.card_congr k.toEquiv).trans
      (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.1
  have hpres : ∀ f ∈ a.range, ∀ x : U,
      f x ∈ H.subgroupOf U ↔ x ∈ H.subgroupOf U := by
    rintro _ ⟨i,rfl⟩ x
    exact (mem_normalizer_iff.mp (hTH i.property) (x : G)).symm
  have hrad : ∀ f : MulAut U,
      (∀ x ∈ H.subgroupOf U, f x = x) →
      (∀ x : U, f x * x⁻¹ ∈ H.subgroupOf U) → f ∈ a.range := by
    intro f hfix hdisp
    exact hqa ((hQrad f).mpr ⟨hfix,hdisp⟩)
  have hres : ∀ f : MulAut (H.subgroupOf U),
      ∃ g ∈ a.range, ∀ x : H.subgroupOf U, g x = (f x : U) := by
    intro f
    let fH : MulAut H := (k.symm.trans f).trans k
    obtain ⟨i,hi⟩ := hHsurj fH
    refine ⟨a i,⟨i,rfl⟩,?_⟩
    intro x
    apply Subtype.ext
    exact congrArg (fun g : MulAut H => (g (k x) : G)) hi
  exact ⟨hTU,hTH,MulAut.elementary_five_marked_parabolic hUcard
    (H.subgroupOf U) hHcard a.range l.range hlne hla hpres hrad hres⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
