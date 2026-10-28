module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanContainingComponent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanNormalizerCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanProduct
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryTheta
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.BinaryFiveImage
public import Theory.ElementaryAbelian.AutomorphismLinearModel
public import Theory.GroupTheory.CComponent.PrimeGroupOvergroup
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The actual binary-five containing component

The original component moves its fixed span. The normal containing component
therefore has nontrivial normal image in the full simple automorphism group
of that span. Its image is the whole group, and the SQTK kernel theorem
identifies the action kernel with its intrinsic two-core. Movement of the
normal elementary subgroup also excludes an ordinary component, giving
characteristic two for its join with the original Sylow subgroup.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem component_image_eq_theta {G : Type*} [Group G] [Finite G] (A : Subgroup G) (D : Subgroup A)
    (hD : D.IsCComponent) (hrA : primeRank 3 A ≤ 2)
    (e : (D ⧸ pCore 2 D) ≃* PSL(5,ZMod 2)) : D.map A.subtype = theta A := by
  have hF := Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv (e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide)))
    (Theory.SpecificGroups.BinaryComponentResidual.linear (Or.inr rfl))
  let : IsQuasisimple PSL(5,ZMod 2) := Theory.SpecificGroups.PSL5Two.UniversalCover.isQuasisimple _
  let : IsQuasisimple (D ⧸ pCore 2 D) := IsQuasisimple.of_mulEquiv e.symm
  let : Group.IsPerfect D := hD.perfect
  have hres : D = primeToResidual 3 A :=
    hD.eq_primeToResidual_three_of_rank_outer_two hF.1 hF.2.1 hrA hF.2.2
  have hr : 2 ≤ primeRank 3 D := hF.2.1.trans
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
  have hz : primeRank 3 (center (D ⧸ pCore 2 D)) ≤ 1 := by
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply primeRank_le_of_card_le_prime_pow (n := 1)
    rw [hF.1,card_bot]
    decide
  have htheta : theta (⊤ : Subgroup A) = D := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      rintro x ⟨_,hx⟩
      rw [hres]
      apply mem_primeToResidual_of_pow (n := 1)
      simpa only [pow_one,hx] using pow_orderOf_eq_one x
    · have hg := cubic_closure_eq_top_of_twoCore_quasisimple hr hz
      have hm := congrArg (map D.subtype) hg
      rw [MonoidHom.map_closure, ←MonoidHom.range_eq_map,range_subtype] at hm
      rw [←hm]
      apply Subgroup.closure_mono
      rintro x ⟨y,hy,rfl⟩
      exact ⟨mem_top _, (D.orderOf_coe y).trans hy⟩
  rw [←htheta,theta_map_of_injective A.subtype A.subtype_injective,
    ←MonoidHom.range_eq_map,range_subtype]

/-- The actual containing component acts fully on U with exactly its two-core
as kernel; adjoining the original S gives characteristic two. -/
theorem binary_three_source_fixed_span_component_action
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
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) 4 2) :
    let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
    let A := normalizer (U : Set G)
    ∃ D : Subgroup A, D.IsCComponent ∧ D.Normal ∧ c.L.subgroupOf A ≤ D ∧
      Function.Surjective (U.normalizerMonoidHom.comp D.subtype) ∧
      (U.normalizerMonoidHom.comp D.subtype).ker = pCore 2 D ∧
      Nonempty ((D ⧸ pCore 2 D) ≃* PSL(5,ZMod 2)) ∧
      HasCharacteristicTwo (D ⊔ d.S.subgroupOf A) := by
  let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
  let A := normalizer (U : Set G)
  have hout := binary_three_source_fixed_span_outside
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  obtain ⟨D,hD,hDn,hLD,_⟩ := binary_three_source_fixed_span_containing_component
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  let : D.Normal := hDn
  let : IsElementaryAbelian 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  have hUcard : Nat.card U = 2 ^ 5 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  let a : MulAut U ≃* PSL(5,ZMod 2) :=
    (IsElementaryAbelian.mulAutLinearEquivOfCard U hUcard).trans
      ((BinaryLinear.OuterCyclic.matrixEquivLinear 5).trans
        (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide)).symm)
  let beta := U.normalizerMonoidHom
  let f : A →* PSL(5,ZMod 2) := a.toMonoidHom.comp beta
  have hbeta : Function.Surjective beta := binary_three_source_fixed_span_full_normalizer
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hfsurj : Function.Surjective f := a.surjective.comp hbeta
  have hLmove : ¬ c.L ≤ centralizer (U : Set G) := by
    intro hfix
    have hQfix := ((LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)).trans hfix
    have hcomm : ⁅U,LinearThree.commutatorCore c.L⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hQfix)
    have hH := (binary_three_source_fixed_span_frattini_product
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).2
    have hz1 : z = 1 := (hH.symm.trans hcomm).le hzH
    rw [hz1,orderOf_one] at hz2
    norm_num at hz2
  have hDmove : ¬ D ≤ beta.ker := by
    intro hfix
    apply hLmove
    intro x hx
    have hxA : x ∈ A := (le_sup_left.trans hout.2.1) hx
    have hk : (⟨x,hxA⟩ : A) ∈ beta.ker := hfix (hLD hx)
    rwa [normalizerMonoidHom_ker] at hk
  let : IsSimpleGroup PSL(5,ZMod 2) := Atlas.psl_simple_high_rank 5 (by decide)
  let : (D.map f).Normal := hDn.map f hfsurj
  have himage : D.map f = ⊤ := by
    rcases (inferInstance : (D.map f).Normal).eq_bot_or_eq_top with hbot | htop
    · apply False.elim
      apply hDmove
      have hker : D ≤ f.ker := (map_eq_bot_iff D).mp hbot
      simpa only [f,MonoidHom.ker_comp_of_injective beta a.toMonoidHom a.injective] using hker
    · exact htop
  let fD := f.comp D.subtype
  have hfD : Function.Surjective fD := by
    rw [←MonoidHom.range_eq_top,MonoidHom.range_comp,range_subtype]
    exact himage
  let betaD := beta.comp D.subtype
  have hbetaD : Function.Surjective betaD := by
    intro x
    obtain ⟨y,hy⟩ := hfD (a x)
    exact ⟨y,a.injective hy⟩
  have hker : fD.ker = pCore 2 D :=
    ChapterA.Section03.cComponent_binary_five_kernel hout.2.2.2.2.1 hD fD hfD
  have hkerBeta : betaD.ker = pCore 2 D := by
    have he : fD = a.toMonoidHom.comp betaD := rfl
    rw [he,MonoidHom.ker_comp_of_injective betaD a.toMonoidHom a.injective] at hker
    exact hker
  have he : Nonempty ((D ⧸ pCore 2 D) ≃* PSL(5,ZMod 2)) := by
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fD hfD)⟩
  let UA := U.subgroupOf A
  have hUA : U ≤ A := U.le_normalizer
  let : UA.Normal := (normal_subgroupOf_iff_le_normalizer hUA).mpr le_rfl
  have hUp : IsPGroup 2 UA := (IsElementaryAbelian.isPGroup 2 U).of_equiv
    (subgroupOfEquivOfLe hUA).symm
  have hmove : ⁅D,UA⁆ ≠ ⊥ := by
    intro hzero
    apply hDmove
    intro x hx
    rw [normalizerMonoidHom_ker]
    intro u hu
    exact congrArg Subtype.val
      ((commutator_eq_bot_iff_le_centralizer.mp hzero hx) ⟨u,hUA hu⟩ hu)
  have hSp : IsPGroup 2 (d.S.subgroupOf A) := (d.T.isPGroup'.to_le (show d.S ≤ d.T from inf_le_left)).of_equiv
    (subgroupOfEquivOfLe (le_sup_right.trans hout.2.1)).symm
  have hchar : HasCharacteristicTwo (D ⊔ d.S.subgroupOf A) := by
    rcases hD.component_or_generalizedFitting_sup_eq_pCore hSp hout.2.2.2.2.2 with hDc | hh
    · rcases hDc.normal_dichotomy UA with hDU | hcomm
      · let : Group.IsNilpotent D := (hUp.to_le hDU).isNilpotent
        exact (hD.not_isSolvable inferInstance).elim
      · exact (hmove hcomm).elim
    · exact hh
  exact ⟨D,hD,hDn,hLD,hbetaD,hkerBeta,he,hchar⟩

/-- The same containing component is the actual cubic closure of its
normalizer and contains the original Yplus; its ambient Sylow join is
also of characteristic two. -/
theorem binary_three_source_fixed_span_component_theta
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
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) 4 2) :
    let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
    let A := normalizer (U : Set G)
    ∃ D : Subgroup A, D.IsCComponent ∧ D.Normal ∧ c.L.subgroupOf A ≤ D ∧
      Function.Surjective (U.normalizerMonoidHom.comp D.subtype) ∧
      (U.normalizerMonoidHom.comp D.subtype).ker = pCore 2 D ∧
      Nonempty ((D ⧸ pCore 2 D) ≃* PSL(5,ZMod 2)) ∧
      D.map A.subtype = theta A ∧ d.Yplus ≤ D.map A.subtype ∧
      HasCharacteristicTwo (D.map A.subtype ⊔ d.S) := by
  let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
  let A := normalizer (U : Set G)
  obtain ⟨D,hD,hDn,hLD,hfull,hker,⟨eD⟩,hchar⟩ :=
    binary_three_source_fixed_span_component_action
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  have hout := binary_three_source_fixed_span_outside
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have htheta : D.map A.subtype = theta A := component_image_eq_theta A D hD
    (hout.2.2.2.2.1.stronglyQuasithin 3 Nat.prime_three (by decide)) eD
  have hY : d.Yplus ≤ D.map A.subtype := by
    have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
      hG d hempty hM hu hmany A hout.2.2.1
    rw [h11.theta_eq,htheta]
    exact theta_mono inf_le_right
  have hSA : d.S ≤ A := le_sup_right.trans hout.2.1
  have hmap : (D ⊔ d.S.subgroupOf A).map A.subtype = D.map A.subtype ⊔ d.S := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hSA]
  let j : ↥(D ⊔ d.S.subgroupOf A) ≃* ↥(D.map A.subtype ⊔ d.S) :=
    ((D ⊔ d.S.subgroupOf A).equivMapOfInjective A.subtype A.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hcharG : HasCharacteristicTwo (D.map A.subtype ⊔ d.S) := by
    change generalizedFitting ↥(D.map A.subtype ⊔ d.S) = pCore 2 ↥(D.map A.subtype ⊔ d.S)
    rw [←map_generalizedFitting_equiv j,←pCore_map_iso 2 j]
    exact congrArg (map j.toMonoidHom) hchar
  exact ⟨D,hD,hDn,hLD,hfull,hker,⟨eD⟩,htheta,hY,hcharG⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
