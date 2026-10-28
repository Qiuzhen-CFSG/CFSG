module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanPointImage
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanUnique
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeFixedFactorBound

/-!
# Full automorphisms of the original fixed span

The original point centralizer induces its full point stabilizer on U.
The opposite residual supplies an element moving the same point, while
uniqueness of U ensures that this element normalizes U. The prime index
of the point stabilizer then forces the entire automorphism group.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- Every automorphism of the original elementary fixed span is induced by
its actual ambient normalizer. -/
theorem binary_three_source_fixed_span_full_normalizer
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
    Function.Surjective U.normalizerMonoidHom := by
  let C := centralizer ({z} : Set G)
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let β := U.normalizerMonoidHom
  let hCU := le_normalizer_conjugateSpanBy (intrinsicFour c.L) C
  let α := β.comp (inclusion hCU)
  let zU : U := ⟨z,le_conjugateSpanBy _ C hzH⟩
  change Function.Surjective β
  have hpoint : α.range = MulAction.stabilizer (MulAut U) zU :=
    binary_three_source_fixed_span_point_image
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  have hstab : MulAction.stabilizer (MulAut U) zU ≤ β.range := by
    rw [←hpoint]
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion hCU x,rfl⟩
  have hnorm : normalizer (c.L : Set G) ≤ normalizer (U : Set G) :=
    (binary_three_source_fixed_span_unique
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).2
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hfixed := coreFixed_opposite_residual_fixed_eq_bot d c.L eSL h hg b t common earlier
  have hFH := (binary_three_large_distance_fixed_factor_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.1
  have hz1 : z ≠ 1 := by
    intro hh
    rw [hh,orderOf_one] at hz2
    norm_num at hz2
  have hmove : ¬ YC d c.L ≤ C := by
    intro hh
    have hzfix : z ∈ centralizer (YC d c.L : Set G) := by
      intro y hy
      exact mem_centralizer_singleton_iff.mp (hh hy)
    exact hz1 (hfixed.le ⟨hFH.symm ▸ hzH,hzfix⟩)
  obtain ⟨y,hy,hyC⟩ := SetLike.not_le_iff_exists.mp hmove
  have hyN : y ∈ normalizer (U : Set G) := hnorm (h.normalizes_component
    (((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_left) hy))
  let yN : normalizer (U : Set G) := ⟨y,hyN⟩
  have hymove : β yN zU ≠ zU := by
    intro hh
    have hyz : y*z*y⁻¹ = z := congrArg Subtype.val hh
    apply hyC
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hyz)
  let : IsElementaryAbelian 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  have hUcard : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hzU : zU ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
  exact MonoidHom.range_eq_top.mp
    (MulAut.eq_top_of_elementaryThirtyTwo_stabilizer_of_moves hUcard β.range zU hzU
      hstab ⟨β yN,⟨yN,rfl⟩,hymove⟩)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
