module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanComponentWitness
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanCentralizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanFrattiniPairing
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointNaturalDerivedSpan
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanKernelCentralizer
public import Theory.ElementaryAbelian.Join

/-!
# The original two spans inside the promoted component core

Both original spans lie in every normal containing component: their seeds
lie in L and the same point centralizer normalizes the component. The fixed
span U and moving span W are disjoint and centralize the normalizer's
full two-core. Their join is therefore an elementary subgroup of order
512 in the center of the promoted component's intrinsic two-core.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The literal fixed and moving point spans give an elementary 512 in the
center of the two-core of every normal component containing the original L. -/
theorem binary_three_source_fixed_span_promoted_core
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
    let C := centralizer ({z} : Set G)
    let U := conjugateSpanBy (intrinsicFour c.L) C
    let W := conjugateSpanBy ⁅coreCenter c.L,c.L⁆ C
    let A := normalizer (U : Set G)
    Disjoint U W ∧ IsElementaryAbelian 2 (U ⊔ W : Subgroup G) ∧
      Nat.card (U ⊔ W : Subgroup G) = 512 ∧
      ∀ D : Subgroup A, D.Normal → c.L.subgroupOf A ≤ D →
        let B := D.map A.subtype
        U ⊔ W ≤ B.pCoreIn 2 ∧
        U ⊔ W ≤ centralizer (B.pCoreIn 2 : Set G) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let V := ⁅coreCenter c.L,c.L⁆
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let W := conjugateSpanBy V C
  let A := normalizer (U : Set G)
  let F := A.pCoreIn 2
  let _ := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  have hz1 : z ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hz2
    omega
  have hWdata := binary_three_source_natural_core_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
      (K.map q) hBK hm hzH hz1
  have hWstruct := binary_three_source_binary_central_eight_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
      (K.map q) hBK (Or.inl rfl) hm
  let : IsElementaryAbelian 2 W := hWstruct.2.2.2.2.2
  let : IsElementaryAbelian 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  have hUcard : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hpair := binary_three_source_fixed_span_frattini_pairing
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hUQ : U ≤ Q := (show U ≤ frattiniIn Q from hpair.1 ▸ le_sup_left).trans
    (map_subtype_le _)
  have hUW : Disjoint U W := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    have hxV : x ∈ V := hWdata.2.1.le ⟨hx.2,hUQ hx.1⟩
    exact hpair.2.1.le_bot ⟨hx.1,hxV⟩
  have hF : F = N ⊓ centralizer (U : Set G) :=
    binary_three_source_fixed_span_normalizer_core
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  have hFCU : F ≤ centralizer (U : Set G) := hF.le.trans inf_le_right
  have hFCW : F ≤ centralizer (W : Set G) := hFCU.trans
    (binary_three_source_fixed_span_centralizer
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).1
  have hUF : U ≤ F := by
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
      U.le_normalizer le_rfl
  have hWF : W ≤ F := by
    have hWN := (binary_three_source_natural_point_derived_span
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
        (K.map q) hBK hm hzH hz1).1
    have hNF := (binary_three_source_fixed_span_kernel_centralizer
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).2.1
    exact (hWN.trans hNF).trans hF.ge
  have hWCU : W ≤ centralizer (U : Set G) := hWF.trans hFCU
  have hEW : IsElementaryAbelian 2 (U ⊔ W : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hWCU
  have hcard : Nat.card (U ⊔ W : Subgroup G) = 512 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U W
      (hWCU.trans (Subgroup.centralizer_le_normalizer _)) hUW,hUcard,hWdata.1]
  refine ⟨hUW,hEW,hcard,?_⟩
  change ∀ D : Subgroup A, D.Normal → c.L.subgroupOf A ≤ D →
    (U ⊔ W ≤ (D.map A.subtype).pCoreIn 2 ∧
      U ⊔ W ≤ centralizer ((D.map A.subtype).pCoreIn 2 : Set G))
  intro D hDn hLD
  let B := D.map A.subtype
  have hBA : B ≤ A := map_subtype_le D
  have hBAeq : B.subgroupOf A = D := comap_map_eq_self_of_injective A.subtype_injective D
  have hBn : (B.subgroupOf A).Normal := hBAeq.symm ▸ hDn
  have hAB : A ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hBA).mp hBn
  have hout := binary_three_source_fixed_span_outside
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hLA : c.L ≤ A := le_sup_left.trans hout.2.1
  have hLB : c.L ≤ B := by
    intro x hx
    exact ⟨⟨x,hLA hx⟩,hLD hx,rfl⟩
  have hCB : C ≤ normalizer (B : Set G) :=
    (le_normalizer_conjugateSpanBy (intrinsicFour c.L) C).trans hAB
  have hQL : Q ≤ c.L := (LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)
  have hHL : intrinsicFour c.L ≤ c.L :=
    ((commutator_mono (commutator_le_self Q) le_rfl).trans
      (commutator_le_self Q)).trans hQL
  have hUB : U ≤ B := conjugateSpanBy_le (hHL.trans hLB) hCB
  have hVL : V ≤ c.L := by
    have hZL : coreCenter c.L ≤ c.L := (map_subtype_le _).trans hQL
    exact (commutator_mono hZL le_rfl).trans (commutator_le_self c.L)
  have hWB : W ≤ B := conjugateSpanBy_le (hVL.trans hLB) hCB
  have hXB : U ⊔ W ≤ B := sup_le hUB hWB
  have hXF : U ⊔ W ≤ F := sup_le hUF hWF
  have hcore : U ⊔ W ≤ B.pCoreIn 2 :=
    (le_inf hXB hXF).trans (inf_pCoreIn_le_of_le 2 hBA)
  have hBF : B.pCoreIn 2 ≤ F := pCoreIn_mono_of_normalizes hBA hAB
  exact ⟨hcore,(sup_le (le_centralizer_iff.mp hFCU)
    (le_centralizer_iff.mp hFCW)).trans (centralizer_le hBF)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
