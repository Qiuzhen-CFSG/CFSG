module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointPhiAction
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# The original moving eight lies in the center of the point kernel

The point kernel N moves Z(Q) only into H, which L centralizes. Moreover
[N,L] lies in Q and Q centralizes Z(Q). The three-subgroups lemma therefore
makes N centralize the actual natural eight [Z(Q),L]. In the binary four
and five carriers its entire C-conjugate span lies in Z(N), since Z(Q)
lies in Phi(Q) and Phi(Q) lies in N. No invariance of Q under C is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem source_center_displacement_structure
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical) :
    IsElementaryAbelian 2 (⁅coreCenter L,L⁆ : Subgroup G) ∧
      Nat.card (⁅coreCenter L,L⁆ : Subgroup G) = 8 := by
  let J := L ⊔ d.S
  let Q := LinearThree.commutatorCore L
  let Q₀ := BinaryMS.commutatorCore (L.subgroupOf J)
  have hmap : Q₀.map J.subtype = Q := sourceQ_map_subtype
    (show L ≤ J from le_sup_left) b.component
  have hms : msQ (L.subgroupOf J) (d.S.subgroupOf J) = Q₀ := by
    have hp : (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J := pCore_map_iso 2 topEquiv
    rw [msQ,b.sup_eq_top,hp]
  obtain ⟨hZe,_,_,hs⟩ := t.center_source_sections common hb
  rw [hms] at hZe
  change HasSectionModel (L.subgroupOf J)
    (⁅CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ (L.subgroupOf J) (d.S.subgroupOf J)),L.subgroupOf J⁆)
    ⊥ _ _ at hs
  rw [hms] at hs
  let V₀ := ⁅CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q₀,L.subgroupOf J⁆
  have hVZ : V₀ ≤ CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q₀ := by
    apply le_normalizer_iff_commutator_le_left.mp
    exact (normalizer_commutator_ge_right _ _).trans
      (normalizer_le_normalizer_characteristic_image Q₀ (center Q₀))
  obtain ⟨_,_,_,hn,ev,_⟩ := hs
  let := hn
  have hv0 : Nat.card V₀ = 8 := by
    have he : Nat.card (V₀ ⧸ (⊥ : Subgroup J).subgroupOf V₀) = 8 := by
      rw [Nat.card_congr ev.toEquiv]
      change Nat.card (Fin 3 → ZMod 2) = 8
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Module.finrank_pi,
        Fintype.card_fin,Nat.card_zmod]
      norm_num
    simpa only [bot_subgroupOf,Nat.card_congr (QuotientGroup.quotientBot (G := V₀)).toEquiv] using he
  have hm : V₀.map J.subtype = ⁅coreCenter L,L⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)]
    change ⁅((center Q₀).map Q₀.subtype).map J.subtype,L⁆ = _
    rw [map_subgroup_center_eq _ J.subtype_injective,hmap]
    rfl
  have hVE : IsElementaryAbelian 2 V₀ := by
    let := hZe
    exact IsElementaryAbelian.of_le hVZ
  rw [←hm,card_map_of_injective J.subtype_injective]
  let := hVE
  exact ⟨IsElementaryAbelian.map J.subtype,hv0⟩

/-- The actual moving eight centralizes the original point kernel. -/
theorem binary_three_source_point_central_eight
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
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    : let C := centralizer ({z} : Set G)
      let N := C.pCoreIn 2
      let V := ⁅coreCenter c.L,c.L⁆
      IsElementaryAbelian 2 V ∧ Nat.card V = 8 ∧
        V ≤ centralizer (N : Set G) := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let J := c.L ⊔ d.S
  let Q := LinearThree.commutatorCore c.L
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hH := (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2.trans inf_le_right
  have hNZ := (binary_three_source_point_phi_action
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP).1
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hNJ : N ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 C) (hNS.trans le_sup_right) (hLS.trans hCN)
  have hJL : J ≤ normalizer c.L :=
    (normal_subgroupOf_iff_le_normalizer (show c.L ≤ J from le_sup_left)).mp b.component_normal
  have hNL : ⁅N,c.L⁆ ≤ Q := (commutator_mono hNJ le_rfl).trans
    (overgroup_core_commutator_eq d c (le_sup_right.trans hJL)).le
  have hZQ : coreCenter c.L ≤ centralizer (Q : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hrot₁ : ⁅⁅c.L,N⁆,coreCenter c.L⁆ = ⊥ := by
    rw [commutator_comm c.L N]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hNL.trans (le_centralizer_iff.mp hZQ))
  have hrot₂ : ⁅⁅N,coreCenter c.L⁆,c.L⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hNZ.trans hH)
  exact ⟨(source_center_displacement_structure d c.L b t common hb).1,
    (source_center_displacement_structure d c.L b t common hb).2,
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_commutator_eq_bot_of_rotate hrot₁ hrot₂)⟩

/-- The full C-span of the original moving eight is elementary and central in N. -/
theorem binary_three_source_binary_central_eight_span
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
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL K n 2) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let V := ⁅coreCenter c.L,c.L⁆
    let W := conjugateSpanBy V C
    IsElementaryAbelian 2 V ∧ Nat.card V = 8 ∧ V ≤ W ∧
      W ≤ (center N).map N.subtype ∧ C ≤ normalizer W ∧
      IsElementaryAbelian 2 W := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  obtain ⟨hVe,hVcard,hVc⟩ := binary_three_source_point_central_eight
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
  have hPhi := binary_three_source_binary_phi_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hn hm
  have hZPhi : coreCenter c.L ≤ frattiniIn Q := map_mono
    (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.2.1
  have hLZ : c.L ≤ normalizer (coreCenter c.L) :=
    (normalizer_commutator_ge_right _ _).trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))
  have hVZ : V ≤ coreCenter c.L := le_normalizer_iff_commutator_le_left.mp hLZ
  have hVN : V ≤ N := hVZ.trans (hZPhi.trans hPhi)
  have hVcenter : V ≤ (center N).map N.subtype := by
    intro x hx
    refine ⟨⟨x,hVN hx⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hVc hx y y.property)
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hWcenter : W ≤ (center N).map N.subtype := conjugateSpanBy_le hVcenter
    (hCN.trans (normalizer_le_normalizer_characteristic_image N (center N)))
  let : IsElementaryAbelian 2 V := hVe
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp (by
    intro x hx y hy
    obtain ⟨x,hxc,rfl⟩ := hWcenter hx
    have hyN : y ∈ N := map_subtype_le _ (hWcenter hy)
    exact congrArg Subtype.val (mem_center_iff.mp hxc ⟨y,hyN⟩))
  exact ⟨hVe,hVcard,le_conjugateSpanBy V C,hWcenter,
    le_normalizer_conjugateSpanBy V C,conjugateSpanBy_elementary_of_commutative V C⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
