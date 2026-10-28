module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourFixedIntersection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourPhiCentralizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Exact center and Frattini intersections of the original span

The whole recognized span is disjoint from the intrinsic four. Inside the
original core center, adjoining that four multiplies orders by four. The
center has order32 and the original natural eight lies in both factors,
so the span intersects the center in exactly that eight. The actual
point-kernel centralizer theorem then gives the same Frattini intersection.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- Both literal original core intersections are exactly the original
natural eight; no characteristicity of Q in the point kernel is asserted. -/
theorem binary_three_source_four_center_intersection
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
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let Q := LinearThree.commutatorCore c.L
    let V := ⁅coreCenter c.L,c.L⁆
    let W := conjugateSpanBy V (centralizer ({z} : Set G))
    W ⊓ coreCenter c.L=V ∧ W ⊓ frattiniIn Q=V := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let ZQ := coreCenter c.L
  let Phi := frattiniIn Q
  let H := intrinsicFour c.L
  let V := ⁅ZQ,c.L⁆
  let W := conjugateSpanBy V C
  let A := W ⊓ ZQ
  obtain ⟨_,hVcard,hVW,hWZ,_,_⟩ := binary_three_source_binary_central_eight_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm
  have hWH := (binary_three_source_four_fixed_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm).2
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨_,hHcard,hHF⟩ := intrinsicFour_properties_of_MS93 d c.L b t common earlier
  have hHZ : H ≤ ZQ := by
    intro x hx
    refine ⟨⟨x,(hHF hx).1⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext ((hHF hx).2 y
      (((LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)) y.property))
  have hZQ : ZQ ≤ Q := map_subtype_le _
  have hZc : ZQ ≤ centralizer (Q : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hHA : H ≤ normalizer A :=
    ((hHZ.trans hZc).trans (centralizer_le (show A ≤ Q from inf_le_right.trans hZQ))).trans
      (Subgroup.centralizer_le_normalizer (A : Set G))
  have hdis : Disjoint A H := disjoint_iff.mpr
    (bot_unique ((inf_le_inf_right H (show A ≤ W from inf_le_left)).trans hWH.le))
  have hZcard : Nat.card ZQ=32 := by
    rw [show ZQ=(center Q).map Q.subtype from rfl,card_map_of_injective Q.subtype_injective]
    exact (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.1
  have hAcard : Nat.card A ≤ 8 := by
    have hh := card_le_of_le (sup_le (show A ≤ ZQ from inf_le_right) hHZ)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A H hHA hdis,hHcard,hZcard] at hh
    omega
  have hLVZ : c.L ≤ normalizer ZQ :=
    (normalizer_commutator_ge_right _ _).trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))
  have hVZ : V ≤ ZQ := le_normalizer_iff_commutator_le_left.mp hLVZ
  have heZ : A=V := (eq_of_le_of_card_ge (le_inf hVW hVZ)
    (hAcard.trans_eq hVcard.symm)).symm
  have hWc : W ≤ centralizer (N : Set G) := by
    intro w hw
    obtain ⟨x,hx,rfl⟩ := hWZ hw
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hWPZ : W ⊓ Phi ≤ ZQ :=
    (binary_three_source_four_phi_centralizer
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm).2.2.2 W hWc
  have hZPhi : ZQ ≤ Phi := by
    change (center Q).map Q.subtype ≤ (frattini Q).map Q.subtype
    exact map_mono (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.2.1
  exact ⟨heZ,le_antisymm ((le_inf inf_le_left hWPZ).trans heZ.le)
    (le_inf hVW (hVZ.trans hZPhi))⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
