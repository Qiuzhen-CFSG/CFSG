module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanKernelBoundary
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanNPrimePairing
public import Theory.GroupTheory.Commutator.SplitPair
public import Theory.GroupTheory.FixedSupplementCentralizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Exact Frattini pairing with the original point kernel

The fixed span U and the natural eight V are disjoint commuting subgroups
of Phi(Q), of orders 32 and 8. Thus Phi(Q)=UV. The point kernel fixes V
and has precisely the point line Z as both its fixed subgroup and its
displacement on U. Hence C_Phi(N)=ZV and [Phi,N]=Z. The derived point
kernel centralizes the whole Frattini subgroup, so its intersection with Q
lies in the literal middle core D. No containment of N' in Q is asserted.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The whole original Frattini layer splits into the fixed span and natural eight,
with exact point-kernel fixed subgroup and displacement. -/
theorem binary_three_source_fixed_span_frattini_pairing
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
    let N := C.pCoreIn 2
    let E := ⁅N,N⁆
    let Q := LinearThree.commutatorCore c.L
    let Phi := frattiniIn Q
    let V := ⁅coreCenter c.L,c.L⁆
    let U := conjugateSpanBy (intrinsicFour c.L) C
    let Z := zpowers z
    let D := Q ⊓ centralizer (Phi : Set G)
    Phi = U ⊔ V ∧ Disjoint U V ∧
      Phi ⊓ centralizer (N : Set G) = Z ⊔ V ∧ ⁅Phi,N⁆ = Z ∧
      ⁅E,Phi⁆ = ⊥ ∧ E ⊓ Q ≤ D := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let N := C.pCoreIn 2
  let E := ⁅N,N⁆
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let ZQ := coreCenter c.L
  let V := ⁅ZQ,c.L⁆
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let W := conjugateSpanBy V C
  let Z := zpowers z
  let := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  have hUcard : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hUPhi : U ≤ Phi := (binary_three_source_fixed_span_frattini
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK hm).2
  have hUW : U ⊓ W = ⊥ := (binary_three_source_fixed_span_center_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK hm).1
  have hVN := binary_three_source_point_central_eight
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
  have hVcard : Nat.card V = 8 := hVN.2.1
  have hVcN : V ≤ centralizer (N : Set G) := hVN.2.2
  have hUV : Disjoint U V := disjoint_iff.mpr (bot_unique
    ((inf_le_inf_left U (le_conjugateSpanBy V C)).trans hUW.le))
  have hLZ : c.L ≤ normalizer ZQ :=
    (normalizer_commutator_ge_right _ _).trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))
  have hVZ : V ≤ ZQ := le_normalizer_iff_commutator_le_left.mp hLZ
  have hsizes := binary_three_large_distance_original_core_structure
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hZPhi : ZQ ≤ Phi := map_mono hsizes.2.2.2.2.1
  have hPhicard : Nat.card Phi = 256 := by
    change Nat.card ((frattini Q).map Q.subtype) = 256
    rw [card_map_of_injective Q.subtype_injective]
    exact hsizes.2.2.1
  have hUQ : U ≤ Q := hUPhi.trans (map_subtype_le _)
  have hZcQ : ZQ ≤ centralizer (Q : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hVcU : V ≤ centralizer (U : Set G) :=
    (hVZ.trans hZcQ).trans (centralizer_le hUQ)
  have hVnU : V ≤ normalizer U := hVcU.trans (Subgroup.centralizer_le_normalizer _)
  have hprod : Phi = U ⊔ V := (eq_of_le_of_card_ge
    (sup_le hUPhi (hVZ.trans hZPhi)) (by
      rw [card_sup_eq_mul_of_normalizes_of_disjoint U V hVnU hUV,hUcard,hVcard,hPhicard])).symm
  obtain ⟨hfixed,hcomm⟩ := binary_three_source_fixed_span_kernel_boundary
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hPhiFixed : Phi ⊓ centralizer (N : Set G) = Z ⊔ V := by
    rw [hprod,sup_comm U V,inf_centralizer_sup_of_centralizing V U N hVnU hVcN,hfixed,
      sup_comm V Z]
  have hPhiComm : ⁅Phi,N⁆ = Z := by
    rw [hprod,commutator_sup_of_commuting_factors U V N (le_centralizer_iff.mp hVcU)
      ((le_centralizer_iff.mp hVcN).trans (Subgroup.centralizer_le_normalizer _)),
      commutator_eq_bot_iff_le_centralizer.mpr hVcN,hcomm,sup_bot_eq]
  have hEU : ⁅E,U⁆ = ⊥ := (binary_three_source_fixed_span_nprime_pairing
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK (Or.inl rfl) hm).2.2
  have hPhiE : Phi ≤ centralizer (E : Set G) := by
    rw [hprod]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hEU))
      (hVcN.trans (centralizer_le (commutator_le_self N)))
  have hEcent : E ≤ centralizer (Phi : Set G) := le_centralizer_iff.mp hPhiE
  exact ⟨hprod,hUV,hPhiFixed,hPhiComm,commutator_eq_bot_iff_le_centralizer.mpr hEcent,
    le_inf inf_le_right (inf_le_left.trans hEcent)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
