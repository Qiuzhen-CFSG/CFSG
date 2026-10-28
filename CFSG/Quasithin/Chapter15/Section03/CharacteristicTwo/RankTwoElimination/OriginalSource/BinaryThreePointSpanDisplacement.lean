module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSpanCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightCenter
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The original component moves at most eight elements of the A7 span

The invariant span U=span_C(H) has [U,L]<=Z(Q). Perfectness makes this
displacement idempotent under L, so it lies in [Z(Q),L]. The latter is
literally the original natural three-space in MS93's center decomposition,
transported through the same join embedding, and has order eight.
No bound on the dimension of the point-kernel Frattini quotient is used.

Source: Aschbacher--Smith15.3.23, pp.1128--1129; MS93(4.5)(iii)--(iv), p.895.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource LinearThree.CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem source_center_displacement_card
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical) :
    Nat.card (⁅coreCenter L,L⁆ : Subgroup G) = 8 := by
  let J := L ⊔ d.S
  let Q := LinearThree.commutatorCore L
  let Q₀ := BinaryMS.commutatorCore (L.subgroupOf J)
  have hmap : Q₀.map J.subtype = Q := sourceQ_map_subtype
    (show L ≤ J from le_sup_left) b.component
  have hms : msQ (L.subgroupOf J) (d.S.subgroupOf J) = Q₀ := by
    have hp : (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J := pCore_map_iso 2 topEquiv
    rw [msQ,b.sup_eq_top,hp]
  obtain ⟨_,_,_,hs⟩ := t.center_source_sections common hb
  change HasSectionModel (L.subgroupOf J)
    (⁅CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ (L.subgroupOf J) (d.S.subgroupOf J)),L.subgroupOf J⁆)
    ⊥ _ _ at hs
  rw [hms] at hs
  let V₀ := ⁅CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q₀,L.subgroupOf J⁆
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
  rw [←hm,card_map_of_injective J.subtype_injective]
  exact hv0

/-- The actual A7 point span has original component displacement of order at most eight. -/
theorem binary_three_source_a7_span_displacement_bound
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
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (a : K ≃* alternatingGroup (Fin 7)) :
    let C := centralizer ({z} : Set G)
    let U := conjugateSpanBy (intrinsicFour c.L) C
    ⁅U,c.L⁆ ≤ ⁅coreCenter c.L,c.L⁆ ∧
      Nat.card (⁅coreCenter c.L,c.L⁆ : Subgroup G) = 8 ∧
      Nat.card (⁅U,c.L⁆ : Subgroup G) ≤ 8 := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let U := conjugateSpanBy (intrinsicFour c.L) C
  obtain ⟨common⟩ := t.commonFacts hc
  have hspan := binary_three_source_a7_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK a
  have hUN : U ≤ N := hspan.2.2.2.1
  have hLU : c.L ≤ normalizer U := (le_sup_left.trans hLS).trans hspan.2.2.2.2.1
  have hcore := binary_three_source_a7_span_core_control
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK a
  let : Group.IsPerfect (c.L.subgroupOf (c.L ⊔ d.S)) := b.component.perfect
  let i := subgroupOfEquivOfLe (show c.L ≤ c.L ⊔ d.S from le_sup_left)
  let : Group.IsPerfect c.L := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
  have hp : IsPPerfect 2 c.L := (pResidual_eq_top_iff 2 c.L).mp (pResidual_eq_top_of_isPerfect 2)
  have hid := commutator_isPPerfect_idempotent c.L U hp
    ((isPGroup_pCoreIn 2 C).to_le hUN) hLU
  have hm : ⁅U,c.L⁆ ≤ ⁅coreCenter c.L,c.L⁆ := by
    rw [←hid]
    exact commutator_mono (hcore.2.2.trans inf_le_left) le_rfl
  have h8 := source_center_displacement_card d c.L b t common hb
  exact ⟨hm,h8,(card_le_of_le hm).trans h8.le⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
