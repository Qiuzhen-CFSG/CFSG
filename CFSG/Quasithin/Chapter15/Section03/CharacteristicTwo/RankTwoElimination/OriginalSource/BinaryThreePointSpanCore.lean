module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFrattiniSpan
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightSmallDisplacement

/-!
# The actual invariant A7 span centralizes the original core

Put U=span_C(H), N=O2(C), and Q=[O2(L),L] at the original point.
The bound [U,N]<=<z> gives small displacement on U intersect Q.
The actual MS93 core has no new central elements modulo that original
central line, so U intersect Q lies in Z(Q). Since [N,L]=Q and L
normalizes U, the three-subgroup lemma first proves [U,Q]=1 and then
[[U,L],N]=1. These are literal original-subgroup statements and do not
make Q characteristic in N or assume the point kernel self-centralizing.

Source: Aschbacher--Smith15.3.23, pp.1128--1129, and the original
MS93 large-core small-displacement theorem, Section7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource LinearThree.CoreActions ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The full point-centralizer span of H centralizes the original Q;
its L-displacement lies in Z(Q) and centralizes the actual point kernel. -/
theorem binary_three_source_a7_span_core_control
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
    let N := C.pCoreIn 2
    let Q := LinearThree.commutatorCore c.L
    let U := conjugateSpanBy (intrinsicFour c.L) C
    U ⊓ Q ≤ coreCenter c.L ∧ U ≤ centralizer (Q : Set G) ∧
      ⁅U,c.L⁆ ≤ coreCenter c.L ⊓ centralizer (N : Set G) := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let J := c.L ⊔ d.S
  let Q := LinearThree.commutatorCore c.L
  let Q₀ := BinaryMS.commutatorCore (c.L.subgroupOf J)
  let H := intrinsicFour c.L
  let Z := zpowers z
  let U := conjugateSpanBy H C
  let A := U ⊓ Q
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨_,_,hHQ⟩ := intrinsicFour_properties_of_MS93 d c.L b t common earlier
  obtain ⟨hQN,hNL,_,_⟩ := binary_three_source_a7_core_stabilizer
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK a
  have hspan := binary_three_source_a7_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK a
  have hUN : U ≤ N := hspan.2.2.2.1
  have hCU : C ≤ normalizer U := hspan.2.2.2.2.1
  have hUNcomm : ⁅U,N⁆ ≤ Z := hspan.2.2.2.2.2.1
  have hZQ : Z ≤ Q := (zpowers_le.mpr hzH).trans (hHQ.trans inf_le_left)
  have hCZ : C ≤ centralizer (Z : Set G) := by
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hZL : Z ≤ centralizer (c.L : Set G) :=
    le_centralizer_iff.mp ((le_sup_left.trans hLS).trans hCZ)
  have hmap : Q₀.map J.subtype = Q :=
    sourceQ_map_subtype (show c.L ≤ J from le_sup_left) b.component
  have hQJ : Q ≤ J := hmap ▸ map_subtype_le _
  have hZJ : Z ≤ J := hZQ.trans hQJ
  have hAJ : A ≤ J := inf_le_right.trans hQJ
  have hcore : Q.subgroupOf J = Q₀ := by
    rw [←hmap]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hA₀ : A.subgroupOf J ≤ Q₀ := by rw [←hcore]; exact comap_mono inf_le_right
  have hZ₀ : Z.subgroupOf J ≤ Q₀ := by rw [←hcore]; exact comap_mono hZQ
  have hcentral : Z.subgroupOf J ≤ center J := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext ((hLS.trans hCZ) y.property x hx).symm
  have hcard : Nat.card (Z.subgroupOf J) ≤ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZJ).toEquiv,Nat.card_zpowers,hz2]
  have hsmall : ⁅A.subgroupOf J,Q₀⁆ ≤ Z.subgroupOf J := by
    intro x hx
    have hh := mem_map_of_mem J.subtype hx
    rw [map_commutator,map_subgroupOf_eq_of_le hAJ,hmap] at hh
    exact ((commutator_mono inf_le_left hQN).trans hUNcomm) hh
  have hsmallC := t.large_core_small_displacement common earlier hA₀ hZ₀ hcentral hcard hsmall
  have hAQ : A ≤ centralizer (Q : Set G) := by
    intro x hx y hy
    have hy₀ : (⟨y,hQJ hy⟩ : J) ∈ Q₀ := hcore ▸ hy
    exact congrArg Subtype.val (hsmallC (show (⟨x,hAJ hx⟩ : J) ∈ A.subgroupOf J from hx)
      ⟨y,hQJ hy⟩ hy₀)
  have hAZ : A ≤ coreCenter c.L := by
    intro x hx
    refine ⟨⟨x,hx.2⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hAQ hx y y.property)
  have hULA : ⁅U,c.L⁆ ≤ A := le_inf
    (le_normalizer_iff_commutator_le_left.mp ((le_sup_left.trans hLS).trans hCU))
    ((commutator_mono hUN le_rfl).trans hNL.le)
  have hULQ : ⁅⁅U,c.L⁆,Q⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hULA.trans hAQ)
  have hQUL : ⁅⁅Q,U⁆,c.L⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [commutator_comm Q U]
    exact ((commutator_mono le_rfl hQN).trans hUNcomm).trans hZL
  have hQL : ⁅Q,c.L⁆ = Q := by
    have hh := congrArg (map J.subtype) b.commutatorCore_idempotent
    rw [map_commutator,hmap,map_subgroupOf_eq_of_le (show c.L ≤ J from le_sup_left)] at hh
    exact hh
  have hLQU := commutator_commutator_eq_bot_of_rotate hQUL hULQ
  rw [commutator_comm c.L Q,hQL,commutator_comm Q U] at hLQU
  have hUQ : U ≤ centralizer (Q : Set G) := commutator_eq_bot_iff_le_centralizer.mp hLQU
  have hNLU : ⁅⁅N,c.L⁆,U⁆ = ⊥ := by rw [hNL,commutator_comm Q U]; exact hLQU
  have hUNL : ⁅⁅U,N⁆,c.L⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hUNcomm.trans hZL)
  have hLUN := commutator_commutator_eq_bot_of_rotate hUNL hNLU
  rw [commutator_comm c.L U] at hLUN
  exact ⟨hAZ,hUQ,le_inf (hULA.trans hAZ) (commutator_eq_bot_iff_le_centralizer.mp hLUN)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
