module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanKernelBoundary
public import Theory.GroupTheory.CentralBinarySelfCentralizer

/-!
# Exact order of the original point-kernel action on the fixed span

The fixed span U lies in the Frattini subgroup and centralizes it, hence U
is abelian. Its elementary generators make U elementary of order 32.
The central binary commutator pairing then equates the two centralizer
indices. Since C_U(N) is the original point line, |N:C_N(U)| is 16.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The full original point kernel induces an action of order sixteen on the
actual elementary fixed span; its centralizer kernel is retained. -/
theorem binary_three_source_fixed_span_kernel_index
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
    let U := conjugateSpanBy (intrinsicFour c.L) C
    IsElementaryAbelian 2 U ∧ (centralizer (U : Set G)).relIndex N = 16 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let H := intrinsicFour c.L
  let U := conjugateSpanBy H C
  let Z := zpowers z
  let := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  obtain ⟨hUD,hUPhi⟩ := binary_three_source_fixed_span_frattini
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK hm
  have hUcPhi : U ≤ centralizer (Phi : Set G) := hUD.trans inf_le_right
  let : IsMulCommutative U := le_centralizer_iff_isMulCommutative.mp
    (hUcPhi.trans (centralizer_le hUPhi))
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  let : IsElementaryAbelian 2 H :=
    (intrinsicFour_properties_of_MS93 d c.L b t common earlier).1
  let hU : IsElementaryAbelian 2 U := conjugateSpanBy_elementary_of_commutative H C
  have hUcard : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  obtain ⟨hfixed,hcommEq⟩ := binary_three_source_fixed_span_kernel_boundary
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  obtain ⟨hZH,_,hHU,hUN,hCU,_⟩ := binary_three_source_binary_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK (Or.inl rfl) hm
  change U ⊓ centralizer (N : Set G) = Z at hfixed
  change ⁅U,N⁆ = Z at hcommEq
  have hZU : Z ≤ U := hZH.trans hHU
  have hNC : N ≤ C := C.pCoreIn_le 2
  let UN := U.subgroupOf N
  let ZN := Z.subgroupOf N
  let : IsElementaryAbelian 2 UN := IsElementaryAbelian.subgroupOf hUN
  let : UN.Normal := normal_subgroupOf_of_le_normalizer (hNC.trans hCU)
  have hZcentral : ZN ≤ center N := by
    intro x hx
    apply mem_center_iff.mpr
    intro n
    apply Subtype.ext
    exact (show Z ≤ centralizer (C : Set G) from
      zpowers_le.mpr (fun y hy => mem_centralizer_singleton_iff.mp hy)) hx n (hNC n.property)
  have hZcard : Nat.card ZN = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hZU.trans hUN)).toEquiv,Nat.card_zpowers,hz2]
  have hcomm : ⁅(⊤ : Subgroup N),UN⁆ ≤ ZN := by
    apply commutator_le.mpr
    intro n _ u hu
    change ⁅(n:G),(u:G)⁆ ∈ Z
    rw [←hcommEq,commutator_comm]
    exact commutator_mem_commutator n.property hu
  have hpair := centralizer_relIndex_eq_of_central_binary_commutators
    (⊤ : Subgroup N) UN ZN le_top hZcentral hcomm hZcard
  have hCU' : centralizer (UN : Set N) = (centralizer (U : Set G)).subgroupOf N := by
    ext n
    constructor
    · intro hn u hu
      exact congrArg N.subtype (hn ⟨u,hUN hu⟩ hu)
    · intro hn u hu
      exact Subtype.ext (hn u hu)
  have hCN' : centralizer ((⊤ : Subgroup N) : Set N) =
      (centralizer (N : Set G)).subgroupOf N := by
    ext n
    constructor
    · intro hn x hx
      exact congrArg N.subtype (hn ⟨x,hx⟩ (mem_top _))
    · intro hn x _
      exact Subtype.ext (hn x x.property)
  rw [hCU',relIndex_top_right,hCN',relIndex_subgroupOf hUN] at hpair
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G)
    (U ⊓ centralizer (N : Set G)) U bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at hi
  rw [hfixed,hUcard,Nat.card_zpowers,hz2] at hi
  change 2 * (centralizer (N : Set G)).relIndex U = 32 at hi
  have hindex : (centralizer (N : Set G)).relIndex U = 16 := by omega
  exact ⟨hU,hpair.trans hindex⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
