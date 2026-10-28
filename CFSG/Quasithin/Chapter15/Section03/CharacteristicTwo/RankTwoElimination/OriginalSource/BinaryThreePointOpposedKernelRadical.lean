module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanFrattiniPairing
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointOpposedClassTwo
public import Theory.GroupTheory.CentralBinarySelfCentralizer

/-!
# The original opposed point kernels meet in the radical

The opposed intrinsic plane is central in the actual point kernel. Applying
this to the inverse exchanger gives the other centralization. Since the
two original planes generate V, the kernel intersection lies in R=C_T(V).
The exact fixed line in the intrinsic plane also shows that N meets R in
index two. All kernels and the exchanger remain in the original group.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem center_image_le_centralizer (N : Subgroup G) :
    (center N).map N.subtype ≤ centralizer (N : Set G) := by
  rintro _ ⟨x,hx,rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)

/-- The actual opposed point kernels intersect in R, and the original point
kernel acts on its intrinsic plane with exact image of order two. -/
theorem binary_three_source_opposed_kernel_radical
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
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let H := intrinsicFour c.L
    N ⊓ N.conjBy g ≤ d.R ∧ ⁅N,N⁆ ≤ d.R ∧
      N ⊓ d.R = N ⊓ centralizer (H : Set G) ∧ d.R.relIndex N = 2 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let N := C.pCoreIn 2
  let H := intrinsicFour c.L
  let U := conjugateSpanBy H C
  let Z := zpowers z
  let Phi := frattiniIn (LinearThree.commutatorCore c.L)
  let := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  have hHgN : H.conjBy g ≤ centralizer (N : Set G) :=
    (binary_three_source_binary_opposed_class_two
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
        (K.map q) hBK (Or.inl rfl) hm g hgT hgS).1.trans
          (center_image_le_centralizer N)
  have hHgiN : H.conjBy g⁻¹ ≤ centralizer (N : Set G) :=
    (binary_three_source_binary_opposed_class_two
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
        (K.map q) hBK (Or.inl rfl) hm g⁻¹ (d.T.inv_mem hgT)
          (fun hi => hgS (d.S.inv_mem_iff.mp hi))).1.trans
            (center_image_le_centralizer N)
  have hHNg : H ≤ centralizer (N.conjBy g : Set G) := by
    have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hHgiN).trans
      (map_centralizer_le_centralizer_image (N : Set G) (MulAut.conj g).toMonoidHom)
    change (H.conjBy g⁻¹).conjBy g ≤ _ at hh
    rwa [conjBy_inv'] at hh
  obtain ⟨_,hFH,_,hex⟩ := binary_three_large_distance_fixed_factor_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  rw [hFH] at hex
  have hV : H ⊔ H.conjBy g = d.V := hex g hgT hgS
  have hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) := htwo.2.2.2.2.1
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hNT : N ≤ (d.T : Subgroup G) := hNS.trans inf_le_left
  have hNHg : N ≤ centralizer (H.conjBy g : Set G) := le_centralizer_iff.mp hHgN
  have hNgH : N.conjBy g ≤ centralizer (H : Set G) := le_centralizer_iff.mp hHNg
  have hcentral (A : Subgroup G) (hAH : A ≤ centralizer (H : Set G))
      (hAE : A ≤ centralizer (H.conjBy g : Set G)) :
      A ≤ centralizer (d.V : Set G) := by
    apply le_centralizer_iff.mpr
    rw [←hV]
    exact sup_le (le_centralizer_iff.mp hAH) (le_centralizer_iff.mp hAE)
  have hintersection : N ⊓ N.conjBy g ≤ d.R := by
    rw [hR]
    exact le_inf (inf_le_left.trans hNT)
      (hcentral _ (inf_le_right.trans hNgH) (inf_le_left.trans hNHg))
  obtain ⟨hZH,hZHindex,hHU,hUN,_,hUNcomm,_⟩ := binary_three_source_binary_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK (Or.inl rfl) hm
  have hPhi := binary_three_source_fixed_span_frattini_pairing
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hUPhi : U ≤ Phi := le_sup_left.trans hPhi.1.ge
  have hHPhi : H ≤ Phi := hHU.trans hUPhi
  have hderived : ⁅N,N⁆ ≤ d.R := by
    rw [hR]
    exact le_inf ((commutator_le_self N).trans hNT)
      (hcentral _ ((commutator_eq_bot_iff_le_centralizer.mp hPhi.2.2.2.2.1).trans
        (centralizer_le hHPhi)) ((commutator_le_self N).trans hNHg))
  have hmeet : N ⊓ d.R = N ⊓ centralizer (H : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (by
        rw [hR]
        exact inf_le_right.trans (centralizer_le
          ((show H ≤ H ⊔ H.conjBy g from le_sup_left).trans hV.le)))
    · rw [hR]
      exact le_inf inf_le_left (le_inf (inf_le_left.trans hNT)
        (hcentral _ inf_le_right (inf_le_left.trans hNHg)))
  have hNC : N ≤ C := C.pCoreIn_le 2
  have hHN : H ≤ N := hHU.trans hUN
  have hZcN : Z ≤ centralizer (N : Set G) :=
    (show Z ≤ centralizer (C : Set G) from
      zpowers_le.mpr (fun y hy => mem_centralizer_singleton_iff.mp hy)).trans
        (centralizer_le hNC)
  have hfixedU : U ⊓ centralizer (N : Set G) = Z :=
    (binary_three_source_fixed_span_kernel_boundary
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).1
  have hfixedH : H ⊓ centralizer (N : Set G) = Z :=
    le_antisymm ((inf_le_inf hHU le_rfl).trans hfixedU.le) (le_inf hZH hZcN)
  have hHNcomm : ⁅H,N⁆ ≤ Z := (commutator_mono hHU le_rfl).trans hUNcomm
  have hNnH : N ≤ normalizer H := le_normalizer_iff_commutator_le_left.mpr
    (hHNcomm.trans hZH)
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  let : IsElementaryAbelian 2 H :=
    (intrinsicFour_properties_of_MS93 d c.L b t common earlier).1
  let HN := H.subgroupOf N
  let ZN := Z.subgroupOf N
  let : IsElementaryAbelian 2 HN := IsElementaryAbelian.subgroupOf hHN
  let : HN.Normal := normal_subgroupOf_of_le_normalizer hNnH
  have hZcentral : ZN ≤ center N := by
    intro x hx
    exact mem_center_iff.mpr (fun n => Subtype.ext (hZcN hx n n.property))
  have hZcard : Nat.card ZN = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hZH.trans hHN)).toEquiv,Nat.card_zpowers,hz2]
  have hcomm : ⁅(⊤ : Subgroup N),HN⁆ ≤ ZN := by
    apply commutator_le.mpr
    intro n _ u hu
    change ⁅(n:G),(u:G)⁆ ∈ Z
    exact (commutator_comm H N ▸ hHNcomm) (commutator_mem_commutator n.property hu)
  have hpair := centralizer_relIndex_eq_of_central_binary_commutators
    (⊤ : Subgroup N) HN ZN le_top hZcentral hcomm hZcard
  have hCH' : centralizer (HN : Set N) = (centralizer (H : Set G)).subgroupOf N := by
    ext n
    constructor
    · intro hn u hu
      exact congrArg N.subtype (hn ⟨u,hHN hu⟩ hu)
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
  rw [hCH',relIndex_top_right,hCN',relIndex_subgroupOf hHN] at hpair
  change (centralizer (H : Set G)).relIndex N =
    (centralizer (N : Set G)).relIndex H at hpair
  have hindex : (centralizer (H : Set G)).relIndex N = 2 := by
    rw [hpair,←inf_relIndex_left,hfixedH]
    exact hZHindex
  refine ⟨hintersection,hderived,hmeet,?_⟩
  rw [←inf_relIndex_left,hmeet,inf_relIndex_left]
  exact hindex

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
