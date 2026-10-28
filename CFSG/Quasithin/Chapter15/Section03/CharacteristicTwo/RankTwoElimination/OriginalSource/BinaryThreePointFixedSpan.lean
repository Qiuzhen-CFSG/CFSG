module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointA7Orbit
public import Theory.GroupTheory.Commutator.NormalSpan
public import Theory.GroupTheory.ConjugateSpanElementaryQuotient
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# An actual invariant central section at the A7 point

The original four H lies in the point kernel N in the A7 case. Its
commutator with N lies in the actual displacement point Z=<z>. Since the
whole point centralizer C fixes z and normalizes N, the same bound holds
for the C-span U of H. Thus U<=N and U/Z is elementary and central in N/Z.
Its literal conjugation action descends to C/N, with the original element
formula. This provides an invariant section without assuming Q characteristic
in N or self-centralization of N. No faithfulness or carrier exclusion is
asserted for this new section.

Source: Aschbacher--Smith15.3.23, pp.1128--1129; the original displacement
calculation and the A7 placement, preserving the original point and kernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The actual point-centralizer span of the original four gives an
invariant elementary section on which the point quotient acts literally. -/
theorem binary_three_source_a7_fixed_span
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
    let H := intrinsicFour c.L
    let Z := zpowers z
    let U := conjugateSpanBy H C
    Z ≤ H ∧ Z.relIndex H = 2 ∧ H ≤ U ∧ U ≤ N ∧
      C ≤ normalizer U ∧ ⁅U,N⁆ ≤ Z ∧
      ∃ hn : (Z.subgroupOf U).Normal,
        letI := hn
        IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U) ∧
        ∃ ρ : (C ⧸ pCore 2 C) →* MulAut (U ⧸ Z.subgroupOf U),
          ∀ (x : C) (u v : U), (v : G) = x*(u : G)*(x : G)⁻¹ →
            ρ (QuotientGroup.mk' (pCore 2 C) x) (QuotientGroup.mk' (Z.subgroupOf U) u) =
              QuotientGroup.mk' (Z.subgroupOf U) v := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let J := c.L ⊔ d.S
  let Q := LinearThree.commutatorCore c.L
  let H := intrinsicFour c.L
  let Z := zpowers z
  let U := conjugateSpanBy H C
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨hHel,hHcard,hHQ⟩ := intrinsicFour_properties_of_MS93 d c.L b t common earlier
  let : IsElementaryAbelian 2 H := hHel
  have hQN := (binary_three_source_a7_core_stabilizer
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK a).1
  have hHN : H ≤ N := (hHQ.trans inf_le_left).trans hQN
  have hNC : N ≤ C := C.pCoreIn_le 2
  have hHC : H ≤ C := hHN.trans hNC
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hNJ : N ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 C) (hNS.trans le_sup_right) (hLS.trans hCN)
  have hZH : Z ≤ H := zpowers_le.mpr hzH
  have hCZ : C ≤ centralizer (Z : Set G) := by
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hCZN : C ≤ normalizer Z := hCZ.trans (Subgroup.centralizer_le_normalizer _)
  have hdisp := binary_three_source_original_displacement_eq_fixedLine
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier
  have hpoint : ⁅H,J.pCoreIn 2⁆ = Z := by
    symm
    apply eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      rw [hdisp.1]
      exact ⟨hzH,fun s hs => mem_centralizer_singleton_iff.mp (hLS (mem_sup_right hs))⟩
    · rw [Nat.card_zpowers,hz2,hdisp.2]
  have hHNcomm : ⁅H,N⁆ ≤ Z := (commutator_mono le_rfl hNJ).trans hpoint.le
  have hUN : U ≤ N := conjugateSpanBy_le hHN hCN
  have hUC : U ≤ C := hUN.trans hNC
  have hCU : C ≤ normalizer U := le_normalizer_conjugateSpanBy H C
  have hUNcomm : ⁅U,N⁆ ≤ Z := by
    rw [commutator_conjugateSpanBy_of_normalized_right H C N hHC hCN]
    exact conjugateSpanBy_le hHNcomm hCZN
  have hZU : Z ≤ U := hZH.trans (le_conjugateSpanBy H C)
  have hn : (Z.subgroupOf U).Normal :=
    (normal_subgroupOf_iff_le_normalizer hZU).mpr (hUC.trans hCZN)
  let := hn
  have hderived : _root_.commutator U ≤ Z.subgroupOf U := by
    intro x hx
    have hm : (_root_.commutator U).map U.subtype = ⁅U,U⁆ := by
      rw [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    exact ((commutator_mono le_rfl hUN).trans hUNcomm)
      (hm ▸ mem_map_of_mem U.subtype hx)
  let : IsMulCommutative (U ⧸ Z.subgroupOf U) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hderived
  have hel : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U) :=
    conjugateSpan_quotient_elementary 2 H C Z
  have hi : Z.relIndex H = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) Z H bot_le hZH
    rw [relIndex_bot_left,relIndex_bot_left,Nat.card_zpowers,hz2,hHcard] at hh
    omega
  obtain ⟨act,hact⟩ := exists_quotient_conjugation_action C U Z hCU hCZN hn
  have hkill : N.subgroupOf C ≤ act.ker :=
    quotient_conjugation_action_kills_commutator_layer C U Z N hn hCU hUNcomm act hact
  let q := QuotientGroup.mk' (pCore 2 C)
  have hk : q.ker ≤ act.ker := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hkill (mem_map_of_mem C.subtype hx)
  let ρ := q.liftOfSurjective (QuotientGroup.mk'_surjective _) ⟨act,hk⟩
  have hρ (x : C) : ρ (q x) = act x := by simp [ρ,MonoidHom.liftOfSurjective]
  refine ⟨hZH,hi,le_conjugateSpanBy H C,hUN,hCU,hUNcomm,hn,hel,ρ,?_⟩
  intro x u v hv
  rw [hρ,hact]
  congr 1
  exact Subtype.ext hv.symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
