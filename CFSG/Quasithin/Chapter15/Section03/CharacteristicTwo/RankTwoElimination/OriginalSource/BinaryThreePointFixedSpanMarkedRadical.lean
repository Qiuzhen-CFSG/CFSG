module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanOvergroup
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanCentralizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalCoreSections
public import Theory.GroupAction.ElementaryFiveMarkedRadical

/-!
# The original core induces the marked 2+3 radical

The full centralizer of U centralizes the original Frattini subgroup Phi.
Consequently the literal action kernel in Q is C_Q(Phi), and the original
six-dimensional section gives an image of order64. It fixes the original
four H pointwise and has all displacements in H, so it is the full radical
at that same H. Its normalizer is exactly the H stabilizer. Original I
preserves this marking through normality of its original component L.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original Q induces precisely the full radical fixing H pointwise
and acting trivially on U/H, with its original kernel and marking retained. -/
theorem binary_three_source_fixed_span_marked_radical
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
    let Q := LinearThree.commutatorCore c.L
    let H := intrinsicFour c.L
    let U := conjugateSpanBy H (centralizer ({z} : Set G))
    I ≤ normalizer (U : Set G) ∧ I ≤ normalizer (H : Set G) ∧
      ∃ hQU : Q ≤ normalizer (U : Set G),
        let a := U.normalizerMonoidHom.comp (inclusion hQU)
        a.ker = (Q ⊓ centralizer (frattiniIn Q : Set G)).subgroupOf Q ∧
        Nat.card a.range = 64 ∧ U ⊓ centralizer (Q : Set G) = H ∧
        (∀ f : MulAut U, f ∈ a.range ↔
          (∀ x : U, (x : G) ∈ H → f x = x) ∧
          ∀ x : U, (f x : G) * (x : G)⁻¹ ∈ H) ∧
        (∀ f : MulAut U, f ∈ normalizer (a.range : Set (MulAut U)) ↔
          ∀ x : U, (f x : G) ∈ H ↔ (x : G) ∈ H) := by
  let Q := LinearThree.commutatorCore c.L
  let H := intrinsicFour c.L
  let U := conjugateSpanBy H (centralizer ({z} : Set G))
  let A := normalizer (U : Set G)
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  have hIA : I ≤ A := (binary_three_source_fixed_span_strict_overgroup
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1.le
  have hQL : Q ≤ c.L := (LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)
  have hQU : Q ≤ A := hQL.trans ((component_le c).trans hIA)
  let a := U.normalizerMonoidHom.comp (inclusion hQU)
  have hHU : H ≤ U := le_conjugateSpanBy H _
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hHp := intrinsicFour_properties_of_MS93 d c.L b t common earlier
  have hHcard : Nat.card H = 4 := hHp.2.1
  have hHL : H ≤ centralizer (c.L : Set G) := hHp.2.2.trans inf_le_right
  have hprod := binary_three_source_fixed_span_frattini_product
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hprodPhi : Phi = U ⊔ coreCenter c.L := hprod.1
  have hprodComm : ⁅U,Q⁆ = H := hprod.2
  have hUPhi : U ≤ Phi := le_sup_left.trans hprodPhi.symm.le
  have hCU : centralizer (U : Set G) ≤ centralizer (Phi : Set G) :=
    (binary_three_source_fixed_span_centralizer
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).2
  have hker : a.ker = D.subgroupOf Q := by
    have ha : a.ker = (centralizer (U : Set G)).subgroupOf Q := by
      rw [←MonoidHom.comap_ker,normalizerMonoidHom_ker]
      rfl
    rw [ha]
    ext q
    exact ⟨fun hh => ⟨q.property,hCU hh⟩,
      fun hh => (centralizer_le hUPhi) hh.2⟩
  obtain ⟨_,_,_,hs⟩ := binary_three_large_distance_original_core_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  obtain ⟨_,_,_,hn,E,_⟩ := hs
  let := hn
  have hquot : Nat.card (Q ⧸ a.ker) = 64 := by
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv,
      Nat.card_congr E.toEquiv]
    simp
  have hcard : Nat.card a.range = 64 :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange a).toEquiv).symm.trans hquot
  let : IsElementaryAbelian 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  have hUcard : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hHUcard : Nat.card (H.subgroupOf U) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hHU).toEquiv).trans hHcard
  have hfix : ∀ f ∈ a.range, ∀ x ∈ H.subgroupOf U, f x = x := by
    rintro _ ⟨q,rfl⟩ x hx
    apply Subtype.ext
    change (q : G) * (x : G) * (q : G)⁻¹ = (x : G)
    have hcomm : (q : G) * (x : G) = (x : G) * (q : G) := hHL hx q (hQL q.property)
    rw [hcomm,mul_inv_cancel_right]
  have hdisp : ∀ f ∈ a.range, ∀ x : U, f x * x⁻¹ ∈ H.subgroupOf U := by
    rintro _ ⟨q,rfl⟩ x
    change ⁅(q : G),(x : G)⁆ ∈ H
    rw [←hprodComm,commutator_comm]
    exact commutator_mem_commutator q.property x.property
  have hmarked := MulAut.elementary_five_marked_radical hUcard (H.subgroupOf U)
    hHUcard a.range hcard hfix hdisp
  have hfixed : U ⊓ centralizer (Q : Set G) = H := by
    apply le_antisymm
    · rintro x ⟨hxU,hxQ⟩
      apply (hmarked.2.1 (⟨x,hxU⟩ : U)).mp
      rintro _ ⟨q,rfl⟩
      apply Subtype.ext
      change (q : G) * x * (q : G)⁻¹ = x
      rw [hxQ q q.property,mul_inv_cancel_right]
    · intro x hx
      exact ⟨hHU hx,(hHL.trans (centralizer_le hQL)) hx⟩
  have hSI : d.S ≤ I := le_sup_right.trans hI.1.2
  have hSyl := (OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI).sylow
  obtain ⟨D0,hD0,hD0n,hLD0,_⟩ := binary_three_source_outside_normal_component
    hG d c.L b I hI (sup_le (component_le c) hSI) hSyl
  have hcomp := LocalData.thompson_component_in c.le_thompson c.component
  have hDeq : c.L.subgroupOf I = D0 := hcomp.eq_of_le hD0 hLD0
  have hnormal : (c.L.subgroupOf I).Normal := hDeq.symm ▸ hD0n
  have hIL : I ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnormal
  have hIH : I ≤ normalizer (H : Set G) := hIL.trans (intrinsicFour_normalized c.L)
  exact ⟨hIA,hIH,hQU,hker,hcard,hfixed,hmarked.1,hmarked.2.2⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
