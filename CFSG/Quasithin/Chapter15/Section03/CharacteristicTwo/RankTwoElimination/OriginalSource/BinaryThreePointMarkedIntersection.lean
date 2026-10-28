module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanJoinAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointIntermediateMarkedParabolic
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry

/-!
# The original intersection is the actual marked parabolic

In the promoted Sylow join J, the intersection with original I induces the
full stabilizer of original H. The action kernel is the two-core of J and
lies in the original Sylow subgroup, hence in I. The intersection is thus
exactly J intersect N(H), a proper outside characteristic-two subgroup of J
contained in the original I.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

private theorem marked_four_not_preserved_by_all
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (H : Subgroup E) (hH : Nat.card H = 4) :
    ¬ ∀ f : MulAut E, ∀ x : E, f x ∈ H ↔ x ∈ H := by
  let W : Submodule (ZMod 2) (Additive E) := AddSubgroup.toZModSubmodule 2 H.toAddSubgroup
  let w : W ≃ H :=
    { toFun x := ⟨x.val.toMul,x.property⟩
      invFun x := ⟨Additive.ofMul x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hWcard : Nat.card W = 4 := (Nat.card_congr w).trans hH
  have hEdim : Module.finrank (ZMod 2) (Additive E) = 5 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hh
    simpa only [Nat.card_zmod,hE] using hh.symm
  have hWdim : Module.finrank (ZMod 2) W = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    simpa only [Nat.card_zmod,hWcard] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)).symm
  have hW0 : W ≠ ⊥ := by
    apply Submodule.nontrivial_iff_ne_bot.mp
    exact Finite.one_lt_card_iff_nontrivial.mp (by rw [hWcard]; decide)
  have hW1 : W ≠ ⊤ := by
    intro hh
    have hd : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) (Additive E) := by
      rw [hh,finrank_top]
    omega
  intro hall
  apply BinaryLinear.FourParabolicAction.parabolic_ne_top hW0 hW1
  apply eq_top_iff.mpr
  intro g _
  let e : MulAut E ≃* BinaryLinear.GL (Additive E) := BinaryFixedLine.linearAutEquiv
  obtain ⟨f,rfl⟩ := e.surjective g
  intro x
  exact hall f x.toMul

/-- Original I intersects the same promoted Sylow join in precisely the
marked H-parabolic. It is proper in that join and lies in original I. -/
theorem binary_three_source_marked_intersection
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
    let H := intrinsicFour c.L
    let U := conjugateSpanBy H (centralizer ({z} : Set G))
    let A := normalizer (U : Set G)
    ∃ D : Subgroup A, D.IsCComponent ∧ D.Normal ∧ c.L.subgroupOf A ≤ D ∧
      let J := D.map A.subtype ⊔ d.S
      I ⊓ J = J ⊓ normalizer (H : Set G) ∧ I ⊓ J < J ∧
      I ⊓ J ∈ d.Hplus ∧ HasCharacteristicTwo (I ⊓ J) ∧
      Chapter1.IsSylowIn 2 d.S (I ⊓ J) ∧ d.Yplus ⊔ d.S ≤ I ⊓ J := by
  let H := intrinsicFour c.L
  let U := conjugateSpanBy H (centralizer ({z} : Set G))
  let A := normalizer (U : Set G)
  obtain ⟨D,hD,hDn,hLD,hJ,hSJ,hchar,hYB,hJA,hfull,hker⟩ :=
    binary_three_source_fixed_span_join_action
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  let B := D.map A.subtype
  let J := B ⊔ d.S
  let T := I ⊓ J
  let f : J →* MulAut U := U.normalizerMonoidHom.comp (inclusion hJA)
  have hTI : T ≤ I := inf_le_left
  have hTJ : T ≤ J := inf_le_right
  have hSI : d.S ≤ I := le_sup_right.trans hI.1.2
  have hST : d.S ≤ T := le_inf hSI le_sup_right
  have hYT : d.Yplus ≤ T := le_inf (le_sup_left.trans hI.1.2)
    (hYB.trans le_sup_left)
  have hIU : I ≤ A := (binary_three_source_fixed_span_strict_overgroup
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1.le
  have hLB : c.L ≤ B := by
    intro x hx
    exact ⟨⟨x,hIU (component_le c hx)⟩,hLD hx,rfl⟩
  have hLT : c.L ≤ T := le_inf (component_le c) (hLB.trans le_sup_left)
  obtain ⟨hTU,hTH,himage⟩ := binary_three_source_intermediate_marked_parabolic
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm T hTI hLT hYT hST
  have hcoreS : J.pCoreIn 2 ≤ d.S := by
    obtain ⟨P,hP⟩ := hSJ
    exact (pCoreIn_le_sylow J P).trans_eq hP
  have hkernelT (x : J) (hx : x ∈ f.ker) : (x : G) ∈ T :=
    hST (hcoreS ⟨x,hker ▸ hx,rfl⟩)
  have heq : T = J ⊓ normalizer (H : Set G) := by
    apply le_antisymm (le_inf hTJ hTH)
    rintro x ⟨hxJ,hxH⟩
    let xJ : J := ⟨x,hxJ⟩
    have him : f xJ ∈ (U.normalizerMonoidHom.comp (inclusion hTU)).range :=
      (himage (f xJ)).mpr (fun u => (mem_normalizer_iff.mp hxH (u : G)).symm)
    obtain ⟨t,ht⟩ := him
    let tJ : J := inclusion hTJ t
    have hk : tJ⁻¹ * xJ ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      have ht' : f tJ = f xJ := ht
      rw [map_mul,map_inv,ht',inv_mul_cancel]
    have hm := T.mul_mem t.property (hkernelT _ hk)
    change (t : G) * ((t : G)⁻¹ * x) ∈ T at hm
    simpa only [mul_inv_cancel_left] using hm
  let : IsElementaryAbelian 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  have hUcard : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hHU : H ≤ U := le_conjugateSpanBy H _
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hHcard : Nat.card (H.subgroupOf U) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hHU).toEquiv).trans
      (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.1
  have hnot : ¬ J ≤ normalizer (H : Set G) := by
    intro hh
    apply marked_four_not_preserved_by_all U hUcard (H.subgroupOf U) hHcard
    intro g u
    obtain ⟨x,rfl⟩ := hfull g
    exact (mem_normalizer_iff.mp (hh x.property) (u : G)).symm
  have hlt : T < J := lt_of_le_not_ge hTJ (fun hh => hnot (hh.trans hTH))
  have hTHplus : T ∈ d.Hplus := d.mem_Hplus_of_intermediate hJ hSJ hTJ
    (sup_le hYT hST) (fun hh => c.outside (hLT.trans hh))
  exact ⟨D,hD,hDn,hLD,heq,hlt,hTHplus,
    characteristicTwo_of_sylow_overgroup hSJ hTJ hST hchar,
    hSJ.restrict hST hTJ,sup_le hYT hST⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
