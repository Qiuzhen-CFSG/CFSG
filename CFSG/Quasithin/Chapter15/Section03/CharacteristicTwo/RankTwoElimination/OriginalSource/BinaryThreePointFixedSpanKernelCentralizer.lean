module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanFrattiniPairing
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointMiddleKernel
public import Theory.GroupTheory.CentralBinaryCentralizerCard

/-!
# The literal kernel of the point-core action on the fixed span

Let F=C_N(U), retaining the full point core N. The exact fixed-point line
and central binary pairing give |N:F|=16. Since Phi=UV and N fixes V,
F=C_N(Phi). Its intersection with the original core Q is precisely the
original middle core D. The subgroup F is invariant under the full point
centralizer C and contains N', without identifying N' or F with Q.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The full point-core action has order sixteen, with its original centralizer kernel. -/
theorem binary_three_source_fixed_span_kernel_centralizer
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
    let Q := LinearThree.commutatorCore c.L
    let Phi := frattiniIn Q
    let U := conjugateSpanBy (intrinsicFour c.L) C
    let F := N ⊓ centralizer (U : Set G)
    let D := Q ⊓ centralizer (Phi : Set G)
    C ≤ normalizer F ∧ ⁅N,N⁆ ≤ F ∧
      F = N ⊓ centralizer (Phi : Set G) ∧ F ⊓ Q = D ∧ F.relIndex N = 16 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let Z := zpowers z
  let F := N ⊓ centralizer (U : Set G)
  let D := Q ⊓ centralizer (Phi : Set G)
  let V := ⁅coreCenter c.L,c.L⁆
  let := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  have hz1 : z ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hz2
    norm_num at hz2
  have hpair := binary_three_source_fixed_span_frattini_pairing
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hprod : Phi = U ⊔ V := hpair.1
  have hUPhi : U ≤ Phi := le_sup_left.trans hprod.ge
  have hVcN : V ≤ centralizer (N : Set G) := (binary_three_source_point_central_eight
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP).2.2
  have hFphi : F = N ⊓ centralizer (Phi : Set G) := by
    apply le_antisymm
    · apply le_inf inf_le_left
      apply le_centralizer_iff.mp
      rw [hprod]
      exact sup_le (le_centralizer_iff.mp (show F ≤ centralizer (U : Set G) from inf_le_right))
        (hVcN.trans (centralizer_le inf_le_left))
    · exact inf_le_inf_left N (centralizer_le hUPhi)
  have hDN : D ≤ N := binary_three_source_natural_middle_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
      (K.map q) hBK hm hzH hz1
  have hFQ : F ⊓ Q = D := by
    rw [hFphi]
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf hDN inf_le_right) inf_le_left
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hCU : C ≤ normalizer U := le_normalizer_conjugateSpanBy _ _
  have hCF : C ≤ normalizer F := (le_inf hCN
    (hCU.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hEF : ⁅N,N⁆ ≤ F := by
    rw [hFphi]
    exact le_inf (commutator_le_self N)
      (commutator_eq_bot_iff_le_centralizer.mp hpair.2.2.2.2.1)
  obtain ⟨hUD,_⟩ := binary_three_source_fixed_span_frattini
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK hm
  let : IsMulCommutative U := le_centralizer_iff_isMulCommutative.mp
    ((hUD.trans inf_le_right).trans (centralizer_le hUPhi))
  let : IsMulCommutative Z := inferInstance
  obtain ⟨hfixed,hcomm⟩ := binary_three_source_fixed_span_kernel_boundary
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hZU : Z ≤ U := hfixed.ge.trans inf_le_left
  have hZC : Z ≤ centralizer (C : Set G) := by
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hZN : ⁅Z,N⁆ ≤ ⊥ := (commutator_eq_bot_iff_le_centralizer.mpr
    (hZC.trans (centralizer_le (C.pCoreIn_le 2)))).le
  have hZcard : Nat.card Z = 2 := by rw [Nat.card_zpowers,hz2]
  have hUcard : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hfixedCard : Nat.card ((centralizer (N : Set G)).subgroupOf U) = 2 := by
    have he : (centralizer (N : Set G)).subgroupOf U =
        (U ⊓ centralizer (N : Set G)).subgroupOf U := by
      ext u
      simp only [mem_subgroupOf,mem_inf,u.property,true_and]
    rw [he,Nat.card_congr (subgroupOfEquivOfLe
      (show U ⊓ centralizer (N : Set G) ≤ U from inf_le_left)).toEquiv,hfixed,hZcard]
  let F₀ := (centralizer (U : Set G)).subgroupOf N
  have hc := card_mul_card_centralizer_restrict_of_central_binary_pairing
    U N Z hZU hcomm.le hZN hZcard
  rw [hUcard,hfixedCard] at hc
  have hi := F₀.index_mul_card
  have hindex : F₀.index = 16 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card F₀ from Nat.card_pos)
    change 32 * Nat.card F₀ = Nat.card N * 2 at hc
    omega
  refine ⟨hCF,hEF,hFphi,hFQ,?_⟩
  change (N ⊓ centralizer (U : Set G)).relIndex N = 16
  rw [inf_relIndex_left]
  exact hindex

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
