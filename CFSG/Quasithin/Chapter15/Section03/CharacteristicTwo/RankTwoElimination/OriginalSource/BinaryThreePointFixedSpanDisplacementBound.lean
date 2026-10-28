module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanMiddleIntersection

/-!
# A bound for the displacement of the original fixed-four span

The original middle core D has index eight in R=Q intersection N. The
checked intersection [U,L] intersection D lies in Phi(Q), of order256.
Thus the actual displacement has order at most2048. Both the full original
point kernel and the middle denominator are retained in the index bound.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original fixed-four span has at most eleven binary dimensions of L-displacement. -/
theorem binary_three_source_fixed_span_displacement_bound
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
    (hm : ClassicalGroup.IsPSL K 4 2)
    (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let Q := LinearThree.commutatorCore c.L
    let Phi := frattiniIn Q
    let D := Q ⊓ centralizer (Phi : Set G)
    let R := Q ⊓ N
    let U := conjugateSpanBy (intrinsicFour c.L) C
    D.relIndex R = 8 ∧ (⁅U,c.L⁆ ⊓ D).relIndex ⁅U,c.L⁆ ≤ 8 ∧
      Nat.card (⁅U,c.L⁆ ⊓ D : Subgroup G) ≤ 256 ∧ Nat.card (⁅U,c.L⁆ : Subgroup G) ≤ 2048 := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let R := Q ⊓ N
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let T := ⁅U,c.L⁆
  obtain ⟨_,hTR,hTD⟩ := binary_three_source_fixed_span_middle_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hz hz1
  have hDN : D ≤ N := binary_three_source_natural_middle_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hz hz1
  have hDR : D ≤ R := le_inf inf_le_left hDN
  have hsizes := binary_three_large_distance_original_core_structure
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hPhicard : Nat.card Phi = 256 := by
    change Nat.card ((frattini Q).map Q.subtype) = 256
    rw [card_map_of_injective Q.subtype_injective]
    exact hsizes.2.2.1
  have hRcard : Nat.card R = 131072 := by
    have hh := (binary_three_source_binary_core_sizes
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK
      (Or.inl rfl) hm).2
    simpa only [Nat.reduceSub,Nat.reduceMul,Nat.reducePow] using hh
  obtain ⟨a,_,_,ht⟩ := binary_three_large_distance_original_core_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hDcard : Nat.card D = 16384 := by
    obtain ⟨_,_,_,hn,ev,_⟩ := ht
    let := hn
    have hquot : Nat.card (Q ⧸ D.subgroupOf Q) = 64 := by
      rw [Nat.card_congr ev.toEquiv]
      change Nat.card ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) = 64
      rw [Nat.card_prod]
      have h8 : Nat.card (Fin 3 → ZMod 2) = 8 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Module.finrank_pi,
          Fintype.card_fin,Nat.card_zmod]
        norm_num
      rw [h8]
    have hmul := card_eq_card_quotient_mul_card_subgroup (D.subgroupOf Q)
    have hD : Nat.card (D.subgroupOf Q) = Nat.card D :=
      Nat.card_congr (subgroupOfEquivOfLe (show D ≤ Q from inf_le_left)).toEquiv
    have hQ : Nat.card Q = 1048576 := hsizes.2.2.2.1
    rw [hQ,hquot,hD] at hmul
    omega
  have hindex : D.relIndex R = 8 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) D R bot_le hDR
    rw [relIndex_bot_left,relIndex_bot_left,hDcard,hRcard] at hh
    omega
  have hTindex : (T ⊓ D).relIndex T ≤ 8 := by
    rw [inf_relIndex_left]
    exact (relIndex_le_of_le_right hTR (by rw [hindex]; decide)).trans_eq hindex
  have hTcard : Nat.card (T ⊓ D : Subgroup G) ≤ 256 :=
    (card_le_of_le hTD).trans_eq hPhicard
  have hbound : Nat.card T ≤ 2048 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (T ⊓ D) T bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left] at hh
    rw [←hh]
    exact (Nat.mul_le_mul hTcard hTindex).trans_eq (by decide)
  exact ⟨hindex,hTindex,hTcard,hbound⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
