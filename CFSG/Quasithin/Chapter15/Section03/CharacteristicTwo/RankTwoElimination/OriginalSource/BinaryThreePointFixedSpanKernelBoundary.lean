module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanOrder
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourPhiCentralizer

/-!
# The exact fixed subgroup and displacement of the original point kernel

The original fixed span U has order 32 and lies in Phi(Q). The actual
centralizer theorem bounds its N-fixed subgroup by H. Since that fixed
subgroup is C-invariant and contains the point line Z, its index-two
placement in H forces it to be Z: otherwise its C-span would be all U
inside H. Consequently the original kernel displacement is exactly Z.
The full point kernel is retained, and its action is not assumed trivial.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The point kernel fixes exactly the point line in U and has precisely that displacement. -/
theorem binary_three_source_fixed_span_kernel_boundary
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
    let Z := zpowers z
    U ⊓ centralizer (N : Set G) = Z ∧ ⁅U,N⁆ = Z := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let H := intrinsicFour c.L
  let ZQ := coreCenter c.L
  let U := conjugateSpanBy H C
  let Z := zpowers z
  let A := U ⊓ centralizer (N : Set G)
  let := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  have hUcard : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hUPhi : U ≤ Phi := (binary_three_source_fixed_span_frattini
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK hm).2
  have hUZ : U ⊓ ZQ = H := (binary_three_source_fixed_span_center_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK hm).2.1
  obtain ⟨hZH,hZHindex,hHU,_,hCU,hUNcomm,_⟩ := binary_three_source_binary_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK (Or.inl rfl) hm
  have hPhiN := (binary_three_source_four_phi_centralizer
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
      (K.map q) hBK hm).2.2.2 A (show A ≤ centralizer (N : Set G) from inf_le_right)
  have hAPhi : A ≤ Phi := inf_le_left.trans hUPhi
  have hAZQ : A ≤ ZQ := by
    rw [inf_eq_left.mpr hAPhi] at hPhiN
    exact hPhiN
  have hAH : A ≤ H := (le_inf inf_le_left hAZQ).trans hUZ.le
  have hZC : Z ≤ centralizer (C : Set G) := by
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hZA : Z ≤ A := le_inf (hZH.trans hHU)
    (hZC.trans (centralizer_le (C.pCoreIn_le 2)))
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hCA : C ≤ normalizer A := (le_inf hCU
    (hCN.trans (normalizer_le_normalizer_centralizer N))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hHcard : Nat.card H = 4 :=
    (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.1
  have hAHne : A.relIndex H ≠ 1 := by
    intro he
    have hHA : H ≤ A := relIndex_eq_one.mp he
    have hUH : U ≤ H := (conjugateSpanBy_le hHA hCA).trans hAH
    have hbound := card_le_of_le hUH
    rw [hUcard,hHcard] at hbound
    omega
  have hAHindex : A.relIndex H = 2 := by
    have hd : A.relIndex H ∣ 2 := hZHindex ▸ relIndex_dvd_of_le_left H hZA
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hAHne
  have hZAindex : Z.relIndex A = 1 := by
    have hi := relIndex_mul_relIndex Z A H hZA hAH
    rw [hZHindex,hAHindex] at hi
    omega
  have hAZ : A = Z := le_antisymm (relIndex_eq_one.mp hZAindex) hZA
  have hZcard : Nat.card Z = 2 := by rw [Nat.card_zpowers,hz2]
  have hcommne : ⁅U,N⁆ ≠ ⊥ := by
    intro he
    have hUA : U ≤ A := le_inf le_rfl (commutator_eq_bot_iff_le_centralizer.mp he)
    have hbound := card_le_of_le (hUA.trans hAZ.le)
    rw [hUcard,hZcard] at hbound
    omega
  have hcommcard : Nat.card (⁅U,N⁆ : Subgroup G) = 2 := by
    have hd : Nat.card (⁅U,N⁆ : Subgroup G) ∣ 2 := hZcard ▸ card_dvd_of_le hUNcomm
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact (hcommne ((eq_bot_iff_card _).mpr h1)).elim
    · exact h2
  exact ⟨hAZ,eq_of_le_of_card_ge hUNcomm (by rw [hZcard,hcommcard])⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
