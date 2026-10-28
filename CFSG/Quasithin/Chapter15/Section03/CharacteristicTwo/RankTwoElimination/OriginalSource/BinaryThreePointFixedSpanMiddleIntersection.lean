module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalMiddleDerived
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointMiddleKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointBinaryFixedSpan

/-!
# The original fixed-four span meets the middle core only in Phi

For A=U intersection D, the commutator [A,D] lies in D'=V and in the
original point line inside H. The checked disjointness V intersection H=1
forces A to centralize D. Since Z(D)=Phi, the actual middle intersection is
U intersection Phi. The L-displacement of U therefore meets D only in Phi.
This is the source intersection needed by the original fifteen-coset cover.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The literal original U has no middle-core intersection above Phi(Q). -/
theorem binary_three_source_fixed_span_middle_intersection
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
    let U := conjugateSpanBy (intrinsicFour c.L) C
    U ⊓ D = U ⊓ Phi ∧ ⁅U,c.L⁆ ≤ Q ⊓ N ∧ ⁅U,c.L⁆ ⊓ D ≤ Phi := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let H := intrinsicFour c.L
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  let U := conjugateSpanBy H C
  let A := U ⊓ D
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  let : IsElementaryAbelian 2 H := (intrinsicFour_properties_of_MS93 d c.L b t common earlier).1
  have hz2 : orderOf z = 2 := by
    have ho : orderOf (⟨z,hz⟩ : H) = 2 := by
      apply orderOf_eq_prime
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 H) _
      · exact fun hh => hz1 (congrArg Subtype.val hh)
    exact (Subgroup.orderOf_coe (⟨z,hz⟩ : H)).trans ho
  obtain ⟨hZH,_,_,hUN,hCU,hcomm,_⟩ := binary_three_source_binary_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hz hz2 hLS P hP K hBK (Or.inl rfl) hm
  have hDN : D ≤ N := binary_three_source_natural_middle_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hz hz1
  have hderived : ⁅D,D⁆ = V := binary_three_large_distance_original_middle_derived
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hcenter : (center D).map D.subtype = Phi :=
    (binary_three_large_distance_original_middle_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).1
  have hPhiD : Phi ≤ D := hcenter.symm.le.trans (map_subtype_le _)
  have hVW : V ≤ W := le_conjugateSpanBy V C
  have hWH : W ⊓ H = ⊥ := (binary_three_source_four_fixed_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm).2
  have hAD : ⁅A,D⁆ = ⊥ := le_bot_iff.mp ((le_inf
    (((commutator_mono inf_le_right le_rfl).trans hderived.le).trans hVW)
    (((commutator_mono inf_le_left hDN).trans hcomm).trans hZH)).trans hWH.le)
  have hAc : A ≤ centralizer (D : Set G) := commutator_eq_bot_iff_le_centralizer.mp hAD
  have hAPhi : A ≤ Phi := by
    rw [←hcenter]
    intro x hx
    exact ⟨⟨x,hx.2⟩,mem_center_iff.mpr (fun y => Subtype.ext (hAc hx y y.property)),rfl⟩
  have hUinter : U ⊓ D = U ⊓ Phi :=
    le_antisymm (le_inf inf_le_left hAPhi) (inf_le_inf_left U hPhiD)
  have hNL : ⁅N,c.L⁆ = Q ⊓ N := (binary_three_source_binary_kernel_residual
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm).1
  have hmove : ⁅U,c.L⁆ ≤ Q ⊓ N := (commutator_mono hUN le_rfl).trans hNL.le
  have hmoveU : ⁅U,c.L⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp
    ((le_sup_left.trans hLS).trans hCU)
  exact ⟨hUinter,hmove,(inf_le_inf_right D hmoveU).trans hAPhi⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
