module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanKernelIndex
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreImage

/-!
# The full fixed-span kernel is intrinsic to the span

The centralizer of U lies in C_G(z), because z belongs to U, and is normal
there. Its two-core is therefore exactly C_N(U). This identifies the full
kernel intrinsically, so the whole normalizer of U normalizes it. The
original elementary U lies in this kernel, which is nontrivial.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original full fixed-span action kernel is the intrinsic two-core
of the full span centralizer; its normalizer contains the span normalizer. -/
theorem binary_three_source_fixed_span_canonical_kernel
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
    let F := N ⊓ centralizer (U : Set G)
    F = (centralizer (U : Set G)).pCoreIn 2 ∧
      normalizer (U : Set G) ≤ normalizer (F : Set G) ∧ U ≤ F ∧ F ≠ ⊥ := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let N := C.pCoreIn 2
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let F := N ⊓ centralizer (U : Set G)
  let CU := centralizer (U : Set G)
  have hzU : z ∈ U := le_conjugateSpanBy _ C hzH
  have hCUC : CU ≤ C := centralizer_le (Set.singleton_subset_iff.mpr hzU)
  have hCCU : C ≤ normalizer CU :=
    (le_normalizer_conjugateSpanBy _ C).trans (normalizer_le_normalizer_centralizer U)
  have hcanonical : F = CU.pCoreIn 2 := by
    apply le_antisymm
    · change N ⊓ CU ≤ CU.pCoreIn 2
      rw [inf_comm]
      exact inf_pCoreIn_le_of_le 2 hCUC
    · exact le_inf (pCoreIn_mono_of_normalizes hCUC hCCU) (CU.pCoreIn_le 2)
  have hnormal : normalizer (U : Set G) ≤ normalizer (F : Set G) := by
    rw [hcanonical]
    exact (normalizer_le_normalizer_centralizer U).trans
      (normalizer_le_normalizer_characteristic_image CU (pCore 2 CU))
  let := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  have hUN : U ≤ N := (binary_three_source_binary_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK (Or.inl rfl) hm).2.2.2.1
  let : IsElementaryAbelian 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  have hUF : U ≤ F := le_inf hUN (le_centralizer U)
  have hnon : F ≠ ⊥ := by
    intro he
    have hz1 : z = 1 := he.le (hUF hzU)
    rw [hz1,orderOf_one] at hz2
    norm_num at hz2
  exact ⟨hcanonical,hnormal,hUF,hnon⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
