module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpan
public import Theory.Frattini.Intersection
public import Theory.Frattini.QuadraticCentralizer
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# The actual A7 fixed-four span inside the point Frattini subgroup

The original four is the third lower-central subgroup of Q, so it lies
in Phi(Q). In the A7 row Q lies in the actual point kernel N. Frattini
functoriality and C-invariance therefore put U=span_C(H) inside Phi(N).
The literal bound [U,N]<=<z>, with z fixed by C, makes Phi(N) centralize U.
Consequently U itself is elementary abelian. This locates the surviving
invariant layer inside the Frattini kernel; it does not claim that its
image on N/Phi(N) survives or that the A7 carrier is excluded.

Source: Aschbacher--Smith15.3.23, pp.1128--1129, with the original
intrinsic-four displacement and finite two-group Frattini functoriality.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The original four's full point-centralizer span is an elementary subgroup
of the center of the point kernel's Frattini subgroup. -/
theorem binary_three_source_a7_frattini_span
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
    let U := conjugateSpanBy (intrinsicFour c.L) C
    let Phi := (frattini N).map N.subtype
    U ≤ Phi ∧ U ≤ centralizer (Phi : Set G) ∧ IsElementaryAbelian 2 U := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let H := intrinsicFour c.L
  let Z := zpowers z
  let U := conjugateSpanBy H C
  let Phi := (frattini N).map N.subtype
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨hHel,_,_⟩ := intrinsicFour_properties_of_MS93 d c.L b t common earlier
  let : IsElementaryAbelian 2 H := hHel
  have hQN := (binary_three_source_a7_core_stabilizer
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK a).1
  have hspan := binary_three_source_a7_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK a
  have hUNcomm : ⁅U,N⁆ ≤ Z := hspan.2.2.2.2.2.1
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hCPhi : C ≤ normalizer Phi := hCN.trans
    (normalizer_le_normalizer_characteristic_image N (frattini N))
  have hNp : IsPGroup 2 N := isPGroup_pCoreIn 2 C
  let : Fact (IsPGroup 2 Q) := ⟨hNp.to_le hQN⟩
  have hHder : H ≤ ⁅Q,Q⁆ :=
    le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_left Q Q)
  have hHphi : H ≤ (frattini Q).map Q.subtype := by
    apply hHder.trans
    rw [← map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hUPhi : U ≤ Phi := conjugateSpanBy_le
    (hHphi.trans (frattini_image_le_of_le hQN hNp)) hCPhi
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_injective
    (inclusion (show Z ≤ H from zpowers_le.mpr hzH)) (inclusion_injective _)
  have hCZ : C ≤ centralizer (Z : Set G) := by
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hPhiU : Phi ≤ centralizer (U : Set G) :=
    frattini_image_le_centralizer_of_elementary_commutator N U Z hNp
      (by simpa only [commutator_comm N U] using hUNcomm)
      ((pCoreIn_le 2 C).trans hCZ)
  have hUPhiC : U ≤ centralizer (Phi : Set G) := le_centralizer_iff.mp hPhiU
  let : IsMulCommutative U := le_centralizer_iff_isMulCommutative.mp (hUPhi.trans hPhiU)
  exact ⟨hUPhi,hUPhiC,conjugateSpanBy_elementary_of_commutative H C⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
