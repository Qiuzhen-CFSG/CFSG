module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanKernelCentralizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanCentralizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanNormalizerCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointPhiKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanOutside

/-!
# The original component action on the normalizer-core center

The middle core has center Phi(Q), and the normalizer core centralizes
Phi(Q). This identifies its centralizer inside Q exactly. Relative core
containment in LS and original commutator generation then show that L
moves the full center of the normalizer core onto exactly Phi(Q).
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The full center of the fixed-span normalizer core meets the original
core in Phi and has precisely Phi as its L-commutator. -/
theorem binary_three_source_fixed_span_core_center
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
    let U := conjugateSpanBy (intrinsicFour c.L) C
    let F := (normalizer (U : Set G)).pCoreIn 2
    let ZF := (center F).map F.subtype
    let Q := LinearThree.commutatorCore c.L
    Q ⊓ centralizer (F : Set G) = frattiniIn Q ∧
      ZF ⊓ Q = frattiniIn Q ∧ ⁅ZF,c.L⁆ = frattiniIn Q := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let A := normalizer (U : Set G)
  let F := A.pCoreIn 2
  let ZF := (center F).map F.subtype
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  have hF : F = N ⊓ centralizer (U : Set G) :=
    binary_three_source_fixed_span_normalizer_core
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  have hFQ : F ⊓ Q = D := by
    rw [hF]
    exact (binary_three_source_fixed_span_kernel_centralizer
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm).2.2.2.1
  have hDF : D ≤ F := hFQ.symm.le.trans inf_le_left
  have hDPhi : (center D).map D.subtype = Phi :=
    (binary_three_large_distance_original_middle_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).1
  have hPhiD : Phi ≤ D := hDPhi.symm.le.trans (map_subtype_le _)
  have hPhiF : Phi ≤ F := hPhiD.trans hDF
  have hPhiQ : Phi ≤ Q := map_subtype_le _
  have hFfix : F ≤ centralizer (Phi : Set G) :=
    (hF.le.trans inf_le_right).trans
      (binary_three_source_fixed_span_centralizer
        hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
          K hK hKn hLK eB hrX hrB hm).2
  have hPhiZ : Phi ≤ ZF := by
    intro x hx
    exact ⟨⟨x,hPhiF hx⟩,mem_center_iff.mpr
      (fun y => Subtype.ext ((hFfix y.property) x hx).symm),rfl⟩
  have hQcent : Q ⊓ centralizer (F : Set G) = Phi := by
    apply le_antisymm
    · intro x hx
      have hxD : x ∈ D := ⟨hx.1,(centralizer_le hPhiF) hx.2⟩
      have hxZ : x ∈ (center D).map D.subtype :=
        ⟨⟨x,hxD⟩,mem_center_iff.mpr
          (fun y => Subtype.ext (hx.2 y (hDF y.property))),rfl⟩
      exact hDPhi.le hxZ
    · exact le_inf hPhiQ (le_centralizer_iff.mp hFfix)
  have hZfix : ZF ≤ centralizer (F : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hZQ : ZF ⊓ Q = Phi := le_antisymm
    ((le_inf inf_le_right (inf_le_left.trans hZfix)).trans hQcent.le)
    (le_inf hPhiZ hPhiQ)
  have hout := binary_three_source_fixed_span_outside
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hLA : c.L ≤ A := le_sup_left.trans hout.2.1
  have hAF : A ≤ normalizer (F : Set G) := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hLZ : c.L ≤ normalizer (ZF : Set G) := hLA.trans
    (hAF.trans (normalizer_le_normalizer_characteristic_image F (center F)))
  obtain ⟨S,hS⟩ := hout.2.2.2.1
  have hFS : F ≤ d.S := hS ▸ pCoreIn_le_sylow A S
  have hFJ : F ≤ c.L ⊔ d.S := hFS.trans le_sup_right
  have hFcore : F ≤ (c.L ⊔ d.S).pCoreIn 2 := by
    apply (le_inf hFJ (show F ≤ A.pCoreIn 2 from le_rfl)).trans
    exact inf_pCoreIn_le_of_le 2 hout.2.1
  have hSL : d.S ≤ normalizer (c.L : Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (show c.L ≤ c.L ⊔ d.S from le_sup_left)).mp b.component_normal)
  have hZLQ : ⁅ZF,c.L⁆ ≤ Q :=
    (commutator_mono ((map_subtype_le _).trans hFcore) le_rfl).trans
      (overgroup_core_commutator_le d c hSL)
  have hZLPhi : ⁅ZF,c.L⁆ ≤ Phi :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp hLZ) hZLQ).trans hZQ.le
  have hroot := (binary_three_large_distance_original_core_structure
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.2.2.1
  have hPhi : Phi = ⁅Q,Q⁆ := by
    dsimp only [Phi,frattiniIn]
    rw [←hroot,_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  have hPhiL : ⁅Phi,c.L⁆ = Phi := by
    rw [hPhi]
    exact binary_three_large_distance_original_derived_full_commutation
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  exact ⟨hQcent,hZQ,le_antisymm hZLPhi
    (hPhiL.symm.le.trans (commutator_mono hPhiZ le_rfl))⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
