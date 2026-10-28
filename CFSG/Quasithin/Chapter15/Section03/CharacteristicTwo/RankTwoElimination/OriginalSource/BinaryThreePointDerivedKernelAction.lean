module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointNaturalDerivedSpan
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointPhiAction
public import Theory.ThreeSubgroups

/-!
# The original point-derived kernel has central Frattini displacement

The original point kernel moves Phi(Q) into H, and moves H only into the
point line Z. The latter is fixed by the whole point centralizer. The
relative three-subgroup identity consequently bounds [N',Phi] by Z and
makes N' centralize H. A further rotation places [N',Q] in the actual
middle core D. The second derived subgroup centralizes Phi outright.
The full point kernel is retained; no containment N'≤Q is asserted.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The actual derived point kernel centralizes H and acts on Q through its middle core. -/
theorem binary_three_source_natural_derived_kernel_action
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
    let E := ⁅N,N⁆
    let Q := LinearThree.commutatorCore c.L
    let Phi := frattiniIn Q
    let H := intrinsicFour c.L
    let Z := zpowers z
    let D := Q ⊓ centralizer (Phi : Set G)
    ⁅E,H⁆ = ⊥ ∧ ⁅E,Phi⁆ ≤ Z ∧ ⁅E,Q⁆ ≤ D ∧
      ⁅⁅E,E⁆,Phi⁆ = ⊥ ∧ ⁅E,E⁆ ⊓ Q ≤ D := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let E := ⁅N,N⁆
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let H := intrinsicFour c.L
  let Z := zpowers z
  let D := Q ⊓ centralizer (Phi : Set G)
  have hNC : N ≤ C := C.pCoreIn_le 2
  have hEN : E ≤ N := commutator_le_self N
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hQL : Q ≤ c.L := (LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)
  have hQC : Q ≤ C := hQL.trans hLC
  have hPhiC : Phi ≤ C := (map_subtype_le (frattini Q)).trans hQC
  have hZC : Z ≤ centralizer (C : Set G) := by
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hCZ : C ≤ normalizer Z :=
    (le_centralizer_iff.mp hZC).trans (Subgroup.centralizer_le_normalizer _)
  have hNZ : N ≤ normalizer Z := hNC.trans hCZ
  have hZQ : ⁅Z,Q⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hZC.trans (centralizer_le hQC))
  have hZN : ⁅Z,N⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hZC.trans (centralizer_le hNC))
  have hZE : ⁅Z,E⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hZC.trans (centralizer_le (hEN.trans hNC)))
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
  have hspan := binary_three_source_binary_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hz hz2 hLS P hP K hBK (Or.inl rfl) hm
  have hHN : ⁅H,N⁆ ≤ Z := (commutator_mono hspan.2.2.1 le_rfl).trans hspan.2.2.2.2.2.1
  have hNPhi : ⁅N,Phi⁆ ≤ H := (binary_three_source_point_phi_action
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP).2
  have hNHN : ⁅⁅N,H⁆,N⁆ = ⊥ := by
    rw [commutator_comm N H]
    exact le_bot_iff.mp ((commutator_mono hHN le_rfl).trans hZN.le)
  have hEH : ⁅E,H⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hNHN
    (by rwa [commutator_comm H N])
  have hPhiN : ⁅Phi,N⁆ ≤ H := by rwa [commutator_comm]
  have hEPhi : ⁅E,Phi⁆ ≤ Z :=
    commutator_commutator_le_of_rotate_of_le_normalizer hNZ hNZ (hPhiC.trans hCZ)
      ((commutator_mono hNPhi le_rfl).trans hHN)
      ((commutator_mono hPhiN le_rfl).trans hHN)
  have hroot : _root_.commutator Q = frattini Q :=
    (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.2.2.1
  have hPhi : Phi = ⁅Q,Q⁆ := by
    dsimp only [Phi,frattiniIn]
    rw [←hroot,_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  have hQPhi : ⁅Q,Phi⁆ = H := by rw [hPhi,commutator_comm]; rfl
  have hEQPhi : ⁅⁅E,Q⁆,Phi⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (by rw [hQPhi,commutator_comm]; exact hEH)
      (by
        rw [commutator_comm Phi E]
        exact le_bot_iff.mp ((commutator_mono hEPhi le_rfl).trans hZQ.le))
  have hJL : c.L ⊔ d.S ≤ normalizer c.L :=
    (normal_subgroupOf_iff_le_normalizer (show c.L ≤ c.L ⊔ d.S from le_sup_left)).mp
      b.component_normal
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hNQ : N ≤ normalizer Q := ((hNS.trans le_sup_right).trans hJL).trans
    (normalizer_le_normalizer_commutatorCore c.L)
  have hEQ : ⁅E,Q⁆ ≤ D := le_inf
    (le_normalizer_iff_commutator_le_right.mp (hEN.trans hNQ))
    (commutator_eq_bot_iff_le_centralizer.mp hEQPhi)
  have hE'E : ⁅⁅E,E⁆,Phi⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (le_bot_iff.mp ((commutator_mono hEPhi le_rfl).trans hZE.le))
      (by
        rw [commutator_comm Phi E]
        exact le_bot_iff.mp ((commutator_mono hEPhi le_rfl).trans hZE.le))
  exact ⟨hEH,hEPhi,hEQ,hE'E,le_inf inf_le_right
    (inf_le_left.trans (commutator_eq_bot_iff_le_centralizer.mp hE'E))⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
