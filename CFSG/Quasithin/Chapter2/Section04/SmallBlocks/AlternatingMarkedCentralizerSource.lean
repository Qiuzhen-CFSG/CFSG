module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingAffineMarkingSource
public import Theory.SpecificGroups.BinaryFiveAffine.MarkedCentralizerTransport
public import Theory.SpecificGroups.BinaryFiveAffine.ResidualCoreMarks
/-!
# The original marked alternating-five involution centralizer

The literal affine equivalence identifies Hᵤ with D₈ × S₄, its two-residual
with A₄, and the natural-module fixed subgroup with the marked four-group.
Two fixed vectors are conjugates of the original central involution under
the block. The product u z lies in the residual two-core and in the moved
module; two-perfect idempotence retains the latter's exact residual action.

Source: Aschbacher--Smith 2.4.29, printed pp.545--546.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

abbrev MinimalBlockSetup.affineInvolution (d : MinimalBlockSetup M) (eH : d.H ≃* BinaryFiveAffine.W) : G :=
  ((eH.symm BinaryFiveAffine.t : d.H) : G)
abbrev MinimalBlockSetup.affineCentralVector (d : MinimalBlockSetup M) (eH : d.H ≃* BinaryFiveAffine.W) : G :=
  ((eH.symm (SemidirectProduct.inl BinaryFiveAffine.centralSingular) : d.H) : G)
abbrev MinimalBlockSetup.affineFirstFixed (d : MinimalBlockSetup M) (eH : d.H ≃* BinaryFiveAffine.W) : G :=
  ((eH.symm (SemidirectProduct.inl BinaryFiveAffine.firstSingular) : d.H) : G)
abbrev MinimalBlockSetup.affineSecondFixed (d : MinimalBlockSetup M) (eH : d.H ≃* BinaryFiveAffine.W) : G :=
  ((eH.symm (SemidirectProduct.inl BinaryFiveAffine.secondSingular) : d.H) : G)
abbrev MinimalBlockSetup.affineCentralizer (d : MinimalBlockSetup M) (eH : d.H ≃* BinaryFiveAffine.W) : Subgroup G :=
  d.H ⊓ centralizer ({d.affineInvolution eH} : Set G)
abbrev MinimalBlockSetup.affineCentralizerResidual (d : MinimalBlockSetup M) (eH : d.H ≃* BinaryFiveAffine.W) : Subgroup G :=
  (pResidual 2 (d.affineCentralizer eH)).map (d.affineCentralizer eH).subtype
abbrev MinimalBlockSetup.affineResidualFixedFour (d : MinimalBlockSetup M) (eH : d.H ≃* BinaryFiveAffine.W) : Subgroup G :=
  sourceModule (d.block.map d.H.subtype) ⊓ centralizer (d.affineCentralizerResidual eH : Set G)

/-- The finite part of 2.4.29 with the original subgroup maps. -/
structure MinimalBlockSetup.MarkedA5CentralizerPacket (d : MinimalBlockSetup M)
    (eH : d.H ≃* BinaryFiveAffine.W) : Prop where
  product : Nonempty (d.affineCentralizer eH ≃* DihedralGroup 4 × Equiv.Perm (Fin 4))
  residual : Nonempty (pResidual 2 (d.affineCentralizer eH) ≃* alternatingGroup (Fin 4))
  card : Nat.card (d.affineCentralizer eH)=192
  not_two : ¬IsPGroup 2 (d.affineCentralizer eH)
  fixed_card : Nat.card (d.affineResidualFixedFour eH)=4
  fixed_members : ∀ w : G, w∈d.affineResidualFixedFour eH ↔
    w=1 ∨ w=d.affineInvolution eH ∨ w=d.affineFirstFixed eH ∨ w=d.affineSecondFixed eH
  first_conj : ∃ g∈d.block.map d.H.subtype,
    g * d.affineCentralVector eH * g⁻¹=d.affineFirstFixed eH
  second_conj : ∃ g∈d.block.map d.H.subtype,
    g * d.affineCentralVector eH * g⁻¹=d.affineSecondFixed eH
  marked_moved : d.affineInvolution eH*d.affineCentralVector eH ∈
    ⁅sourceModule (d.block.map d.H.subtype),d.affineCentralizerResidual eH⁆
  marked_core : d.affineInvolution eH*d.affineCentralVector eH ∈
    (d.affineCentralizerResidual eH).pCoreIn 2
  marked_ne : d.affineInvolution eH*d.affineCentralVector eH ≠1
  moved_idempotent :
    ⁅⁅sourceModule (d.block.map d.H.subtype),d.affineCentralizerResidual eH⁆,d.affineCentralizerResidual eH⁆=
      ⁅sourceModule (d.block.map d.H.subtype),d.affineCentralizerResidual eH⁆

theorem MinimalBlockSetup.single_alternating_marked_centralizer_packet
    (d : MinimalBlockSetup M) (hsingle : d.L0=d.block)
    (eH : d.H ≃* BinaryFiveAffine.W)
    (hU : ((blockU d.block).map d.block.subtype).map eH.toMonoidHom=BinaryFiveAffine.vectorGroup) :
    d.MarkedA5CentralizerPacket eH := by
  let Ui := (blockU d.block).map d.block.subtype
  have hUi : Ui.map d.H.subtype=sourceModule (d.block.map d.H.subtype) :=
    (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  have hL : d.block=pResidual 2 d.H := hsingle.symm.trans d.L0_eq_residual
  let f : BinaryFiveAffine.W →* G := d.H.subtype.comp eH.symm.toMonoidHom
  have hfU : BinaryFiveAffine.vectorGroup.map f=sourceModule (d.block.map d.H.subtype) := by
    rw [←hU,map_map]
    have hf : f.comp eH.toMonoidHom=d.H.subtype := by
      ext x
      exact congrArg d.H.subtype (eH.symm_apply_apply x)
    rw [hf,hUi]
  have hfL : BinaryFiveAffine.residualImage.map f=d.affineCentralizerResidual eH := by
    rw [←BinaryFiveAffine.markedResidualImage_map eH,map_map]
    have hf : f.comp eH.toMonoidHom=d.H.subtype := by
      ext x
      exact congrArg d.H.subtype (eH.symm_apply_apply x)
    rw [hf]
    exact BinaryFiveAffine.markedResidualImage_ambient_map d.H eH
  obtain ⟨⟨a,ha,hea⟩,⟨b,hb,heb⟩⟩ := BinaryFiveAffine.markedSingular_conjugates_residual eH
  refine ⟨⟨BinaryFiveAffine.ambientMarkedProductEquiv d.H eH⟩,
    ⟨BinaryFiveAffine.ambientMarkedResidualEquiv d.H eH⟩,
    BinaryFiveAffine.ambientMarkedCentralizer_card d.H eH,
    BinaryFiveAffine.ambientMarkedCentralizer_not_two d.H eH,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change Nat.card (↥(sourceModule (d.block.map d.H.subtype) ⊓ centralizer
      (BinaryFiveAffine.ambientMarkedResidualImage d.H eH : Set G)))=4
    rw [←hUi]
    exact BinaryFiveAffine.ambientMarkedFixedFour_card d.H eH Ui hU
  · intro w
    change w∈sourceModule (d.block.map d.H.subtype) ⊓ centralizer
      (BinaryFiveAffine.ambientMarkedResidualImage d.H eH : Set G) ↔ _
    rw [←hUi]
    exact BinaryFiveAffine.ambientMarkedFixedFour_members d.H eH Ui hU w
  · refine ⟨a,mem_map_of_mem _ (hL.symm ▸ ha),?_⟩
    exact congrArg d.H.subtype hea
  · refine ⟨b,mem_map_of_mem _ (hL.symm ▸ hb),?_⟩
    exact congrArg d.H.subtype heb
  · have hh := mem_map_of_mem f BinaryFiveAffine.t_standardZ_commutator
    rw [map_commutator,hfU,hfL] at hh
    rw [BinaryFiveAffine.standardZ_eq_centralSingular,map_mul] at hh
    exact hh
  · have hh := mem_map_of_mem f BinaryFiveAffine.t_standardZ_mem_residual_core
    rw [map_pCoreIn_of_injective 2 _ f (d.H.subtype_injective.comp eH.symm.injective),hfL] at hh
    rw [BinaryFiveAffine.standardZ_eq_centralSingular,map_mul] at hh
    exact hh
  · change f BinaryFiveAffine.t*f (SemidirectProduct.inl BinaryFiveAffine.centralSingular)≠1
    rw [←map_mul,←BinaryFiveAffine.standardZ_eq_centralSingular]
    intro hh
    exact BinaryFiveAffine.t_standardZ_ne_one
      ((d.H.subtype_injective.comp eH.symm.injective) (hh.trans f.map_one.symm))
  · have hLperf : IsPPerfect 2 (d.affineCentralizerResidual eH) :=
      isPPerfect_embedded_pResidual 2 (d.affineCentralizer eH)
    have hnUi : Ui.Normal := by
      let : d.block.Normal := hsingle ▸ d.L0_normal
      infer_instance
    let := hnUi
    have hHU : d.H ≤ normalizer (sourceModule (d.block.map d.H.subtype) : Set G) := by
      rw [←hUi]
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
        Ui.le_normalizer_map d.H.subtype
    have hLU : d.affineCentralizerResidual eH ≤ normalizer (sourceModule (d.block.map d.H.subtype) : Set G) :=
      (map_subtype_le _).trans (inf_le_left.trans hHU)
    have hUp : IsPGroup 2 (sourceModule (d.block.map d.H.subtype)) := by
      rw [←hUi]
      have hUc : Ui≤pCore 2 d.H := by
        rw [←BinaryFiveAffine.pCore_eq_vectorGroup] at hU
        have hc : (pCore 2 d.H).map eH.toMonoidHom=pCore 2 BinaryFiveAffine.W := pCore_map_iso 2 eH
        exact (map_le_map_iff_of_injective eH.injective).mp (hU.trans hc.symm).le
      exact (pCore_isPGroup.to_le hUc).map _
    exact commutator_isPPerfect_idempotent (p:=2) (d.affineCentralizerResidual eH)
      (sourceModule (d.block.map d.H.subtype)) hLperf hUp hLU

omit [Finite G] in
theorem MinimalBlockSetup.single_alternating_marked_moved_elementary
    (d : MinimalBlockSetup M) (hsingle : d.L0=d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (eH : d.H ≃* BinaryFiveAffine.W) :
    IsElementaryAbelian 2 (↥(⁅sourceModule (d.block.map d.H.subtype),d.affineCentralizerResidual eH⁆ : Subgroup G)) := by
  let Ui := (blockU d.block).map d.block.subtype
  have hUi : Ui.map d.H.subtype=sourceModule (d.block.map d.H.subtype) :=
    (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  have hnUi : Ui.Normal := by
    let : d.block.Normal := hsingle ▸ d.L0_normal
    infer_instance
  let := hnUi
  have hHU : d.H ≤ normalizer (sourceModule (d.block.map d.H.subtype) : Set G) := by
    rw [←hUi]
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Ui.le_normalizer_map d.H.subtype
  have hLU : d.affineCentralizerResidual eH ≤ normalizer (sourceModule (d.block.map d.H.subtype) : Set G) :=
    (map_subtype_le _).trans (inf_le_left.trans hHU)
  have hEU := le_normalizer_iff_commutator_le_left.mp hLU
  let : IsElementaryAbelian 2 (sourceModule (d.block.map d.H.subtype)) :=
    hA.2.1.elementary.map (d.block.map d.H.subtype).subtype
  exact IsElementaryAbelian.of_injective (inclusion hEU) (inclusion_injective hEU)

omit [Finite G] in
theorem MinimalBlockSetup.marked_centralizer_not_le_of_secondary_centralizer
    (d : MinimalBlockSetup M) (T : Sylow 2 G) (eH : d.H ≃* BinaryFiveAffine.W)
    (hp : d.MarkedA5CentralizerPacket eH)
    (hMu : M ⊓ centralizer ({d.affineInvolution eH}:Set G) =
      (T:Subgroup G) ⊓ centralizer ({d.affineInvolution eH}:Set G)) :
    ¬d.affineCentralizer eH ≤ M := by
  intro hle
  apply hp.not_two
  have hCT : d.affineCentralizer eH ≤ (T:Subgroup G) := by
    have hh : d.affineCentralizer eH ≤ M ⊓ centralizer ({d.affineInvolution eH}:Set G) :=
      le_inf hle inf_le_right
    rw [hMu] at hh
    exact hh.trans inf_le_left
  exact T.isPGroup'.to_le hCT

end CFSG.Quasithin.Chapter2
