module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.RadicalAction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SylowOrbit.Generators
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PairQuotients

/-!
# Placement of the native radical operators

The two explicit operators are short words in the proved native Sylow generators.
The point stabilizer is identified with the design pair stabilizer, whose
five-hexad action has kernel equal to its intrinsic two-core. Checking those
five hexads places the operators in that core. The transvection word is even,
so it also lies in the genuine triple-cover component.

Source: Aschbacher–Smith 14.4.12, printed pp.1011–1012; H.12.1, pp.393–394.
-/

@[expose] public section
noncomputable section
open Matrix Subgroup Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender
open scoped Matrix Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction
namespace NativePositions
open SylowCertificates OrbitCertificates

def inverterWord : Group := s0 * s1 * s2
def transvectionWord : Group := s1 * s3 * s3 * s5

theorem inverterWord_matrix : ((inverterWord : Matrix12ˣ) : Matrix12) = inverterMatrix := by
  simp only [inverterWord, Subgroup.coe_mul, Units.val_mul, s0_matrix, s1_matrix, s2_matrix]
  rw [show (fromRows ![3449, 1774, 2689, 547, 3744, 3682, 397, 1875, 712, 1533, 783, 4051]) * (fromRows ![958, 2055, 1094, 3300, 1573, 139, 3829, 1917, 1188, 1491, 688, 4093]) = (fromRows ![3816, 3781, 3821, 3809, 3944, 3815, 2245, 174, 191, 558, 620, 2094]) by decide +kernel]
  rw [show (fromRows ![3816, 3781, 3821, 3809, 3944, 3815, 2245, 174, 191, 558, 620, 2094]) * (fromRows ![618, 181, 1426, 1461, 2397, 1857, 1648, 2534, 3094, 1072, 3100, 358]) = (fromRows ![1064, 292, 976, 1015, 472, 1744, 2312, 3637, 1282, 995, 1318, 1717]) by decide +kernel]
  rfl

theorem transvectionWord_matrix : ((transvectionWord : Matrix12ˣ) : Matrix12) = nativeTransvectionMatrix := by
  simp only [transvectionWord, Subgroup.coe_mul, Units.val_mul, s1_matrix, s3_matrix, s5_matrix]
  rw [show (fromRows ![958, 2055, 1094, 3300, 1573, 139, 3829, 1917, 1188, 1491, 688, 4093]) * (fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920]) = (fromRows ![1850, 854, 271, 430, 1396, 299, 1154, 1565, 1225, 1892, 1291, 2221]) by decide +kernel]
  rw [show (fromRows ![1850, 854, 271, 430, 1396, 299, 1154, 1565, 1225, 1892, 1291, 2221]) * (fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920]) = (fromRows ![44, 47, 41, 14, 2397, 38, 2312, 3271, 1012, 3689, 1759, 954]) by decide +kernel]
  rw [show (fromRows ![44, 47, 41, 14, 2397, 38, 2312, 3271, 1012, 3689, 1759, 954]) * (fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504]) = (fromRows ![1898, 1438, 146, 158, 3944, 577, 64, 2802, 3097, 1802, 3091, 1423]) by decide +kernel]
  rfl

theorem inverterWord_unit : (inverterWord : Matrix12ˣ) = inverterUnit :=
  Units.ext inverterWord_matrix

theorem transvectionWord_unit : (transvectionWord : Matrix12ˣ) = nativeTransvectionUnit :=
  Units.ext transvectionWord_matrix

theorem inverter_mem_actionGroup : inverterUnit ∈ actionGroup :=
  inverterWord_unit ▸ inverterWord.property

theorem transvection_mem_actionGroup : nativeTransvectionUnit ∈ actionGroup :=
  transvectionWord_unit ▸ transvectionWord.property

private theorem generator_mem_candidate (i : Fin 6) : generator i ∈ candidate :=
  subset_closure ⟨i, rfl⟩

theorem inverterWord_point : inverterWord ∈ pointCentralizer := by
  apply candidate_le_pointCentralizer
  exact candidate.mul_mem (candidate.mul_mem (generator_mem_candidate 0)
    (generator_mem_candidate 1)) (generator_mem_candidate 2)

theorem transvectionWord_point : transvectionWord ∈ pointCentralizer := by
  apply candidate_le_pointCentralizer
  exact candidate.mul_mem (candidate.mul_mem (candidate.mul_mem
    (generator_mem_candidate 1) (generator_mem_candidate 3))
    (generator_mem_candidate 3)) (generator_mem_candidate 5)

theorem pointCentralizer_eq_reference :
    pointCentralizer = ActorCatalogue.Native.pointCentralizer ActorCatalogue.Native.referenceVector := by
  ext g
  constructor
  · intro h
    exact h.2 markedVector (Submodule.mem_span_singleton_self _)
  · intro h
    refine ⟨mem_top _, ?_⟩
    intro v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul]
    exact congrArg (fun w => a • w) h

private def referenceEquiv : pointCentralizer ≃* ActorCatalogue.Native.referencePairStabilizer ActorCatalogue.Native.referencePair :=
  (MulEquiv.subgroupCongr pointCentralizer_eq_reference).trans
    (ActorCatalogue.Native.referencePointCentralizerEquivPair ActorCatalogue.Native.referencePair
      (fun g => (ActorCatalogue.Native.reference_projective_comparison g).trans (ActorCatalogue.Native.referenceRowPairComparison g)))

private theorem referenceEquiv_val (g : pointCentralizer) :
    (referenceEquiv g).val = ActorCatalogue.Native.referenceProjection g.val := rfl

private def endpointProjection : Group →* Equiv.Perm (Fin 22) :=
  m22DesignAut.subtype.comp ActorCatalogue.Native.referenceProjection

private theorem endpointProjection_C :
    endpointProjection outerInvolution = ActorCatalogue.Native.ReferenceOuterAction.permC :=
  CoreProjectiveAction.compatible_unique (ActorCatalogue.Native.referenceProjection_compatible outerInvolution)
    ActorCatalogue.Native.ReferenceOuterAction.compatible_C

private theorem endpointProjection_D :
    endpointProjection generatorD = ActorCatalogue.Native.ReferenceOuterAction.permD :=
  CoreProjectiveAction.compatible_unique (ActorCatalogue.Native.referenceProjection_compatible generatorD)
    ActorCatalogue.Native.ReferenceOuterAction.compatible_D

private def pairTransportWord : Group :=
  outerInvolution * generatorD * generatorD * generatorD * outerInvolution * generatorD * generatorD

private def pairTransport : m22DesignAut := ActorCatalogue.Native.referenceProjection pairTransportWord

private def pairTransportPerm : Equiv.Perm (Fin 22) :=
  ActorCatalogue.Native.ReferenceOuterAction.permC * ActorCatalogue.Native.ReferenceOuterAction.permD * ActorCatalogue.Native.ReferenceOuterAction.permD *
    ActorCatalogue.Native.ReferenceOuterAction.permD * ActorCatalogue.Native.ReferenceOuterAction.permC *
      ActorCatalogue.Native.ReferenceOuterAction.permD * ActorCatalogue.Native.ReferenceOuterAction.permD

private theorem pairTransport_perm : (pairTransport : Equiv.Perm (Fin 22)) = pairTransportPerm := by
  change endpointProjection pairTransportWord = _
  simp only [pairTransportWord, pairTransportPerm, map_mul, endpointProjection_C, endpointProjection_D]

private theorem pairTransport_pair : m22Pair12 = pairTransport • ActorCatalogue.Native.referencePair := by
  change m22Pair12 = (pairTransport : Equiv.Perm (Fin 22)) • ActorCatalogue.Native.referencePair
  rw [pairTransport_perm]
  decide +kernel

private def pairEquiv : ActorCatalogue.Native.referencePairStabilizer ActorCatalogue.Native.referencePair ≃* M22ValueBound.Concrete.outerFirst :=
  MulAction.stabilizerEquivStabilizer pairTransport_pair

private def pointEquiv : pointCentralizer ≃* M22ValueBound.Concrete.outerFirst := referenceEquiv.trans pairEquiv

private theorem pointEquiv_perm (g : pointCentralizer) :
    ((pointEquiv g).val : Equiv.Perm (Fin 22)) =
      pairTransportPerm * endpointProjection g.val * pairTransportPerm⁻¹ := by
  have he : (pairEquiv (referenceEquiv g)).val =
      pairTransport * (referenceEquiv g).val * pairTransport⁻¹ :=
    MulAction.stabilizerEquivStabilizer_apply pairTransport_pair (referenceEquiv g)
  have he' := congrArg (fun z : m22DesignAut => z.val) he
  change ((pointEquiv g).val : Equiv.Perm (Fin 22)) = _ at he'
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, referenceEquiv_val,
    pairTransport_perm, endpointProjection, MonoidHom.comp_apply, Subgroup.subtype_apply] using he'

private theorem mem_pointRadical_of_hexads (g : pointCentralizer)
    (h : ∀ i : Fin 5, ((pointEquiv g).val : Equiv.Perm (Fin 22)) • M22ValueBound.Concrete.pairHexad i = M22ValueBound.Concrete.pairHexad i) :
    g.val ∈ pointRadical := by
  have hg : pointEquiv g ∈ pCore 2 M22ValueBound.Concrete.outerFirst := by
    rw [← M22ValueBound.Concrete.outerPairAction_ker_eq_twoCore]
    apply Equiv.ext
    intro i
    apply M22ValueBound.Concrete.pairHexad_injective
    rw [M22ValueBound.Concrete.outerPairAction_spec, h]
    rfl
  rw [← pCore_map_iso 2 pointEquiv] at hg
  obtain ⟨a, ha, he⟩ := hg
  have he' : a = g := pointEquiv.injective he
  exact ⟨g, he' ▸ ha, rfl⟩

theorem inverterWord_radical : inverterWord ∈ pointRadical := by
  apply mem_pointRadical_of_hexads ⟨inverterWord, inverterWord_point⟩
  intro i
  rw [pointEquiv_perm]
  simp only [inverterWord, s0, s1, s2, actor0, actor1, actor2, actor3,
    map_mul, map_inv, endpointProjection_C, endpointProjection_D]
  revert i
  decide +kernel

theorem transvectionWord_radical : transvectionWord ∈ pointRadical := by
  apply mem_pointRadical_of_hexads ⟨transvectionWord, transvectionWord_point⟩
  intro i
  rw [pointEquiv_perm]
  simp only [transvectionWord, s1, s3, s5, actor0, actor1, actor2, actor3,
    map_mul, map_inv, endpointProjection_C, endpointProjection_D]
  revert i
  decide +kernel

theorem transvectionWord_component : transvectionWord ∈ componentInclusion.range := by
  have hc : outerInvolution ∉ ActorCatalogue.Native.component := ActorCatalogue.Native.outerInvolution_not_mem
  have hd : generatorD ∉ ActorCatalogue.Native.component := by
    have hcd : outerInvolution * generatorD ∈ ActorCatalogue.Native.component := coreA_mem_derivedGroup
    rw [mul_mem_iff_of_index_two ActorCatalogue.Native.component_index] at hcd
    exact fun hd => hc (hcd.mpr hd)
  have h0 : actor0 ∉ ActorCatalogue.Native.component := by
    simp [actor0, mul_mem_iff_of_index_two ActorCatalogue.Native.component_index, hc, hd]
  have h1 : actor1 ∉ ActorCatalogue.Native.component := by
    simp [actor1, mul_mem_iff_of_index_two ActorCatalogue.Native.component_index, hc, hd]
  have h2 : actor2 ∈ ActorCatalogue.Native.component := by
    simp [actor2, mul_mem_iff_of_index_two ActorCatalogue.Native.component_index, hc, hd]
  have h3 : actor3 ∉ ActorCatalogue.Native.component := by
    simp [actor3, mul_mem_iff_of_index_two ActorCatalogue.Native.component_index, hc, hd]
  have ht : transvectionWord ∈ ActorCatalogue.Native.component := by
    simp [transvectionWord, s1, s3, s5,
      mul_mem_iff_of_index_two ActorCatalogue.Native.component_index, h0, h1, h2, h3]

  exact ⟨⟨transvectionWord.val, ht⟩, rfl⟩

end NativePositions

/-- The literal native inverter lies in the embedded intrinsic point two-core. -/
theorem inverterUnit_mem_pointRadical : inverterUnit ∈ pointRadical.map actionGroup.subtype :=
  ⟨NativePositions.inverterWord, NativePositions.inverterWord_radical,
    NativePositions.inverterWord_unit⟩

/-- The literal native transvection lies in the point two-core inside the genuine component. -/
theorem nativeTransvectionUnit_mem_pointRadical_component : nativeTransvectionUnit ∈
    (pointRadical ⊓ componentInclusion.range).map actionGroup.subtype :=
  ⟨NativePositions.transvectionWord,
    ⟨NativePositions.transvectionWord_radical, NativePositions.transvectionWord_component⟩,
    NativePositions.transvectionWord_unit⟩

/-- The central F₄-point is moved by the literal point radical on the marked
orthogonal hyperplane. This is the first source containment in E. -/
theorem markedPoint_le_markedPerp_radical_moved :
    binaryPoint markedVector ≤ subspaceCommutator representation markedPerp pointRadical := by
  obtain ⟨T, hT, _, hmove⟩ :=
    exists_radical_transvection_subgroup nativeTransvectionUnit_mem_pointRadical_component
  apply hmove.trans
  apply Submodule.span_le.mpr
  rintro w ⟨g, hg, v, hv, rfl⟩
  exact Submodule.subset_span ⟨g, (hT hg).1.1, v,
    parabolicSpace_le_markedPerp hv, rfl⟩

/-- The first cubic actor's displacement lies in the genuine radical
commutator on the marked orthogonal hyperplane. -/
theorem scalar_moved_le_markedPerp_radical_moved :
    subspaceCommutator representation (binaryLine markedVector)
      (Subgroup.zpowers centralScalar) ≤
      subspaceCommutator representation markedPerp pointRadical := by
  rw [scalar_moved_line_eq_point]
  exact markedPoint_le_markedPerp_radical_moved

/-- The native operator calculations with both point-radical positions discharged. -/
theorem native_operator_calculations_of_second_image
    (A : Subgroup parabolic)
    (hA : A.map parabolicRepresentation.asGroupHom = secondImage) :
    Nat.card (subspaceCommutator parabolicRepresentation markedLine A) = 4 ∧
    subspaceCommutator parabolicRepresentation markedLine A ≤
      subspaceCommutator parabolicRepresentation ⊤ (pointRadical.subgroupOf parabolic) ∧
    (binaryPoint markedVector).comap parabolicSpace.subtype ≤
      subspaceCommutator parabolicRepresentation ⊤
        ((pointRadical ⊓ componentInclusion.range).subgroupOf parabolic) :=
  native_operator_calculations A hA inverterUnit_mem_pointRadical
    nativeTransvectionUnit_mem_pointRadical_component

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.RadicalAction
