module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticKernel
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticBlock
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticPlane
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticMarkedPlane
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticCoreBound
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticSecondary

/-!
# Conditional assembly of the original symplectic tensor branch

The proved centralizer-kernel identification transports the supplied action
marking to the literal two-core quotient. Whole-block recognition then feeds
the marked plane restriction, whose retained maps give the existing terminal
tensor contradiction. The original three-premise interface is preserved;
the strengthened assemblies discharge its kernel and plane premises.
The original plane-local surjection, its entire kernel, the full-module
natural quotient and exact equivariance are constructed. Whole-block
recognition remains with qt-d-tensor-sp4-plane. The numerical whole-core
route also constructs the original model; the final block consumer uses it.

Source: Aschbacher--Smith 9.3.10 and the final paragraph of 9.3,
printed pp.734--735, using C.1.32 and MS93 (3.6).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Conditional assembly, discharging the literal quotient transport between
the independent source kernel, block, and plane-recognition arguments. -/
theorem symplecticPlaneRecognition_of_kernel_block_plane
    (hkernel : m.SymplecticKernelRecognition)
    (hblock : m.SymplecticBlockRecognition)
    (hplane : m.SymplecticPlaneFromBlock) : m.SymplecticPlaneRecognition := by
  intro c W hr
  let := hr.normal
  intro hact
  obtain ⟨eact⟩ := hact
  have hker := hkernel c hr ⟨eact⟩
  let eK := (c.residualActionEquiv hr hker).trans eact
  exact hplane c eK (hblock c eK)

/-- The actual terminal consumer of the three separate symplectic contracts.
The earlier source inputs and the other two action rows remain explicit. -/
theorem false_of_generationTwo_source_inputs_of_symplectic_inputs
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion)
    (hkernel : m.SymplecticKernelRecognition)
    (hblock : m.SymplecticBlockRecognition)
    (hplane : m.SymplecticPlaneFromBlock) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain hrows
    (m.symplecticPlaneRecognition_of_kernel_block_plane hkernel hblock hplane)

/-- The original action kernel is proved; only whole-block recognition and
the literal original plane maps remain in this source branch. -/
theorem symplecticPlaneRecognition_of_block_plane
    (hblock : m.SymplecticBlockRecognition)
    (hplane : m.SymplecticPlaneFromBlock) : m.SymplecticPlaneRecognition :=
  m.symplecticPlaneRecognition_of_kernel_block_plane
    m.symplecticKernelRecognition hblock hplane

/-- Actual tensor-exclusion assembly with the symplectic kernel premise discharged. -/
theorem false_of_generationTwo_source_inputs_of_block_plane
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion)
    (hblock : m.SymplecticBlockRecognition)
    (hplane : m.SymplecticPlaneFromBlock) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain hrows
    (m.symplecticPlaneRecognition_of_block_plane hblock hplane)

/-- The natural quotient and its kernel inclusion are proved; the remaining
plane premise supplies only the actual marked plane-local surjection. -/
theorem symplecticPlaneRecognition_of_block_marked_quotient
    (hblock : m.SymplecticBlockRecognition)
    (hquot : m.SymplecticMarkedPlaneQuotient) : m.SymplecticPlaneRecognition :=
  m.symplecticPlaneRecognition_of_block_plane hblock
    (symplecticPlaneFromBlock_of_marked_quotient hquot)

/-- Apply the constructed natural quotient to the actual generation-two
tensor exclusion, retaining the two remaining symplectic source arguments. -/
theorem false_of_generationTwo_source_inputs_of_block_marked_quotient
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion)
    (hblock : m.SymplecticBlockRecognition)
    (hquot : m.SymplecticMarkedPlaneQuotient) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain hrows
    (m.symplecticPlaneRecognition_of_block_marked_quotient hblock hquot)

/-- All original plane maps are proved. Only whole-block recognition remains
in the symplectic source branch. -/
theorem symplecticPlaneRecognition_of_block
    (hblock : m.SymplecticBlockRecognition) : m.SymplecticPlaneRecognition :=
  symplecticPlaneRecognition_of_core_bound (symplecticCoreBound_of_block hblock)

/-- The literal tensor-exclusion consumer with every plane premise discharged. -/
theorem false_of_generationTwo_source_inputs_of_block
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion)
    (hblock : m.SymplecticBlockRecognition) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain hrows
    (m.symplecticPlaneRecognition_of_block hblock)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
