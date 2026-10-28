module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticBoundaryTerminal
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticAssembly
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalTensorAssembly

/-!
# Complete recognition of the original symplectic tensor branch

The Frattini-small case gives the whole intrinsic Sp₄(4) block. In the
remaining case, the original critical geometry has distance four, and the
positioned backward-path argument excludes it. Thus whole-block recognition
has no remaining local or geometric premise.

The proved centralizer/two-core equality transports the literal residual
action marking. The original marked plane surjection, its exact kernel,
and the full-module natural quotient then construct OriginalPlaneModel.
Its subgroup has order 256 and is normalized by the actual outside residual.
Both tensor assemblies below use these same maps and discharge their plane
premise; the independent Cartan, zero-core, A₅-pair and other-row inputs
remain explicit.

Source: Aschbacher--Smith 9.3.10 and the final paragraph of 9.3,
printed pp.734--735; C.1.32 and MS93 (3.6), (5.12), pp.868--871,924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
open Stellmacher.PushingUp.AmalgamGraph
open ChapterC.BinaryMS.MS93
open ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Source 9.3.10 on the entire original residual, including its full core. -/
theorem symplecticBlockRecognition : m.SymplecticBlockRecognition := by
  intro c eK
  by_cases hsmall : ⁅pCore 2 c.M,pResidual 2 c.M⁆ ≤
      (frattini (pCore 2 c.M)).map (pCore 2 c.M).subtype ⊔
        omegaCenterIn (pCore 2 c.M)
  · exact c.sp4_block_of_quotient_frattini_small eK hsmall
  · obtain ⟨geometry,_,_⟩ := c.exists_positive_even_geometry eK
    obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from
      (geometry := geometry) (a := alpha _) rfl
    exact (c.false_of_original_boundary_distance eK geometry path).elim

/-- The original action image yields every field of the original plane model,
with no kernel, block, order, natural-module or positioning premise. -/
theorem symplecticPlaneRecognition : m.SymplecticPlaneRecognition :=
  m.symplecticPlaneRecognition_of_kernel_block_plane
    m.symplecticKernelRecognition m.symplecticBlockRecognition m.symplecticPlaneFromBlock

/-- The original generation-two assembly with its symplectic premise discharged. -/
theorem false_of_generationTwo_source_inputs_of_symplectic
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain hrows
    m.symplecticPlaneRecognition

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 SourceA5TensorModel ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Original point control uses the proved plane recognition on each actual tensor model. -/
theorem source_a5_point_control_of_tensor_inputs_of_symplectic
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnormal : ∀ m : SourceA5TensorModel D e, m.NonzeroCoreCartanNormalization)
    (hzero : ∀ m : SourceA5TensorModel D e, m.ZeroCoreLineCentralization)
    (hcontain : A5PairContainment G)
    (hrows : ∀ m : SourceA5TensorModel D e, m.LinearAndG2Exclusion) :
    (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) :=
  source_a5_point_control_of_tensor_source_inputs D e hn ht htn hD hmany
    hnormal hzero hcontain hrows (fun m => m.symplecticPlaneRecognition)

end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02 Chapter10 Chapter10.SourceA5TensorModel ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal reselected Chapter13 consumer, with the original symplectic
plane premise discharged and both proved cubic bounds retained. -/
theorem exists_original_minimal_point_control_of_tensor_inputs_of_symplectic
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnormal : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.NonzeroCoreCartanNormalization)
    (hzero : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.ZeroCoreLineCentralization)
    (hcontain : A5PairContainment G)
    (hrows : ∀ (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      D.IsMinimalFullModule → ∀ m : SourceA5TensorModel D e, m.LinearAndG2Exclusion) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧ SourceFullModuleCubicBound D ∧
      SourceLocalModuleCubicBound D ∧
      (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) ∧
      1 < globalW D.fullModule (T : Subgroup G) :=
  exists_original_minimal_point_control_of_tensor_source_inputs h e hn ht htn hmany
    hnormal hzero hcontain hrows (fun _ _ m => m.symplecticPlaneRecognition)

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
