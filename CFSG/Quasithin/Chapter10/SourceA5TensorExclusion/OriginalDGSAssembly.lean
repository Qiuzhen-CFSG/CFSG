module

public import CFSG.Quasithin.Chapter14.Section09.ShortRoute.MixedSize
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.CubicFactor.MarkedQuotient
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationComplete
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoCartanComplete
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticComplete
public import CFSG.Quasithin.Chapter10.SourceA5Normalization

/-!
# Original tensor exclusion with the mixed size theorem discharged

The genuine mixed DGS theorem bounds the Sylow of the constructed A₅/S₃
pair by 256. The original tensor module already has order 256 and is proper
in that Sylow, so the zero-core branch is impossible. This proves the
old-residual line centralization with the actual cubic factor constructed.

The completed nonzero Cartan, linear/G₂ and symplectic arguments then leave
only the original A₅/A₅ pair containment theorem in the tensor exclusion.
All modules and overgroups retain their original ambient group and Sylow.
The pair theorem remains explicit; this does not prove normalization by itself.
Source: Aschbacher--Smith 9.3.1--10 and 10.2.13, pp.732--735,755,
using the mixed case of F.1.12(I), pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Original 9.3.1 line centralization, without a size or cubic-factor premise. -/
theorem old_residual_centralizes_tensorLine_from_dgs
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < ChapterE.generationParameter H) :
    (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) := by
  apply m.old_residual_centralizes_tensorLine_of_mixed_size ?_ hH hlarge
  intro K U S h _ _ hK hU _
  exact ChapterF.Source.DGS85.ShortRoute.mixed_original_sylow_card_le h hK.some hU.some

include m in
/-- The original tensor contradiction retains only the independent A₅-pair theorem. -/
theorem false_of_a5_pair_containment
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcontain : A5PairContainment G) : False := by
  apply m.false_of_generationTwo_source_inputs hout ?_ ?_ hcontain
    m.linearAndG2Exclusion m.symplecticPlaneRecognition
  · exact m.nonzero_core_cartan_normalizes
  · intro H hH hlarge A B hAB hA9 hAe hB3 hBK hBC hzero
    exact m.old_residual_centralizes_tensorLine_from_dgs hH hlarge

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 SourceA5TensorModel
variable {G : Type*} [Group G] [Finite G]

/-- The genuine remaining A₅-pair source supplies the tensor input on every
original minimal setup; the mixed and geometric inputs have been proved. -/
theorem sourceA5TensorExclusionAt_of_pair_containment
    (hcontain : A5PairContainment G) (T : Sylow 2 G) : SourceA5TensorExclusionAt T := by
  intro L D e _ hmany _ hm
  obtain ⟨m⟩ := hm
  exact m.false_of_a5_pair_containment (source_maximalOutside_of_many D hmany) hcontain

end CFSG.Quasithin.Chapter10
