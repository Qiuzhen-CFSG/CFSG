module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairContainmentSource
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalDGSAssembly

/-!
# Original A5 tensor exclusion with pair containment proved

The genuine F.1.1 source proves both original A5 containments, retaining
one normalized Borel. Apply it to the existing original tensor argument:
the mixed size theorem, nonzero Cartan normalization, native linear/G2
exclusions and specialized symplectic geometry have already been proved.
No pair-containment or tensor-exclusion callback remains.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
variable {G : Type*} [Group G] [Finite G]

/-- The original A5-pair containment contract is a theorem of the actual
source, with no recognition premise. -/
theorem a5PairContainment_from_source : A5PairContainment G := by
  intro L S h _ a hn
  exact (ChapterF.Source.a5_pair_core_and_containment_from_source h a hn).2

open Chapter3.Section02
variable {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

include m in
/-- The actual original tensor model is impossible when a maximal two-local
lies outside the selected maximal subgroup. All source inputs are proved. -/
theorem false_of_original_source
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) : False :=
  m.false_of_a5_pair_containment hout a5PairContainment_from_source

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

namespace CFSG.Quasithin.Chapter10
open SourceA5TensorModel
variable {G : Type*} [Group G] [Finite G]

/-- Original tensor exclusion at the same ambient group and Sylow, with
no external pair, mixed-size, Cartan or geometric premise. -/
theorem sourceA5TensorExclusionAt_from_source (T : Sylow 2 G) :
    SourceA5TensorExclusionAt T :=
  sourceA5TensorExclusionAt_of_pair_containment a5PairContainment_from_source T

end CFSG.Quasithin.Chapter10
