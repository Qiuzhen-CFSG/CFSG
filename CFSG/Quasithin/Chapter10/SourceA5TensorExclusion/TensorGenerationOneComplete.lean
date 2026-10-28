module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointNormalityComplete
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorWeakClosureComplete
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualRecognition

/-!+# Excluding generation one in the original tensor configuration

The same original H-star subgroup supplies the generation-one Sylow action
needed for nonsingular-point normality. Point normality then gives pair
control, corank greater than three, and the weak-closure contradiction.
Thus an original H-star subgroup cannot have generation parameter one.
Combining this with the proved one-or-two bound leaves generation two as
the only possible value in the original tensor configuration.

The outside-maximal-local guard remains explicit. No point-normality,
component-classification, action-image or weak-closure premise remains.
The generation-two exclusion is a separate earlier source argument.

Source: Aschbacher--Smith 9.2.7(2) and 9.4.1--5, printed pp.731,735--737.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The original generation-one H-star branch of the tensor configuration
is impossible, with all point-normality and weak-closure inputs discharged. -/
theorem tensor_generation_one_false
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hgen : generationParameter H = 1) : False :=
  m.tensor_generation_one_false_of_point_normality
    (m.tensorPointResidual_normality_of_generation_one hout hH hgen) hH hgen

/-- Every original H-star subgroup in the tensor configuration has
generation parameter two. -/
theorem tensor_hstar_generation_eq_two
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    generationParameter H = 2 := by
  rcases m.hstar_generation_one_or_two hH with hgen | hgen
  · exact (m.tensor_generation_one_false hout hH hgen).elim
  · exact hgen

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
