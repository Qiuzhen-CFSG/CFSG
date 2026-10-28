module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointQuaternion
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.BinaryOrders
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition

/-!
# The two SL₂(3) factors in the binary unitary point residual

The actual unitary point parabolic has order 576 and a self-centralizing
quaternion central-product two-core. Its independent cubic actors extend
the two embedded quaternion factors to commuting SL₂(3) groups whose join
is precisely its two-residual. This is the concrete residual input for
the marked ordinary point comparison in Aschbacher--Smith 13.5.17,
printed pp.920--922; the model is the point parabolic of F.4.29.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.PointResidual
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open PointQuaternion

local notation "P" => pointParabolic 1 (Nat.le_refl 1)
local notation "Q" => pCore 2 P

/-- Recognition uses the actual point core and the two quaternion factors constructed in it. -/
theorem projective_point_residual_exists :
    Nonempty (QuaternionResidualCentralProduct Q projectivePointQuaternionData) := by
  obtain ⟨actors⟩ := independent_cubics_of_normal_quaternion_product_card_576
    Q projectivePointQuaternionData PointCore.projective_point_core_selfCentralizing
    BinaryCompletion.point_card
  obtain ⟨c,_,_⟩ := actors.residual_central_product
    Q projectivePointQuaternionData BinaryCompletion.point_card
  exact ⟨c⟩

/-- The concrete point residual, with both actual SL₂(3) embeddings retained. -/
def projectivePointResidualData :
    QuaternionResidualCentralProduct Q projectivePointQuaternionData :=
  Classical.choice projective_point_residual_exists

end CFSG.Quasithin.ChapterF.UnitaryTwo.PointResidual
