module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.SporadicOrder
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.JankoTwo
public import CFSG.Quasithin.ChapterC.Section03.A5.MathieuTwentyTwo
public import CFSG.Quasithin.ChapterC.Section03.A5.MathieuTwentyThreeSource

/-!
# The full sporadic exclusion for the normal deleted-five branch

The cardinal constraints leave M22, M23 and J2. Their native elementary-sixteen
geometries and the actual action of the original alternating-five block exclude
these remaining rows. The source normalizer containment is used without replacing
the block by an unmarked group of order 960.

Source: Aschbacher--Smith, 13.5.15, printed p.921, inspecting Theorem C.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
open ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Every sporadic row of Theorem C contradicts the literal normal-branch markings. -/
theorem not_sporadicModel_of_alternatingFive (K : Subgroup G)
    (hK : IsAlternatingBlock K 5)
    (hcard : Nat.card ((blockU K).map K.subtype) = 16)
    (hctrl : normalizer ((blockU K).map K.subtype : Set G) ≤ normalizer (K : Set G))
    (T : Sylow 2 G) (hT : Nat.card T ≤ 256) :
    ¬ChapterA.Section02.IsTheoremCSporadicModel G := by
  intro hmodel
  let := hK.2.1.elementary
  have hE : IsElementaryAbelian 2 ((blockU K).map K.subtype) := IsElementaryAbelian.map _
  rcases sporadic_remaining_models K hK hE hcard T hT hmodel with ⟨e⟩ | ⟨e⟩ | ⟨e⟩
  · exact no_normalized_alternatingFive_of_m22_equiv e.some K hK hcard hctrl
  · exact no_normalized_alternatingFive_of_m23_equiv e.some K hK hcard hctrl
  · exact no_alternatingFive_of_j2_equiv e.some K hK hcard

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
