module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.ExtensionRecognition
/-!
# The doubled binary unitary specialization of F.4.26

Two involutions in the marked endpoints, outside their common overlap,
whose product has order four give the quadrangle metric. The faithful
27-point action then identifies the completion with the literal graph
extension of U₄(2), preserving both original endpoint ranges.

Source: Aschbacher--Smith F.4.26, printed p.288. This is the finite binary
unitary case consumed by F.5.5(4), without extra recognition hypotheses.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Extension.Completion
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G : Type*} [Group G] [Finite G] (c : Completion G)

theorem exists_parabolic_preserving_equiv_of_endpoint_involutions (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : orderOf s=2) (ht2 : orderOf t=2) (hst : orderOf (s*t)=4) :
    ∃ e : G≃*GreenBook.LieModels.UnitaryFour.Extension.ProjectiveExtension 1 hn,
      c.left.range.map e.toMonoidHom=GreenBook.LieModels.UnitaryFour.Extension.point 1 hn ∧
      c.right.range.map e.toMonoidHom=GreenBook.LieModels.UnitaryFour.Extension.plane 1 hn := by
  have hd := (c.quadrangle_metric_of_involutions s t hs ht hsout htout
    (by rw [←hs2]; exact pow_orderOf_eq_one s)
    (by rw [←ht2]; exact pow_orderOf_eq_one t)
    (by rw [←hst]; exact pow_orderOf_eq_one (s*t))).2.1
  exact c.exists_parabolic_preserving_equiv_of_diameter hd
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Extension.Completion
