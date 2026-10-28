module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.ComponentImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.IntrinsicKernel.CoverReduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.IntrinsicKernel.MaximumOffender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.IntrinsicKernel.QuaternionExclusion

/-!
# Vanishing of the intrinsic elementary MS kernel

For elementary D=[O₂(J),L], the actual component action image is centerless.
The central-cover reduction identifies any nontrivial center with the genuine
SL₂(7) case. The MS maximum-elementary condition and the central-product
offender bound exclude that case, leaving a trivial center and projection
kernel. The exact kernel computation then gives [D,O₂(L)]=1, with O₂(L)
mapped into the ambient group J.

All premises of the cover exclusion are discharged by the genuine MS input
and elementary D. Whole-core action descent and construction of a component
offender belong to the parent Descent task.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137; B.2.4–5, printed pp.75–76; I.1.3, printed p.407.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC.BinaryMS

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R) [IsElementaryAbelian 2 (commutatorCore L)]

/-- The genuine MS hypotheses eliminate the central kernel of the component
action on the elementary commutator core. -/
theorem Input.elementaryCore_componentImage_center_eq_bot :
    center h.coreConjugation.range = ⊥ := by
  rcases h.abelianCore_componentImage_center_cases
    (inferInstance : IsMulCommutative (commutatorCore L)) with hz | ⟨_, he⟩
  · exact hz
  · exact (h.elementaryCore_not_nonempty_SL2Seven he).elim

/-- The projection of the actual component action image onto the specified
SL₃(2) quotient has trivial kernel. -/
theorem Input.elementaryCore_componentProjection_kernel_eq_bot :
    h.coreComponentProjection.ker = ⊥ := by
  rw [h.abelianCore_componentProjection_kernel_eq_center
    (inferInstance : IsMulCommutative (commutatorCore L)),
    h.elementaryCore_componentImage_center_eq_bot]

include h in
/-- The elementary commutator core centralizes the ambient image of the
intrinsic two-core of L. This supplies the centrality needed for descent. -/
theorem Input.elementaryCore_componentCore_centralizes :
    commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J) :=
  (h.abelianCore_componentCore_centralizes_iff_center_eq_bot
    (inferInstance : IsMulCommutative (commutatorCore L))).mpr
      h.elementaryCore_componentImage_center_eq_bot

end CFSG.Quasithin.ChapterC.BinaryMS
