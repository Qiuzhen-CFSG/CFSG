module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramActor
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddTwo
/-!
# Lifting the marked automizer to a source element

For a normal component, every automorphism in the original quotient
automizer is induced by an actual element of the specified source subgroup.
The lift uses the literal quotient map and agrees with the marked action.

Source: Aschbacher–Smith, 14.2.8(3), printed p.983.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

omit [Finite H] [Finite D] in
theorem sourceAutomizer_eq_markedParabolicActor_image (M K T : Subgroup H) [K.Normal]
    (e : sourceImage M K ≃* D) (a : MulAut (sourceImage M K))
    (ha : a ∈ sourceAutomizer M K T) :
    ∃ t : H, t ∈ T ∧ MulAut.congr e a = markedParabolicActor M K e t := by
  let : (sourceImage M K).Normal :=
    (inferInstance : K.Normal).map (QuotientGroup.mk' (sourceKernel M))
      (QuotientGroup.mk'_surjective _)
  rw [sourceAutomizer_eq_map_conjNormal] at ha
  obtain ⟨q,hq,hqa⟩ := ha
  obtain ⟨t,ht,hqt⟩ := hq
  refine ⟨t,ht,?_⟩
  subst a
  subst q
  rfl
end CFSG.Quasithin.Chapter14.Section02
