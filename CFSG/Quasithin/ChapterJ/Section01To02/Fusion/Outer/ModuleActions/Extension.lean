module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.ModuleActions.Natural
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.ModuleActions.Sections
public import Theory.Representation.BinaryInvolutionFreeness

/-!
# The six-space reduction for outer involutions

The marked projection Q/U → Q/HC has a binary plane as kernel. Movement on
that plane makes it free, while the preceding natural-module theorem makes
the head free. The binary extension theorem then proves freeness on Q/U.
The movement premise remains to be derived from the Ru2 indecomposability
and J.2.2(3); these conditional reductions do not assert its existence.

Source: Aschbacher–Smith, J.2.5–6, printed pp.434–435 (PDF pp.445–446).
-/

public section

open Subgroup Representation Representation.BinaryInvolution
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]
variable (d : LocalSetup G) (head : NaturalHead d.toTypeRuSetup)

theorem NaturalHead.kernel_free_of_moved (t : S5) (ht : t * t = 1)
    (hmoved : ∃ v ∈ (head.sixProjection d).ker, d.ru2.sixAction t v ≠ v) :
    FreeAt (head.kernelAction d) t := by
  obtain ⟨v, hv, hvt⟩ := hmoved
  apply free_of_finrank_two _ t ht (head.finrank_sixProjection_kernel d)
  exact ⟨⟨v, hv⟩, fun h => hvt (congrArg Subtype.val h)⟩

/-- Freeness of the six-space from the natural head and movement in its kernel.
Movement is still an independent indecomposable-module obligation. -/
theorem NaturalHead.six_free_of_kernel_moved (t : S5)
    (ht : t ∉ alternatingGroup (Fin 5)) (ht2 : t * t = 1)
    (hmoved : ∃ v ∈ (head.sixProjection d).ker, d.ru2.sixAction t v ≠ v) :
    FreeAt d.ru2.sixAction t := by
  have hk := head.kernel_free_of_moved d t ht2 hmoved
  apply free_of_free_kernel_and_quotient d.ru2.sixAction head.action.action
    (head.sixProjection d) (head.sixProjection_surjective d)
    (head.sixProjection_equivariant d) t ht2 (natural_free_outer head.action t ht ht2)
  intro v hv hvt
  obtain ⟨w, hw⟩ := hk ⟨v, hv⟩ (Subtype.ext hvt)
  exact ⟨w, w.property, congrArg Subtype.val hw⟩

end CFSG.Quasithin.ChapterJ.Fusion.Outer
