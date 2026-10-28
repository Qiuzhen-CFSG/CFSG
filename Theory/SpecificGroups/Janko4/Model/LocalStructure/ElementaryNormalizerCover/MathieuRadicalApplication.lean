module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuCase

/-!
# Direct radical consumer for the native Mathieu local

The Mathieu branch of the elementary-normalizer argument is often consumed
after the preceding local geometry has already placed the whole normalizer of
a radical subgroup inside the normalizer of the native binary kernel.  This
leaf records that specialization with no extra cover premise: the centralizer
of the kernel is placed by the native max1 calculation, and all restriction
maps remain literal.

Source: Kleidman--Wilson, *The Maximal Subgroups of J₄* (1988),
Lemma 1.1.2(i) and Proposition 2.2.3, pp.486 and 491.
-/

public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover

open Subgroup

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- A radical whose ambient normalizer normalizes the native binary kernel is
restricted to the literal Mathieu local, with the full normalizer-core data.
The only placement hypothesis is the displayed normalizer containment; the
Mathieu centralizer and elementary uniqueness calculations are discharged by
the native branch itself. -/
theorem radical_mathieu_local_of_normalizer_le_kernel
    (P : Subgroup Janko4.Model) (hP : P.IsPRadical 2)
    (hNP : normalizer (P : Set Janko4.Model) ≤
      normalizer (embeddedKernel : Set Janko4.Model)) :
    normalizer (P : Set Janko4.Model) ≤ max1 ∧ P ≤ max1 ∧
      (normalizer (P.subgroupOf max1 : Set max1)).map max1.subtype =
        normalizer (P : Set Janko4.Model) ∧
      (P.subgroupOf max1).IsPRadical 2 ∧
      (normalizer (P.subgroupOf max1 : Set max1)).pCoreIn 2 =
        P.subgroupOf max1 ∧
      ((normalizer (P.subgroupOf max1 : Set max1)).pCoreIn 2).map
          max1.subtype = P := by
  exact radical_mathieu_local_of_kernel_and_centralizer P embeddedKernel hP hNP
    le_rfl Janko4.LocalStructure.centralizer_embedded_localKernel_le_max1

end Janko4.LocalStructure.ElementaryNormalizerCover
