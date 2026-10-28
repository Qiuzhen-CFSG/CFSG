module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.GM02.Inputs
public import Theory.Mathieu.LargeInvolutionGeneration

/-!
# Intrinsic involution generation for the large Mathieu degree sieve

The native design-automorphism generation theorems discharge the exact
involution-generation inputs of GM02. The `Reduction` module uses these inputs
through arbitrary faithful irreducible binary central covers, yielding the
degree windows 24 and 48 without a representation-spectrum assumption.

Source: Guralnick--Malle, *Classification of 2F-modules I*, equations
(2.5)--(2.6) and Proposition 5.1, manuscript pp.4,16--17.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
open _root_.Sporadic.Mathieu

/-- Every nonidentity M23 involution has three conjugates generating M23. -/
theorem m23InvolutionGeneration : InvolutionGeneration M23 3 := by
  intro t hne hsq
  exact LargeInvolutionGeneration.m23_three_conjugates_generate t
    (orderOf_eq_prime_iff.mpr ⟨hsq, hne⟩)

/-- Every nonidentity M24 involution has four conjugates generating M24. -/
theorem m24InvolutionGeneration : InvolutionGeneration M24 4 := by
  intro t hne hsq
  exact LargeInvolutionGeneration.m24_four_conjugates_generate t
    (orderOf_eq_prime_iff.mpr ⟨hsq, hne⟩)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
