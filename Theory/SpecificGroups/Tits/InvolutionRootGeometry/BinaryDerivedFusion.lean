module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.BinaryDerivedFusion.OuterSquares

/-!
# Derived membership and internal fusion for binary positive involutions

Every square-one element of the actual positive subgroup of the binary Ree
group lies in its commutator subgroup. Positive coordinates and the marked
Atlas Sylow map reduce the complement to 2,048 outer words; the kernel-checked
matrix certificate excludes square one for each word.

The existing index-two fusion proof corrects ambient conjugators by the
explicit outer centralizers of the two marked root representatives. Together
these results lift positive involutions and their root conjugacies to the
literal derived subgroup. The normal-form application below supplies the
derived-intersection step for the full binary involution coverage calculation;
exhaustion of the two root classes remains a separate calculation.

Source: Parrott (1972), §5, printed p.683 (the marked generators);
GLS3 Table 2.4 and 2.4.5(d) (the fixed root coordinates).
Application: Aschbacher–Smith 16.1.4, printed p.1171.
-/

public section
noncomputable section
namespace Tits.InvolutionRootGeometry.BinaryDerivedFusion
open ReeF4 ReeF4.Parabolics
open Tits.ExceptionalParabolics.FullRee

/-- Every positive square-one element belongs to the actual derived subgroup,
including the identity. The finite outer-coset premise is fully discharged. -/
theorem square_one_mem_derived (x : Model 0) (hx : x ∈ unipotent 0)
    (hsq : x ^ 2 = 1) : x ∈ commutator (Model 0) :=
  square_one_mem_derived_of_check outer_normalForm_square_ne_one x hx hsq

/-- The derived-intersection step of binary involution enumeration, using the
literal marked Atlas embedding and its ordered Sylow normal forms. -/
theorem square_one_atlas_normalForm (x : Model 0) (hx : x ∈ unipotent 0)
    (hsq : x ^ 2 = 1) :
    ∃ n : Fin 2048, atlasEmbedding (atlas1600SylowTwoNormalForm n) = x := by
  have hm : x ∈ ExceptionalParabolics.S.map atlasEmbedding := by
    rw [atlas_sylow_map]
    exact ⟨hx, square_one_mem_derived x hx hsq⟩
  obtain ⟨y, hy, he⟩ := hm
  obtain ⟨n, hn⟩ := atlas1600SylowTwoNormalForm_surjective hy
  exact ⟨n, (congrArg atlasEmbedding hn).trans he⟩

/-- Lift the same square-one element to the derived carrier, preserving both
root conjugacy tests. Each intrinsic conjugacy has a derived-group conjugator. -/
theorem square_one_lift (x : Model 0) (hx : x ∈ unipotent 0) (hsq : x ^ 2 = 1) :
    ∃ y : commutator (Model 0), (y : Model 0) = x ∧ y ^ 2 = 1 ∧
      (IsConj (longRoot : Model 0) x ↔ IsConj longRoot y) ∧
      (IsConj (shortRoot : Model 0) x ↔ IsConj shortRoot y) := by
  let y : commutator (Model 0) := ⟨x, square_one_mem_derived x hx hsq⟩
  exact ⟨y, rfl, Subtype.ext hsq, longRoot_isConj_iff y, shortRoot_isConj_iff y⟩

end Tits.InvolutionRootGeometry.BinaryDerivedFusion
