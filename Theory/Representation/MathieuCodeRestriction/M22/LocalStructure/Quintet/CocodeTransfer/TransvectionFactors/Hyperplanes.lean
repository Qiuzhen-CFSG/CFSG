module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Hyperplanes.OrbitSpan
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Involution selection and ambient hyperplane fixed dimensions

A single specified involution of K outside L with ambient fixed dimension
five supplies the involution needed in every hyperplane other than K ∩ L:
its actual Q-orbit meets each such hyperplane. Ambient conjugation preserves
its order and fixed dimension. The transvection fixed-space theorem then
gives ambient fixed dimension two. For K ∩ L this is the dimension of V2.

The earlier H.14 conjugation structure and this single marked involution
are explicit inputs, as is the permitted irreducible top quotient. In
particular, this argument never assigns the same fixed dimension to both
outer involution classes. The source assembly must discharge these inputs.

Source: Aschbacher--Smith H.15.4(3), printed p.400, using H.14.3(2) and
H.14.4, printed pp.397--398, combined manuscript of 1 March 2004.
-/

public section
noncomputable section
open scoped IsMulCommutative
namespace MathieuCode.M22Quintet.CocodeTransfer

open Representation.BinaryOffender

/-- The specified outer involution supplies a conjugate in every other hyperplane.
Conjugation transports both its order and its ambient fixed dimension. -/
theorem exists_involution_mem_hyperplane [IsElementaryAbelian 2 K]
    (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    (hindecomp : ∀ U W : Subrepresentation kernelConjugation,
      IsCompl U W → U = ⊥ ∨ W = ⊥)
    (i0 : m22PairStabilizer) (hi0 : i0 ∈ K) (hout : i0 ∉ L)
    (horder : orderOf i0 = 2)
    (hfixed : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i0)) = 5)
    (A : Subgroup m22PairStabilizer) (hA : A ≤ K) (hindex : A.relIndex K = 2)
    (hne : A ≠ A0) :
    ∃ i ∈ A, i ∉ L ∧ orderOf i = 2 ∧
      Module.finrank (ZMod 2)
        (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i)) = 5 := by
  obtain ⟨g,hg⟩ := exists_conjugate_mem_hyperplane D I hindecomp i0 hi0 hout A hA hindex hne
  let i := g.val * i0 * g.val⁻¹
  refine ⟨i, hg, ?_, ?_, ?_⟩
  · intro hiL
    have hiA0 : i ∈ A0 := ⟨hA hg, hiL⟩
    have hi0A0 := (Subgroup.mem_normalizer_iff.mp (I.normalizer g.property) i0).mpr hiA0
    exact hout hi0A0.2
  · exact ((MulAut.conj g.val).orderOf_eq i0).trans horder
  · have he := (fixedSpaceConjEquiv m22OuterCocodeRepresentation
        (Subgroup.zpowers i0) g.val).finrank_eq
    rw [MonoidHom.map_zpowers] at he
    exact he.symm.trans hfixed

/-- The ambient fixed space of every hyperplane has dimension two.
Only one marked outer involution is an input; its conjugates are selected above. -/
theorem finrank_fixed_hyperplane [IsElementaryAbelian 2 K]
    (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation]
    (hindecomp : ∀ U W : Subrepresentation kernelConjugation,
      IsCompl U W → U = ⊥ ∨ W = ⊥)
    (i0 : m22PairStabilizer) (hi0 : i0 ∈ K) (hout : i0 ∉ L)
    (horder : orderOf i0 = 2)
    (hfixed : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i0)) = 5)
    (A : Subgroup m22PairStabilizer) (hA : A ≤ K) (hindex : A.relIndex K = 2) :
    Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 2 := by
  by_cases he : A = A0
  · subst A
    exact finrank_V2 D I
  · obtain ⟨i,hia,_,ho,hf⟩ :=
      exists_involution_mem_hyperplane D I hindecomp i0 hi0 hout horder hfixed A hA hindex he
    exact finrank_fixed_hyperplane_of_involution D A hA hindex i hia ho hf

end MathieuCode.M22Quintet.CocodeTransfer
