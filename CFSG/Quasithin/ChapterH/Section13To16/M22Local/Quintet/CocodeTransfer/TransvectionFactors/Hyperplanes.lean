module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Hyperplanes

/-!
# The hyperplane fixed dimensions in H.15.4(3)

The actual Q-orbit of one marked outer involution spans K and meets every
hyperplane other than A0 = K ∩ L. Conjugation preserves its five-dimensional
ambient fixed space, so the transvection argument gives fixed dimension two.
The distinguished hyperplane is handled by the already proved dimension of V2.

These are conditional adapters: the source assembly must supply the earlier
H.14 irreducibility and indecomposability facts, the top quotient, and the one
marked involution from the appropriate outer class. No witness for each
hyperplane and no hyperplane fixed dimension is assumed. The separate xi
conclusion of H.15.4(3) remains with the transvection-factors assembly.

Source: Aschbacher--Smith H.15.4(3), printed p.400, using H.14.3(2) and
H.14.4, printed pp.397--398, combined manuscript of 1 March 2004.
-/

public section
noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.Section13To16
open MathieuCode MathieuCode.M22Quintet Representation.BinaryOffender
open MathieuCode.M22Quintet.CocodeTransfer

/-- Every hyperplane other than the literal K ∩ L meets the specified outer Q-orbit. -/
theorem m22Quintet_hyperplane_contains_conjugate [IsElementaryAbelian 2 K]
    (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    (hindecomp : ∀ U W : Subrepresentation kernelConjugation,
      IsCompl U W → U = ⊥ ∨ W = ⊥)
    (i0 : m22PairStabilizer) (hi0 : i0 ∈ K) (hout : i0 ∉ L)
    (A : Subgroup m22PairStabilizer) (hA : A ≤ K) (hindex : A.relIndex K = 2)
    (hne : A ≠ A0) : ∃ g : Q, g.val * i0 * g.val⁻¹ ∈ A :=
  exists_conjugate_mem_hyperplane D I hindecomp i0 hi0 hout A hA hindex hne

/-- Selection retains the chosen outer involution class and its ambient fixed dimension. -/
theorem m22Quintet_hyperplane_contains_source_involution [IsElementaryAbelian 2 K]
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
        (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i)) = 5 :=
  exists_involution_mem_hyperplane D I hindecomp i0 hi0 hout horder hfixed A hA hindex hne

/-- The fixed-dimension clause of H.15.4(3), with all earlier source inputs explicit. -/
theorem m22Quintet_hyperplane_fixed_dimension [IsElementaryAbelian 2 K]
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
    Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 2 :=
  finrank_fixed_hyperplane D I hindecomp i0 hi0 hout horder hfixed A hA hindex

end CFSG.Quasithin.ChapterH.Section13To16
