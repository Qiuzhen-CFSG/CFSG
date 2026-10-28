module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Conjugation
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Flag
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.ChiefFactors
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Hyperplanes
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer

/-!
# Native quintet transvections, chief factors and hyperplane fixed spaces

The earlier faithful sextet transvections descend to the actual pair quotient,
with image the full radical at V1 inside V6. Their displacement pairing gives
the Q-equivariant dual of the actual conjugation module K. With the earlier
inner-involution facts and irreducible top section, the intrinsic fixed spaces
form the strict flag of dimensions 1, 2, 6, 10. Restriction of the displacement
pairing to A0 = K ∩ L identifies V6/V2 with its actual conjugation dual;
earlier H.14 irreducibility gives every chief factor of the flag.

The common-four calculation supplies the five-dimensional middle fixed space
needed by the generation argument. Indecomposability of K and irreducibility
of A0 force the orbit of one specified outer involution to meet every other
hyperplane. Its earlier fixed dimension then gives ambient fixed dimension
two. Together these prove four-subgroup generation and both hyperplane clauses.

Source: Aschbacher--Smith H.15.4, printed p.400, combined manuscript of 1 March
2004. The earlier M24 and H.14 inputs are explicit; the S5 branch must discharge
the intermediate top irreducibility hypothesis.
-/

public section
noncomputable section
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace MathieuCode.M22Quintet.CocodeTransfer

/-- The displacement duality uses the middle action of the constructed chief flag.
This supplies the precise action boundary used in the later code duality transfer. -/
theorem cocodeChiefFlag_middleDuality_equivariant
    [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation]
    [Representation.IsIrreducible (innerConjugation I)]
    (g : Q) (v : V6 ⧸ (V1.comap V6.subtype)) :
    middleDuality D ((cocodeChiefFlag D I).middleAction g v) =
      kernelConjugation.dual g (middleDuality D v) :=
  middleDuality_equivariant D g v

/-- The common-four dimension premise is discharged by faithful sextet transvections. -/
theorem fourFixedSpan_eq_top_of_transvections
    [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs)
    (hEK : E ≤ K) (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 4)
    [IsElementaryAbelian 2 E24] (hcard24 : Nat.card E24 = 4)
    (hfixed : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation E24) = 6)
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation] :
    fourFixedSpan m22OuterCocodeRepresentation K = ⊤ :=
  fourFixedSpan_eq_top_of_sextet_data (by rw [D.card_kernel]; decide)
    D.kernel_le D.displacement hEK hE hcard hfixed (finrank_common_middle_fixed D hcard24)

/-- The source xi conclusion uses the same proved middle fixed dimension. -/
theorem fixedSpaceSpan_eq_top_of_transvections
    [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs)
    (hEK : E ≤ K) (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 4)
    [IsElementaryAbelian 2 E24] (hcard24 : Nat.card E24 = 4)
    (hfixed : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation E24) = 6)
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation]
    (A : Subgroup m22PairStabilizer) (hindex : A.relIndex K = 2) :
    fixedSpaceSpan m22OuterCocodeRepresentation A = ⊤ :=
  fixedSpaceSpan_eq_top_of_fourFixedSpan _ hindex
    (fourFixedSpan_eq_top_of_transvections D hEK hE hcard hcard24 hfixed)

/-- Four-subgroup generation and both hyperplane conclusions follow from the
earlier sextet action, common-four facts and one marked outer involution.
The middle fixed dimension five and all hyperplane witnesses are proved above. -/
theorem cocode_generation_and_hyperplane_fixed_dimensions
    [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation]
    (hindecomp : ∀ U W : Subrepresentation kernelConjugation,
      IsCompl U W → U = ⊥ ∨ W = ⊥)
    (i0 : m22PairStabilizer) (hi0 : i0 ∈ K) (hout : i0 ∉ L)
    (horder : orderOf i0 = 2)
    (hfixed : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i0)) = 5)
    (hEK : E ≤ K) (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 4)
    [IsElementaryAbelian 2 E24] (hcard24 : Nat.card E24 = 4)
    (hcommon : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation E24) = 6) :
    fourFixedSpan m22OuterCocodeRepresentation K = ⊤ ∧
      ∀ A : Subgroup m22PairStabilizer, A ≤ K → A.relIndex K = 2 →
        fixedSpaceSpan m22OuterCocodeRepresentation A = ⊤ ∧
          Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 2 := by
  have hgen := fourFixedSpan_eq_top_of_transvections D hEK hE hcard hcard24 hcommon
  refine ⟨hgen, fun A hA hindex => ⟨?_, ?_⟩⟩
  · exact fixedSpaceSpan_eq_top_of_fourFixedSpan m22OuterCocodeRepresentation hindex hgen
  · exact finrank_fixed_hyperplane D I hindecomp i0 hi0 hout horder hfixed A hA hindex

end MathieuCode.M22Quintet.CocodeTransfer
