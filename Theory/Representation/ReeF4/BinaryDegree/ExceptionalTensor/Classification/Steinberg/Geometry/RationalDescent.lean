module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters

/-!
# Rational-point descent into the finite split F4 group

A point of the literal algebraic F4 carrier whose presented coordinates lie
in the finite coefficient field image belongs to the image of the finite
root-generated split group. This holds for every coefficient-field embedding
into an algebraically closed field of characteristic two.

Bruhat parameter recovery supplies two ordered root products, four direct
coroot units, and a Weyl word over the coefficient field. The same literal
word in `SplitGroup` is a preimage: root-generator transport, the coroot
convention `n(t) n(1)⁻¹`, and the parameter-one Weyl words identify its image
with the original point. All coverage and parameter-recovery premises are
discharged by `BruhatParameters`.

This supplies the descent input of
`Geometry.modelEmbedding_range_eq_fixed_of_descent`.
Source: Steinberg, *Lectures on Chevalley Groups*, Theorem 7 and its third
corollary, pp. 64–67 (`refs/KGroup/GLS3/Chapter2St1.tex`, lines 1017–1064).
The repeated group subscripts in the transcribed corollary are interpreted
as in its proof: the smaller-field group is the intersection of the
larger-field group with the matrices over the smaller field.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent
open BruhatParameters

variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- Rational coordinates give actual membership in the finite root-generated
split group image, with no additional factorization or fixed-point premise. -/
theorem mem_splitEmbedding_range_of_coordinates {k : ℕ}
    (f : CoefficientField k →+* F) (x : PointGroup F)
    (hx : ∀ i : (F4Chevalley.Carrier (k := F)).Coordinates, x.val i ∈ f.range) :
    x ∈ (splitEmbedding f).range := by
  obtain ⟨o, o', hcover⟩ := exists_positiveOrderings_rational_cell_cover f
  obtain ⟨a, b, t, l, hcell⟩ := hcover x hx
  refine ⟨finiteRootProduct k (fun i => (o i).val) a * finiteCorootProduct k t *
    finiteRootProduct k (fun i => -(o' i).val) b * finiteWeylWord k l, ?_⟩
  exact (splitEmbedding_cell f _ _ a t b l).trans hcell.symm

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent
