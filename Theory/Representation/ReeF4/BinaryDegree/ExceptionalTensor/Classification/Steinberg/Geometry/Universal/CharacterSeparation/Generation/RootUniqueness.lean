module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Characters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.RootWeights
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentLines
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan

/-!
# Concrete F4 root-subgroup uniqueness

The literal root curves already realize their precise inverse-conjugation
characters. The tangent-line calculation gives multiplicity one, including
the higher-weight exclusion needed in characteristic two, once the full
identity tangent is spanned by its fixed space and the literal root tangents.
Scalar reparametrization then identifies any subgroup with the same weight
with the literal root subgroup.

In characteristic two, the concrete geometric dimension bound proves this
spanning statement. Thus uniqueness holds over every algebraically closed
field of characteristic two. The finite-field specialization retains the
source semisimplicity and maximal-torus hypotheses explicitly, although the
concrete proof does not need them. Only the literal root weights are treated;
no catalogue of all torus roots is asserted.

Source: GLS3, Theorem 1.9.5(b), `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section

namespace Theory.AlgebraicGroup.F4Chevalley

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The tangent-spanning input suffices for uniqueness at every literal F4 root weight. -/
theorem concreteRootSubgroup_eq_of_tangent_span
    (hspan : (⨆ i, concreteTangentSummand (k := k) i) = ⊤)
    (r : Root) (Y : ClosedSubgroup (Carrier (k := k)))
    (hY : IsTorusRootSubgroup splitTorus Y)
    (hweight : RootWeightEquation splitTorus Y (rootWeight r)) : Y = rootSubgroup r :=
  RootWeightSpaceMultiplicityOne.rootSubgroup_eq
    (concreteRoot_multiplicityOne_of_tangent_span hspan r)
    hY hweight (rootSubgroup_package r).1 (rootSubgroup_package r).2

/-- For each literal F4 root weight in characteristic two, every root subgroup
with that weight is the literal root subgroup. The geometric tangent-spanning
theorem discharges the premise of the scalar-parametrization argument. -/
theorem concreteRootSubgroup_eq [CharP k 2]
    (r : Root) (Y : ClosedSubgroup (Carrier (k := k)))
    (hY : IsTorusRootSubgroup splitTorus Y)
    (hweight : RootWeightEquation splitTorus Y (rootWeight r)) : Y = rootSubgroup r :=
  concreteRootSubgroup_eq_of_tangent_span concreteTangentSummand_iSup_eq_top r Y hY hweight

/-- GLS3 1.9.5(b) at each literal F4 root weight over the algebraic closure of
a finite field of characteristic two, with the source geometric hypotheses.
Existence and the precise weight equation are supplied by `rootSubgroup_package`;
this theorem supplies uniqueness. -/
theorem concreteRootSubgroup_eq_of_semisimple_maximalTorus
    {E : Type u} [Field E] [Finite E] [CharP E 2]
    (_hsemi : IsSemisimpleAlgebraicGroup (Carrier (k := AlgebraicClosure E)))
    (_hmax : IsMaximalTorus (splitTorus (k := AlgebraicClosure E)))
    (r : Root) (Y : ClosedSubgroup (Carrier (k := AlgebraicClosure E)))
    (hY : IsTorusRootSubgroup splitTorus Y)
    (hweight : RootWeightEquation splitTorus Y (rootWeight r)) : Y = rootSubgroup r :=
  concreteRootSubgroup_eq r Y hY hweight

end Theory.AlgebraicGroup.F4Chevalley
