module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SplitTorus
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.CorootConvention
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.Geometry
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.HighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.Realization
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Assembly

/-!
# Concrete algebraic F4 realization: Frobenius and fixed-point descent

The shared geometry interface currently supplies the actual coordinate
Frobenius morphism, consequences of the exceptional root formula, the concrete
rank-four split torus and its representation coroots, the literal root-subgroup
parametrizations and weights, and the reduction of full
fixed-point coverage to rational-point descent. Construction
of the exceptional morphism and of the concrete semisimple and universal
geometry have their separate owners. The positive and opposite torus/root
candidates are now closed, connected and solvable, with their literal
root-generated groups as unipotent radicals and a dense open product.
Their proved Borel maximality and opposite separation now give the unconditional
opposite big cell for this same torus and root datum. The checked
coroot-convention obstruction rules out same-parameter identification with
`algebraicCorootElement`. Inverting the parameter gives the correct Cartan
exponents for the inverse-conjugation root weights. The corrected regular
cocharacters, labelled root datum, and direct left-character boundary are now
constructed. In characteristic two the concrete tangent-spanning theorem and
split-torus maximality give the actual standard-base F4 root-system model,
without additional geometric premises. Every model cocharacter is identified
with its literal representation coroot word at the inverse parameter. The
original positive labels and the positive representation-coroot eigenvalue
convention are preserved.

The underlying carrier and root/coroot words are the literal ones used by the
Ree representation parameters. Sources: GLS3, Sections 1.9--1.15, and Steinberg,
*Lectures on Chevalley Groups*, Theorems 7 and 28.
-/
