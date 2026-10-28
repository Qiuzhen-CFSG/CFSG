module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Characters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Lattice
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.RootKernel
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation

/-!
# Semisimple F4 character separation

For any actual F4 root model, generation by its root subgroups and maximal
torus identifies the common root kernel with a subgroup of the finite center.
The Cartan adjustment argument then proves injectivity of the four coroot
coordinates. The theorem applies in particular to the literal F4 Chevalley
carrier over the algebraic closure of a finite characteristic-two field.

On this literal carrier, torus conjugacy and concrete root-weight uniqueness
identify the model's root subgroups with conjugates of the Chevalley root
curves. Their generation theorem discharges the geometric prerequisite, so
the final character-separation theorem requires only semisimplicity and the
supplied root model. Its base need not be the displayed standard F4 base.
Source: GLS3, Proposition 1.14.1(a), with the root-generation input of
Theorem 1.9.5(i), `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem

universe u

namespace Theory.AlgebraicGroup.RootSystemModel
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- Geometric root generation completes the semisimple F4 character-separation argument. -/
theorem f4CorootCoordinates_injective_of_rootGeneration
    (M : RootSystemModel typeF4RootPairingULift G)
    (hsemi : IsSemisimpleAlgebraicGroup G)
    (hgen : RootSubgroupGenerated M.rootData Set.univ ⊔ M.torus.toSubgroup = ⊤) :
    Function.Injective M.f4CorootCoordinates :=
  M.f4CorootCoordinates_injective_of_rootKernel_finite
    (rootWeightKernel_finite_of_rootGeneration M.rootData M.realization M.maximalTorus.1 hsemi hgen)

/-- GLS3 1.14.1(a): the four displayed simple coroots separate characters of
the maximal torus of any supplied semisimple F4 model over the algebraic
closure of a finite characteristic-two field. Root generation is proved for
this literal carrier; no generation or character-separation premise remains. -/
theorem f4CorootCoordinates_injective
    {E : Type u} [Field E] [Finite E] [CharP E 2]
    (M : RootSystemModel typeF4RootPairingULift
      (F4Chevalley.Carrier (k := AlgebraicClosure E)))
    (hsemi : IsSemisimpleAlgebraicGroup
      (F4Chevalley.Carrier (k := AlgebraicClosure E))) :
    Function.Injective M.f4CorootCoordinates :=
  M.f4CorootCoordinates_injective_of_rootGeneration hsemi (M.f4_rootGeneration hsemi)

end Theory.AlgebraicGroup.RootSystemModel
