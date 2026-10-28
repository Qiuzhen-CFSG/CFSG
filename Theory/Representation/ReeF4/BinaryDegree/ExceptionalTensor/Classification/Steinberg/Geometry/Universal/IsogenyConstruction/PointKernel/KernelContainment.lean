module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.TorusLift
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Coroots
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.AlgebraicGroup.Tori.IsogenyPreimage

/-!
# Maximality of the connected torus lift in the kernel-containment argument

The published `isogenyTorusLift` is a maximal torus whenever the target
torus is maximal. The geometric proof lives in `Tori.IsogenyPreimage`.

For an incoming isogeny onto the semisimple F4 carrier, source semisimplicity
is supplied by `isogeny_source_semisimple`, and the kernel is central by
`isogeny_kernel_le_center_of_connected`. To put that kernel in this maximal
torus still requires the semisimple case of GLS3, Theorem 1.9.5(h), that the
center lies in every maximal torus. That step is not asserted here.

Source: GLS3, Sections 1.4 and 1.9--1.12, especially the incoming-isogeny
argument for Theorem 1.12.5(b), `refs/KGroup/GLS3/Chapter1.tex`.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The published connected lift of a maximal torus is maximal in the
source of the isogeny. -/
public theorem isogenyTorusLift_isMaximalTorus
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hφ : IsIsogeny φ)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T) :
    IsMaximalTorus (isogenyTorusLift φ T) :=
  φ.closedSubgroupPreimage_identityComponent_isMaximalTorus hφ T hT

end Theory.AlgebraicGroup
