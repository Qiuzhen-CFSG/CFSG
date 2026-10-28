module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.Transport
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.Displacements
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.PlaneGeometry
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification

/-!
# Quadratic actors on the SL₃(4) natural-plus-dual module

Given faithful natural-plus-dual coordinates on a normal SL₃(4) subgroup,
the binary normalizer calculation puts every elementary quadratic actor of
action ratio at most two inside that subgroup. The natural-module displacement
flag then places it in one of the two root-plane orientations. The fixed-space
calculation gives either rank two and codimension four with a full root group,
or rank three or four and codimension six with a full root and an independent
root. Equivariant subgroup transport preserves the original actor, both
numerical invariants and the actual matrix markings.

`criticalShapes_of_equivariant` assembles this classification without assuming
component containment, normalizer forms or output markings. The given module
equivalence remains an input to this intrinsic result; its construction in
the source setting belongs to the source-theorem assembly.

Source: Aschbacher--Smith, proof of 13.8.20, printed p.955 (PDF p.972),
combined manuscript of 1 March 2004.
-/

public section
namespace Representation.SL3FourNaturalDual.QuadraticActors
open BinaryOffender

/-- Every elementary quadratic actor of rank at most four and action ratio
at most two has the exact root markings and numerical alternatives used in
13.8.20, provided the faithful action restricts to the specified natural-plus-dual
SL₃(4) module. Component containment and the matrix classification are proved,
while construction of the equivariant module identification is an explicit input. -/
theorem criticalShapes_of_equivariant
    {J U : Type*} [Group J] [Finite J] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U) (hρ : Function.Injective ρ)
    (K : Subgroup J) [K.Normal] (eK : K ≃* SL) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u))
    (A : Subgroup J) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) (hrank : rank A ≤ 4) :
    CriticalShapes ρ A := by
  have hAK : A ≤ K :=
    NormalizerReduction.actor_le_of_equivariant ρ hρ K eK E hE A hA hq hsmall
  apply criticalShapes_of_modelActor ρ K eK E hE A hAK
  apply criticalShapes_internal (modelActor K eK A)
  · exact modelActor_elementary K eK A hAK hA
  · exact modelActor_quadratic ρ K eK E hE A hq
  · rwa [modelActor_fixedCodim ρ K eK E hE A hAK, modelActor_rank K eK A hAK]
  · rwa [modelActor_rank K eK A hAK]

end Representation.SL3FourNaturalDual.QuadraticActors
