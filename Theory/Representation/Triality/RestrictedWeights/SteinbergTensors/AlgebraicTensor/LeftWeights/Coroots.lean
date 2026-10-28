module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights.Roots

/-!
# Actual left simple-coroot comparison equations

These formulas compare regular maps and their included points, preserving the
source coroot word. The parameter inversion, not a change of root subgroup,
gives the direct-conjugation convention of Steinberg (6.1).
Source: GLS3 1.12.1 and Steinberg §13.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K]

theorem D4Geometry.leftSimpleCoroot_apply (S : D4Geometry K) (i : Fin 4)
    (t : Variety.Point (KMult k)) :
    (S.leftSimpleCoroot i).onPoints t = (S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))).onPoints t⁻¹ := rfl

theorem D4Geometry.leftSimpleCoroot_include (S : D4Geometry K) (i : Fin 4)
    (t : Variety.Point (KMult k)) :
    S.torus.includePoint ((S.leftSimpleCoroot i).onPoints t) =
      (S.torus.includePoint ((S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))).onPoints t))⁻¹ := by
  change S.torus.inclusion.onPoints ((S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))).onPoints t⁻¹) = _
  rw [map_inv, map_inv]
  rfl

theorem D4Geometry.leftSimpleCoroot_morphism (S : D4Geometry K) (i : Fin 4) :
    S.leftSimpleCoroot i = S.torusInversion.comp (S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))) :=
  LeftWeights.leftCocharacter_eq_torusInversion _ _

/-- The left simple coroot is the literal Chevalley h word at the inverse scalar. -/
theorem D4Geometry.leftSimpleCoroot_word (S : D4Geometry K) (i : Fin 4)
    (t : Variety.Point (KMult k)) :
    S.torus.includePoint ((S.leftSimpleCoroot i).onPoints t) =
      S.chevalley.h (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))
        (dPointEquiv 1 t 0)⁻¹ := by
  rw [S.leftSimpleCoroot_apply, S.coroot_spec, LeftWeights.dPointEquiv_inverse]
  rfl

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
