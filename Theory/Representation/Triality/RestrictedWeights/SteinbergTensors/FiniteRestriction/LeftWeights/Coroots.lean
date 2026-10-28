module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftWeights
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
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

theorem Geometry.leftSimpleCoroot_apply (S : Geometry K) (i : Fin 4)
    (t : Variety.Point (KMult k)) :
    (S.leftSimpleCoroot i).onPoints t = (S.roots.rootCocharacter (S.simpleRoot i).val).onPoints t⁻¹ := rfl

theorem Geometry.leftSimpleCoroot_include (S : Geometry K) (i : Fin 4)
    (t : Variety.Point (KMult k)) :
    S.torus.includePoint ((S.leftSimpleCoroot i).onPoints t) =
      (S.torus.includePoint ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints t))⁻¹ := by
  change S.torus.inclusion.onPoints ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints t⁻¹) = _
  rw [map_inv, map_inv]
  rfl

theorem Geometry.leftSimpleCoroot_morphism (S : Geometry K) (i : Fin 4) :
    S.leftSimpleCoroot i = S.torusInversion.comp (S.roots.rootCocharacter (S.simpleRoot i).val) :=
  LeftWeights.leftCocharacter_eq_torusInversion _ _

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
