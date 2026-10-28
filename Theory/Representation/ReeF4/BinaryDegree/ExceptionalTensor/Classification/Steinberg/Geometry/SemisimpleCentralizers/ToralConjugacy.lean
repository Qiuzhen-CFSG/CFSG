module
public import Theory.AlgebraicGroup.Tori.NormalizerConjugacy
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.TorusCoordinates

/-!
# Ambient toral conjugacy in actual F4 coordinates

Adjust an ambient conjugator inside the point centralizer to normalize the
literal maximal split torus. Its proved normalizer action then identifies the
raw and positive left-character evaluations by the actual integral Weyl action.
No connectedness assumption on the point centralizer is used. This discharges
the toral conjugacy direction used in the Ree fundamental-coordinate class map.
Source: Steinberg, *Endomorphisms of Linear Algebraic Groups*, §3.9(5).
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
open BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
attribute [local instance] torusGroup

theorem exists_normalizer_of_toral_conjugacy
    (x y : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (hxy : IsConj ((F4Chevalley.splitTorus (k := F)).includePoint x)
      ((F4Chevalley.splitTorus (k := F)).includePoint y)) :
    ∃ n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup,
      (torusConjugation n).onPoints x = y := by
  obtain ⟨n, hn, he⟩ := SemisimpleCentralizerTori.normalizer_conjugator_of_toral_conjugacy
    RootModel.Corrected.splitTorus_isMaximal
    ((F4Chevalley.splitTorus (k := F)).pointEquiv x).property
    ((F4Chevalley.splitTorus (k := F)).pointEquiv y).property hxy
  refine ⟨⟨n, hn⟩, ?_⟩
  apply (F4Chevalley.splitTorus (k := F)).inclusion_injective
  change (F4Chevalley.splitTorus (k := F)).includePoint _ =
    (F4Chevalley.splitTorus (k := F)).includePoint y
  rw [torusConjugation_include]
  exact he

theorem exists_weyl_of_toral_conjugacy
    (x y : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (hxy : IsConj ((F4Chevalley.splitTorus (k := F)).includePoint x)
      ((F4Chevalley.splitTorus (k := F)).includePoint y)) :
    ∃ w : F4WeightAction.Weyl, ∀ a,
      rawEvaluation y a = rawEvaluation x (F4WeightAction.representation w a) := by
  obtain ⟨n, hn⟩ := exists_normalizer_of_toral_conjugacy x y hxy
  refine ⟨normalizerWeyl n⁻¹, fun a => ?_⟩
  have h := rawEvaluation_normalizer n⁻¹ x a
  rw [inv_inv, hn] at h
  exact h.symm

theorem exists_weyl_leftCharacter_of_toral_conjugacy
    (x y : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety)
    (hxy : IsConj ((F4Chevalley.splitTorus (k := F)).includePoint x)
      ((F4Chevalley.splitTorus (k := F)).includePoint y)) :
    ∃ w : F4WeightAction.Weyl, ∀ a,
      (RootModel.Corrected.leftCharacter a).pointCharacter y =
        (RootModel.Corrected.leftCharacter (F4WeightAction.representation w a)).pointCharacter x := by
  obtain ⟨n, hn⟩ := exists_normalizer_of_toral_conjugacy x y hxy
  refine ⟨normalizerWeyl n⁻¹, fun a => ?_⟩
  rw [leftCharacter_normalizer, weightAction_apply, inv_inv, hn]
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
