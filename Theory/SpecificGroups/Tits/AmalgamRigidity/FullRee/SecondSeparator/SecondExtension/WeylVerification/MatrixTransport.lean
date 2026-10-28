module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.WeylVerification.BinaryCheck
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.RootVerification

/-!
# Transport of the extra Weyl identity to the literal full Ree group

An injective reindexing of the actual Chevalley matrices carries the first
relative-root word and the Parrott generators to their binary tables. This
transports the extra checked conjugation equation to the fixed Ree group.
The local comparison lemmas follow `ParabolicMarkedComparison.RootVerification`;
no choice of an abstract group isomorphism replaces the marked matrices.

Source: Shinoda (1975), pp.81–83; Parrott (1972), p.683.
-/

public section
noncomputable section
namespace Tits.AmalgamRigidity.FullRee.SecondExtension.WeylVerification
open ReeTwo.ParabolicMarkedComparison
open ReeF4 ReeF4.DerivedTits.Realization
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4.DerivedTits.Realization.TransportComparison
open ReeF4.Parabolics.Binary.FixedGeometry

private def renumber (e : F4Chevalley.BasisIndex ≃ Fin 52) :
    MatrixUnits 0 →* (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ :=
  Units.map (Matrix.reindexRingEquiv (CoefficientField 0) e).toMonoidHom

private def extendScalars : Products.BinaryUnit →*
    (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ :=
  Units.map binaryScalar.mapMatrix.toMonoidHom

private theorem compare_simple (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (b : Bool) (i : Fin 4) :
    renumber e (F4Chevalley.rootCurve (signedSimpleRoot b i) 1) =
      extendScalars (ReeF4.DerivedTits.Realization.Binary.simpleAssignment b i) :=
  Units.ext (h b i)

private theorem compare_tits (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (w : List (Fin 4)) :
    renumber e (WordRelations.titsUnit (w.map typeF4RootPairing_baseEquiv)) =
      extendScalars (Products.weylWord w) := by
  let := typeF4RootPairing.indexNeg
  induction w with
  | nil => simp [Products.weylWord]
  | cons i w ih =>
    have hp := compare_simple e h false i
    have hn := compare_simple e h true i
    change renumber e (F4Chevalley.rootCurve (typeF4SimpleRootIndex i) 1) = _ at hp
    change renumber e (F4Chevalley.rootCurve (-typeF4SimpleRootIndex i) 1) = _ at hn
    simp only [List.map_cons, WordRelations.titsUnit_cons,
      typeF4RootPairing_baseEquiv_val, CharTwo.neg_eq, map_mul, hp, hn, ih]
    simp [Products.weylWord, Products.weyl, map_mul]

private theorem compare_root (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (i : Fin 24) :
    renumber e (F4Chevalley.rootCurve (positiveRoot i) 1) =
      extendScalars (Products.root i) := by
  have hp := compare_simple e h false (routeSimple i)
  change renumber e (F4Chevalley.rootCurve (typeF4SimpleRootIndex (routeSimple i)) 1) = _ at hp
  rw [rootCurve_route]
  simp only [map_mul, map_inv, compare_tits e h, hp]
  simp only [Products.root, Products.transported, map_mul, map_inv]

private theorem compare_quartet (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (i : Fin 4) :
    renumber e (quartetElement i).val = extendScalars (Products.quartet i) := by
  rw [quartetElement_eq]
  change renumber e (F4Chevalley.rootCurve (quartetRoots i 0) 1 *
    F4Chevalley.rootCurve (quartetRoots i 1) 1 *
    F4Chevalley.rootCurve (quartetRoots i 3) 1) = _
  simp only [TransportComparison.quartetRoots_eq, map_mul, compare_root e h,
    Products.quartet]

private def numbered (e : F4Chevalley.BasisIndex ≃ Fin 52) :
    Model 0 →* (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ :=
  (renumber e).comp ((SplitGroup 0).subtype.comp (toSplitGroup 0))

private theorem numbered_injective (e : F4Chevalley.BasisIndex ≃ Fin 52) :
    Function.Injective (numbered e) := by
  intro x y he
  apply toSplitGroup_injective 0
  apply Subtype.ext
  apply Units.ext
  apply (Matrix.reindexRingEquiv (CoefficientField 0) e).injective
  exact congrArg Units.val he

private theorem compare_generator (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (i : Tits.ParrottGenerator) :
    numbered e (Tits.ExceptionalParabolics.FullRee.atlasEmbedding (Tits.atlas1600ParrottAssignment i)) =
      extendScalars (ReeF4.DerivedTits.Realization.Binary.assignment i) := by
  change renumber e ((toSplitGroup 0 (Tits.ExceptionalParabolics.FullRee.atlasEmbedding _)).val) = _
  rw [Tits.ExceptionalParabolics.FullRee.atlasEmbedding_generator_matrix]
  exact Units.ext (matrixComparison_of_simpleMatrixComparison e h i)

private theorem compare_one (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) :
    numbered e Ambient.rootOne = extendScalars ReeTwo.ParabolicMarkedComparison.Binary.rootOne := by
  change renumber e ((toSplitGroup 0 Ambient.rootOne).val) = _
  rw [toSplitGroup_apply]
  exact compare_quartet e h 0


/-- The linear Weyl lift interchanges the literal first and fourth source roots. -/
theorem ambient_reflection_rootOne :
    weylLift 0 .linear * Ambient.rootOne * (weylLift 0 .linear)⁻¹ =
      Ambient.root 1 := by
  obtain ⟨e, he⟩ := exists_simpleMatrixComparison
  have hr : weylLift 0 .linear = Tits.ExceptionalParabolics.FullRee.atlasEmbedding
      (Tits.atlas1600ParrottAssignment .r8) := (Ambient.atlas_generator .r8).symm
  have hs : Ambient.root 1 = Tits.ExceptionalParabolics.FullRee.atlasEmbedding
      (Tits.atlas1600ParrottAssignment .s7) * Ambient.rootOne := by
    rw [Ambient.atlas_generator]
    simp only [Ambient.parrottWord, inv_mul_cancel_right]
  apply numbered_injective e
  rw [hr, hs]
  simpa only [map_mul, map_inv, compare_generator e he, compare_one e he] using
    congrArg extendScalars BinaryCheck.reflection_rootOne

end Tits.AmalgamRigidity.FullRee.SecondExtension.WeylVerification
