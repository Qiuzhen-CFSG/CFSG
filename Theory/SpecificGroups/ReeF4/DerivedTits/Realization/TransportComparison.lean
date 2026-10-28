module
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.SimpleData
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.TransportComparison.BinaryProducts

/-!
# Transport from the eight simple matrices to Parrott's ten words

A comparison of the signed simple curves transports along each certified Weyl
route. Multiplicativity then gives the eight relative root elements and the ten
Parrott substitutions, whose binary products have been checked separately.
Only the stated simple-matrix comparison is assumed; the basis enumeration and
that comparison belong to the unconditional realization's assembly.

Source: Parrott (1972), printed p.683, its scan-checked transcription at
`refs/original/n-group-global/parrott-tits-presentation.md`, and GLS3 §§2.3–2.4.
-/

public section
noncomputable section
namespace ReeF4.DerivedTits.Realization
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open TransportComparison
open Parabolics.Binary.FixedGeometry

private def renumber (e : F4Chevalley.BasisIndex ≃ Fin 52) :
    MatrixUnits 0 →* (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ :=
  Units.map (Matrix.reindexRingEquiv (CoefficientField 0) e).toMonoidHom

private def extendScalars : Products.BinaryUnit →*
    (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ :=
  Units.map binaryScalar.mapMatrix.toMonoidHom

private theorem compare_simple (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (b : Bool) (i : Fin 4) :
    renumber e (F4Chevalley.rootCurve (signedSimpleRoot b i) 1) =
      extendScalars (Binary.simpleAssignment b i) :=
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

private theorem compare_pair (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (i : Fin 4) :
    renumber e (pairElement i).val = extendScalars (Products.pair i) := by
  rw [pairElement_eq]
  change renumber e (F4Chevalley.rootCurve (pairRoots i 0) 1 *
    F4Chevalley.rootCurve (pairRoots i 1) 1) = _
  simp only [TransportComparison.pairRoots_eq, map_mul, compare_root e h,
    Products.pair]

private theorem compare_quartet (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (i : Fin 4) :
    renumber e (quartetElement i).val = extendScalars (Products.quartet i) := by
  rw [quartetElement_eq]
  change renumber e (F4Chevalley.rootCurve (quartetRoots i 0) 1 *
    F4Chevalley.rootCurve (quartetRoots i 1) 1 *
    F4Chevalley.rootCurve (quartetRoots i 3) 1) = _
  simp only [TransportComparison.quartetRoots_eq, map_mul, compare_root e h,
    Products.quartet]

private theorem compare_relative (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (i : Fin 8) :
    renumber e (u i).val = extendScalars (Products.relative i) := by
  fin_cases i <;>
    simp [u, Products.relative, compare_pair e h, compare_quartet e h]

private theorem compare_generator (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (g : Tits.ParrottGenerator) :
    renumber e (assignment g).val = extendScalars (Products.generator g) := by
  cases g <;>
    simp only [assignment, Products.generator, Subgroup.coe_mul, Subgroup.coe_inv,
      map_mul, map_inv, compare_relative e h, simpleWord_coe]
  · exact compare_tits e h (sideWord .suzuki)
  · exact compare_tits e h (sideWord .linear)

/-- The eight signed simple comparisons imply the genuine comparison of all ten
root/Weyl words, with Parrott's substitutions and multiplication order. -/
theorem matrixComparison_of_simpleMatrixComparison
    (e : F4Chevalley.BasisIndex ≃ Fin 52) (h : SimpleMatrixComparison e) :
    MatrixComparison e := by
  intro g
  have hg := congrArg Units.val (compare_generator e h g)
  change Matrix.reindex e e (assignment g).val.val =
    (Products.generator g).val.map binaryScalar at hg
  exact hg.trans (congrArg (fun M => M.map binaryScalar) (Products.generator_val g))

end ReeF4.DerivedTits.Realization
