module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.NormalizerCoherence.MatrixLocalPaths.WeylGeometry.Data

/-!
# Checked Schreier corrections in the F4 Weyl group

For each of 48 root states and each of four simple reflections, the element
`v⁻¹ * sᵢ * u` has a path between the signed simple roots marking the two
states. Here `u` and `v` are their chosen root representatives. Eighty tree
edges cancel algebraically. The other corrections are checked on all four
simple-root coordinate vectors, then transported to equality in the actual
Weyl group. Every pair segment separately checks its signed-root endpoints.

There are at most three pair segments in a correction. These certificates
retain the entire stabilizer element, which is essential in GLS3 Lemma 2.9.4.
`source/generate_certificates.py` reproduces the finite search and declarations;
its output is verified by Lean's kernel. No external computation is trusted.
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths.WeylGeometry

private lemma tree_edge_forward (u : List (Fin 4)) (i : Fin 4) (x : Mark) :
    WeylPairPath ((numberedProd (i :: u))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd u) x x := by
  have he : (numberedProd (i :: u))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd u = 1 := by
    rw [numberedProd_cons, mul_assoc, inv_mul_cancel]
  rw [he]
  exact WeylPairPath.refl x

private lemma tree_edge_reverse (v : List (Fin 4)) (i : Fin 4) (x : Mark) :
    WeylPairPath ((numberedProd v)⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (i :: v)) x x := by
  have he : (numberedProd v)⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (i :: v) = 1 := by
    rw [numberedProd_cons]
    simp only [mul_assoc, ← mul_assoc (typeF4RootPairing_base.simpleReflection _),
      RootPairing.Base.simpleReflection_mul_self, one_mul, inv_mul_cancel]
  rw [he]
  exact WeylPairPath.refl x

-- BEGIN GENERATED EDGE CERTIFICATES
private theorem edge_0 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 0 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 0))
      (routeMark 0) (routeMark (nextState 0 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [])
      (true, 0) (false, 0)
    apply edge_from_path (p := [0])
    · exact pair_path 0 1 [true] true true false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [])
      (true, 0) (true, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [])
      (true, 0) (true, 0)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] true true true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [])
      (true, 0) (true, 0)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] true true true true (by decide)
    · decide

private theorem edge_1 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 1 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 1))
      (routeMark 1) (routeMark (nextState 1 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [])
      (true, 1) (true, 0)
    apply edge_from_path (p := [1, 0])
    · exact pair_path 0 1 [false, true] true false true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [])
      (true, 1) (false, 1)
    apply edge_from_path (p := [1])
    · exact pair_path 0 1 [false] true false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [])
      (true, 1) (true, 1)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [])
      (true, 1) (true, 1)
    apply edge_from_path (p := [3])
    · exact pair_path 1 3 [false] true true true true (by decide)
    · decide

private theorem edge_2 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 2 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 2))
      (routeMark 2) (routeMark (nextState 2 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [])
      (true, 2) (true, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] true false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [])
      (true, 2) (true, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [])
      (true, 2) (false, 2)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] true false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [])
      (true, 2) (true, 2)
    exact tree_edge_forward _ _ _

private theorem edge_3 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 3 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 3))
      (routeMark 3) (routeMark (nextState 3 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [])
      (true, 3) (true, 3)
    apply edge_from_path (p := [0])
    · exact pair_path 0 3 [true] true false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [])
      (true, 3) (true, 3)
    apply edge_from_path (p := [1])
    · exact pair_path 1 3 [true] true false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [])
      (true, 3) (true, 2)
    apply edge_from_path (p := [3, 2])
    · exact pair_path 2 3 [false, true] true false true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [])
      (true, 3) (false, 3)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] true false false false (by decide)
    · decide

private theorem edge_4 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 4 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 4))
      (routeMark 4) (routeMark (nextState 4 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [])
      (false, 0) (true, 0)
    apply edge_from_path (p := [0])
    · exact pair_path 0 1 [true] false true true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [])
      (false, 0) (false, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [])
      (false, 0) (false, 0)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] false true false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [])
      (false, 0) (false, 0)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] false true false true (by decide)
    · decide

private theorem edge_5 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 5 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 5))
      (routeMark 5) (routeMark (nextState 5 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [])
      (false, 1) (false, 0)
    apply edge_from_path (p := [1, 0])
    · exact pair_path 0 1 [false, true] false false false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [])
      (false, 1) (true, 1)
    apply edge_from_path (p := [1])
    · exact pair_path 0 1 [false] false false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [])
      (false, 1) (false, 1)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [])
      (false, 1) (false, 1)
    apply edge_from_path (p := [3])
    · exact pair_path 1 3 [false] false true false true (by decide)
    · decide

private theorem edge_6 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 6 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 6))
      (routeMark 6) (routeMark (nextState 6 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [])
      (false, 2) (false, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] false false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [])
      (false, 2) (false, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [])
      (false, 2) (true, 2)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] false false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [])
      (false, 2) (false, 2)
    exact tree_edge_forward _ _ _

private theorem edge_7 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 7 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 7))
      (routeMark 7) (routeMark (nextState 7 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [])
      (false, 3) (false, 3)
    apply edge_from_path (p := [0])
    · exact pair_path 0 3 [true] false false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [])
      (false, 3) (false, 3)
    apply edge_from_path (p := [1])
    · exact pair_path 1 3 [true] false false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [])
      (false, 3) (false, 2)
    apply edge_from_path (p := [3, 2])
    · exact pair_path 2 3 [false, true] false false false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [])
      (false, 3) (true, 3)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] false false true false (by decide)
    · decide

private theorem edge_8 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 8 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 8))
      (routeMark 8) (routeMark (nextState 8 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [1])
      (true, 0) (true, 1)
    apply edge_from_path (p := [0, 1])
    · exact pair_path 0 1 [true, false] true true true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [1])
      (true, 0) (true, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [1])
      (true, 0) (true, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] true true true true (by decide)
    · decide

private theorem edge_9 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 9 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 9))
      (routeMark 9) (routeMark (nextState 9 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2])
      (true, 1) (true, 0)
    apply edge_from_path (p := [1, 0])
    · exact pair_path 0 1 [false, true] true false true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2])
      (true, 1) (true, 1)
    apply edge_from_path (p := [2, 1, 2])
    · exact pair_path 1 2 [false, true, false] true true true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2])
      (true, 1) (true, 1)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [3, 2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2])
      (true, 1) (true, 1)
    exact tree_edge_forward _ _ _

private theorem edge_10 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 10 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 10))
      (routeMark 10) (routeMark (nextState 10 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [1])
      (true, 2) (true, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [1])
      (true, 2) (true, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] true false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [1])
      (true, 2) (true, 2)
    exact tree_edge_forward _ _ _

private theorem edge_11 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 11 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 11))
      (routeMark 11) (routeMark (nextState 11 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3])
      (true, 2) (true, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] true false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3])
      (true, 2) (true, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3])
      (true, 2) (true, 3)
    apply edge_from_path (p := [2, 3])
    · exact pair_path 2 3 [true, false] true true true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3])
      (true, 2) (true, 2)
    exact tree_edge_reverse _ _ _

private theorem edge_12 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 12 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 12))
      (routeMark 12) (routeMark (nextState 12 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [1])
      (false, 0) (false, 1)
    apply edge_from_path (p := [0, 1])
    · exact pair_path 0 1 [true, false] false true false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [1])
      (false, 0) (false, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [1])
      (false, 0) (false, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] false true false true (by decide)
    · decide

private theorem edge_13 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 13 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 13))
      (routeMark 13) (routeMark (nextState 13 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2])
      (false, 1) (false, 0)
    apply edge_from_path (p := [1, 0])
    · exact pair_path 0 1 [false, true] false false false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2])
      (false, 1) (false, 1)
    apply edge_from_path (p := [2, 1, 2])
    · exact pair_path 1 2 [false, true, false] false true false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2])
      (false, 1) (false, 1)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [3, 2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2])
      (false, 1) (false, 1)
    exact tree_edge_forward _ _ _

private theorem edge_14 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 14 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 14))
      (routeMark 14) (routeMark (nextState 14 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [1])
      (false, 2) (false, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [1])
      (false, 2) (false, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] false false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [1])
      (false, 2) (false, 2)
    exact tree_edge_forward _ _ _

private theorem edge_15 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 15 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 15))
      (routeMark 15) (routeMark (nextState 15 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3])
      (false, 2) (false, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] false false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3])
      (false, 2) (false, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3])
      (false, 2) (false, 3)
    apply edge_from_path (p := [2, 3])
    · exact pair_path 2 3 [true, false] false true false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3])
      (false, 2) (false, 2)
    exact tree_edge_reverse _ _ _

private theorem edge_16 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 16 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 16))
      (routeMark 16) (routeMark (nextState 16 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2, 1])
      (true, 0) (true, 1)
    apply edge_from_path (p := [0, 1])
    · exact pair_path 0 1 [true, false] true true true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2, 1])
      (true, 0) (true, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2, 1])
      (true, 0) (true, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [3, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2, 1])
      (true, 0) (true, 0)
    exact tree_edge_forward _ _ _

private theorem edge_17 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 17 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 17))
      (routeMark 17) (routeMark (nextState 17 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 2])
      (true, 1) (true, 0)
    apply edge_from_path (p := [1, 0])
    · exact pair_path 0 1 [false, true] true false true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 2])
      (true, 1) (true, 1)
    apply edge_from_path (p := [2, 1, 2])
    · exact pair_path 1 2 [false, true, false] true true true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 2])
      (true, 1) (true, 1)
    apply edge_from_path (p := [3])
    · exact pair_path 1 3 [false] true true true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 2])
      (true, 1) (true, 1)
    exact tree_edge_reverse _ _ _

private theorem edge_18 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 18 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 18))
      (routeMark 18) (routeMark (nextState 18 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [0, 1])
      (true, 2) (true, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] true false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] true false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [0, 1])
      (true, 2) (true, 2)
    exact tree_edge_forward _ _ _

private theorem edge_19 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 19 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 19))
      (routeMark 19) (routeMark (nextState 19 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [3])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [2, 3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 1])
      (true, 2) (true, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 1])
      (true, 2) (true, 2)
    exact tree_edge_reverse _ _ _

private theorem edge_20 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 20 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 20))
      (routeMark 20) (routeMark (nextState 20 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2, 1])
      (false, 0) (false, 1)
    apply edge_from_path (p := [0, 1])
    · exact pair_path 0 1 [true, false] false true false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2, 1])
      (false, 0) (false, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2, 1])
      (false, 0) (false, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [3, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2, 1])
      (false, 0) (false, 0)
    exact tree_edge_forward _ _ _

private theorem edge_21 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 21 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 21))
      (routeMark 21) (routeMark (nextState 21 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 2])
      (false, 1) (false, 0)
    apply edge_from_path (p := [1, 0])
    · exact pair_path 0 1 [false, true] false false false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 2])
      (false, 1) (false, 1)
    apply edge_from_path (p := [2, 1, 2])
    · exact pair_path 1 2 [false, true, false] false true false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 2])
      (false, 1) (false, 1)
    apply edge_from_path (p := [3])
    · exact pair_path 1 3 [false] false true false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 2])
      (false, 1) (false, 1)
    exact tree_edge_reverse _ _ _

private theorem edge_22 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 22 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 22))
      (routeMark 22) (routeMark (nextState 22 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [0, 1])
      (false, 2) (false, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] false false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] false false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [0, 1])
      (false, 2) (false, 2)
    exact tree_edge_forward _ _ _

private theorem edge_23 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 23 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 23))
      (routeMark 23) (routeMark (nextState 23 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [3])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [2, 3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 1])
      (false, 2) (false, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 1])
      (false, 2) (false, 2)
    exact tree_edge_reverse _ _ _

private theorem edge_24 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 24 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 24))
      (routeMark 24) (routeMark (nextState 24 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [1, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [1, 0, 2, 1, 2, 0, 1])
    · exact path_append _ _ (path_append _ _ (pair_path 0 1 [true, false] true true true false (by decide)) (pair_path 1 2 [false, true, false] true true true true (by decide))) (pair_path 0 1 [false, true] true false true true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [1, 2, 1])
      (true, 0) (true, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [1, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] true true true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [1, 2, 1])
      (true, 0) (true, 0)
    exact tree_edge_forward _ _ _

private theorem edge_25 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 25 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 25))
      (routeMark 25) (routeMark (nextState 25 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 2, 1])
      (true, 0) (true, 1)
    apply edge_from_path (p := [0, 1])
    · exact pair_path 0 1 [true, false] true true true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [3, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] true true true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 2, 1])
      (true, 0) (true, 0)
    exact tree_edge_reverse _ _ _

private theorem edge_26 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 26 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 26))
      (routeMark 26) (routeMark (nextState 26 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] true false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 0, 1])
      (true, 2) (true, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 0, 1])
      (true, 2) (true, 2)
    exact tree_edge_reverse _ _ _

private theorem edge_27 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 27 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 27))
      (routeMark 27) (routeMark (nextState 27 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2, 3, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [2, 3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2, 3, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [3, 2, 1, 2, 3])
    · exact path_append _ _ (path_append _ _ (pair_path 2 3 [true, false] true true true false (by decide)) (pair_path 1 3 [true] true false true false (by decide))) (pair_path 2 3 [false, true] true false true true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2, 3, 1])
      (true, 2) (true, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [2, 3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2, 3, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] true false true false (by decide)
    · decide

private theorem edge_28 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 28 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 28))
      (routeMark 28) (routeMark (nextState 28 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [1, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [1, 0, 2, 1, 2, 0, 1])
    · exact path_append _ _ (path_append _ _ (pair_path 0 1 [true, false] false true false false (by decide)) (pair_path 1 2 [false, true, false] false true false true (by decide))) (pair_path 0 1 [false, true] false false false true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [1, 2, 1])
      (false, 0) (false, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [1, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] false true false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [1, 2, 1])
      (false, 0) (false, 0)
    exact tree_edge_forward _ _ _

private theorem edge_29 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 29 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 29))
      (routeMark 29) (routeMark (nextState 29 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 2])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 2, 1])
      (false, 0) (false, 1)
    apply edge_from_path (p := [0, 1])
    · exact pair_path 0 1 [true, false] false true false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [3, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] false true false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 2, 1])
      (false, 0) (false, 0)
    exact tree_edge_reverse _ _ _

private theorem edge_30 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 30 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 30))
      (routeMark 30) (routeMark (nextState 30 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] false false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 0, 1])
      (false, 2) (false, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 0, 1])
      (false, 2) (false, 2)
    exact tree_edge_reverse _ _ _

private theorem edge_31 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 31 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 31))
      (routeMark 31) (routeMark (nextState 31 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2, 3, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [2, 3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2, 3, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [3, 2, 1, 2, 3])
    · exact path_append _ _ (path_append _ _ (pair_path 2 3 [true, false] false true false false (by decide)) (pair_path 1 3 [true] false false false false (by decide))) (pair_path 2 3 [false, true] false false false true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2, 3, 1])
      (false, 2) (false, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [2, 3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2, 3, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] false false false false (by decide)
    · decide

private theorem edge_32 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 32 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 32))
      (routeMark 32) (routeMark (nextState 32 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 1, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [1, 0, 2, 1, 2, 0, 1])
    · exact path_append _ _ (path_append _ _ (pair_path 0 1 [true, false] true true true false (by decide)) (pair_path 1 2 [false, true, false] true true true true (by decide))) (pair_path 0 1 [false, true] true false true true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [3, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 1, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 1, 2, 1])
      (true, 0) (true, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 1, 2, 1])
      (true, 0) (true, 0)
    exact tree_edge_reverse _ _ _

private theorem edge_33 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 33 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 33))
      (routeMark 33) (routeMark (nextState 33 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2, 3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2, 3, 0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2, 3, 0, 1])
      (true, 2) (true, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2, 3, 0, 1])
      (true, 2) (true, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2, 3, 0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] true false true false (by decide)
    · decide

private theorem edge_34 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 34 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 34))
      (routeMark 34) (routeMark (nextState 34 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 1, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [1, 0, 2, 1, 2, 0, 1])
    · exact path_append _ _ (path_append _ _ (pair_path 0 1 [true, false] false true false false (by decide)) (pair_path 1 2 [false, true, false] false true false true (by decide))) (pair_path 0 1 [false, true] false false false true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [3, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 1, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 1, 2, 1])
      (false, 0) (false, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 1, 2, 1])
      (false, 0) (false, 0)
    exact tree_edge_reverse _ _ _

private theorem edge_35 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 35 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 35))
      (routeMark 35) (routeMark (nextState 35 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2, 3, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2, 3, 0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [])
    · exact WeylPairPath.refl _
    · decide
  · change WeylPairPath ((numberedProd [1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2, 3, 0, 1])
      (false, 2) (false, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2, 3, 0, 1])
      (false, 2) (false, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2, 3, 0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] false false false false (by decide)
    · decide

private theorem edge_36 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 36 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 36))
      (routeMark 36) (routeMark (nextState 36 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [1, 0, 2, 1, 2, 0, 1])
    · exact path_append _ _ (path_append _ _ (pair_path 0 1 [true, false] true true true false (by decide)) (pair_path 1 2 [false, true, false] true true true true (by decide))) (pair_path 0 1 [false, true] true false true true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] true true true true (by decide)
    · decide

private theorem edge_37 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 37 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 37))
      (routeMark 37) (routeMark (nextState 37 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [3, 2, 1, 2, 3])
    · exact path_append _ _ (path_append _ _ (pair_path 2 3 [true, false] true true true false (by decide)) (pair_path 1 3 [true] true false true false (by decide))) (pair_path 2 3 [false, true] true false true true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] true false true false (by decide)
    · decide

private theorem edge_38 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 38 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 38))
      (routeMark 38) (routeMark (nextState 38 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [1, 0, 2, 1, 2, 0, 1])
    · exact path_append _ _ (path_append _ _ (pair_path 0 1 [true, false] false true false false (by decide)) (pair_path 1 2 [false, true, false] false true false true (by decide))) (pair_path 0 1 [false, true] false false false true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] false true false true (by decide)
    · decide

private theorem edge_39 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 39 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 39))
      (routeMark 39) (routeMark (nextState 39 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [3, 2, 1, 2, 3])
    · exact path_append _ _ (path_append _ _ (pair_path 2 3 [true, false] false true false false (by decide)) (pair_path 1 3 [true] false false false false (by decide))) (pair_path 2 3 [false, true] false false false true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] false false false false (by decide)
    · decide

private theorem edge_40 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 40 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 40))
      (routeMark 40) (routeMark (nextState 40 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [0, 1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [1, 2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [1, 2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [1, 2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] true true true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [1, 2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] true true true true (by decide)
    · decide

private theorem edge_41 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 41 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 41))
      (routeMark 41) (routeMark (nextState 41 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2, 1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [3, 2, 1, 2, 3])
    · exact path_append _ _ (path_append _ _ (pair_path 2 3 [true, false] true true true false (by decide)) (pair_path 1 3 [true] true false true false (by decide))) (pair_path 2 3 [false, true] true false true true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2, 1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] true false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2, 1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [3, 2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2, 1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    exact tree_edge_forward _ _ _

private theorem edge_42 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 42 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 42))
      (routeMark 42) (routeMark (nextState 42 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [0, 1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [1, 2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    exact tree_edge_forward _ _ _
  · change WeylPairPath ((numberedProd [2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [1, 2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [1, 2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] false true false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [1, 2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] false true false true (by decide)
    · decide

private theorem edge_43 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 43 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 43))
      (routeMark 43) (routeMark (nextState 43 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [2, 1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [3, 2, 1, 2, 3])
    · exact path_append _ _ (path_append _ _ (pair_path 2 3 [true, false] false true false false (by decide)) (pair_path 1 3 [true] false false false false (by decide))) (pair_path 2 3 [false, true] false false false true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [2, 1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] false false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [2, 1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [3, 2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [2, 1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    exact tree_edge_forward _ _ _

private theorem edge_44 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 44 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 44))
      (routeMark 44) (routeMark (nextState 44 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [0, 1, 2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [0, 1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [0, 1, 2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [1, 0, 2, 1, 2, 0, 1])
    · exact path_append _ _ (path_append _ _ (pair_path 0 1 [true, false] true true true false (by decide)) (pair_path 1 2 [false, true, false] true true true true (by decide))) (pair_path 0 1 [false, true] true false true true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [0, 1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [0, 1, 2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] true true true true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [0, 1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [0, 1, 2, 3, 1, 2, 1])
      (true, 0) (true, 0)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] true true true true (by decide)
    · decide

private theorem edge_45 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 45 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 45))
      (routeMark 45) (routeMark (nextState 45 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 2, 1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [3, 2, 1, 2, 3])
    · exact path_append _ _ (path_append _ _ (pair_path 2 3 [true, false] true true true false (by decide)) (pair_path 1 3 [true] true false true false (by decide))) (pair_path 2 3 [false, true] true false true true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [3, 2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 2, 1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] true false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 2, 1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] true false true false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 2, 1, 2, 3, 0, 1])
      (true, 2) (true, 2)
    exact tree_edge_reverse _ _ _

private theorem edge_46 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 46 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 46))
      (routeMark 46) (routeMark (nextState 46 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [0, 1, 2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    exact tree_edge_reverse _ _ _
  · change WeylPairPath ((numberedProd [0, 1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [0, 1, 2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [1, 0, 2, 1, 2, 0, 1])
    · exact path_append _ _ (path_append _ _ (pair_path 0 1 [true, false] false true false false (by decide)) (pair_path 1 2 [false, true, false] false true false true (by decide))) (pair_path 0 1 [false, true] false false false true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [0, 1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [0, 1, 2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [3])
    · exact pair_path 0 3 [false] false true false true (by decide)
    · decide
  · change WeylPairPath ((numberedProd [0, 1, 2, 3, 1, 2, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [0, 1, 2, 3, 1, 2, 1])
      (false, 0) (false, 0)
    apply edge_from_path (p := [2])
    · exact pair_path 0 2 [false] false true false true (by decide)
    · decide

private theorem edge_47 (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState 47 i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord 47))
      (routeMark 47) (routeMark (nextState 47 i)) := by
  fin_cases i
  · change WeylPairPath ((numberedProd [3, 2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 0) * numberedProd [3, 2, 1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [3, 2, 1, 2, 3])
    · exact path_append _ _ (path_append _ _ (pair_path 2 3 [true, false] false true false false (by decide)) (pair_path 1 3 [true] false false false false (by decide))) (pair_path 2 3 [false, true] false false false true (by decide))
    · decide
  · change WeylPairPath ((numberedProd [3, 2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 1) * numberedProd [3, 2, 1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [0])
    · exact pair_path 0 2 [true] false false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [3, 2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 2) * numberedProd [3, 2, 1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    apply edge_from_path (p := [1, 2, 1])
    · exact pair_path 1 2 [true, false, true] false false false false (by decide)
    · decide
  · change WeylPairPath ((numberedProd [2, 1, 2, 3, 0, 1])⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex 3) * numberedProd [3, 2, 1, 2, 3, 0, 1])
      (false, 2) (false, 2)
    exact tree_edge_reverse _ _ _
-- END GENERATED EDGE CERTIFICATES

/-- Every simple-reflection edge has its complete Schreier correction as a
path through signed simple roots in standard two-node subsystems. -/
theorem edge (r : Fin 48) (i : Fin 4) :
    WeylPairPath ((numberedProd (routeWord (nextState r i)))⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd (routeWord r))
      (routeMark r) (routeMark (nextState r i)) := by
  fin_cases r
  · exact edge_0 i
  · exact edge_1 i
  · exact edge_2 i
  · exact edge_3 i
  · exact edge_4 i
  · exact edge_5 i
  · exact edge_6 i
  · exact edge_7 i
  · exact edge_8 i
  · exact edge_9 i
  · exact edge_10 i
  · exact edge_11 i
  · exact edge_12 i
  · exact edge_13 i
  · exact edge_14 i
  · exact edge_15 i
  · exact edge_16 i
  · exact edge_17 i
  · exact edge_18 i
  · exact edge_19 i
  · exact edge_20 i
  · exact edge_21 i
  · exact edge_22 i
  · exact edge_23 i
  · exact edge_24 i
  · exact edge_25 i
  · exact edge_26 i
  · exact edge_27 i
  · exact edge_28 i
  · exact edge_29 i
  · exact edge_30 i
  · exact edge_31 i
  · exact edge_32 i
  · exact edge_33 i
  · exact edge_34 i
  · exact edge_35 i
  · exact edge_36 i
  · exact edge_37 i
  · exact edge_38 i
  · exact edge_39 i
  · exact edge_40 i
  · exact edge_41 i
  · exact edge_42 i
  · exact edge_43 i
  · exact edge_44 i
  · exact edge_45 i
  · exact edge_46 i
  · exact edge_47 i

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths.WeylGeometry
