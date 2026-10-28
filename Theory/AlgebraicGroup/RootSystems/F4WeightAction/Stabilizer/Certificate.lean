module
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Stabilizer.Data

/-! The finite certificate consists solely of explicit integer equations,
word recursions and finite indices. It contains no group classification or
stabilizer assertion. `Checks` supplies every field by kernel verification;
`Comparison` then interprets them in the original real F4 Weyl group. -/
public noncomputable section
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer
structure Certificate : Prop where
  words_zero : Data.words 0 = []
  matrix_zero : Data.matrix 0 = 1
  parent_spec : ∀ k : Fin 1152, k ≠ 0 →
    (Data.parent k).val < k.val ∧
    Data.words k = Data.step k :: Data.words (Data.parent k) ∧
    Data.next (Data.parent k) (Data.step k) = k
  next_columns : ∀ (k : Fin 1152) (i j : Fin 4),
    Data.reflection i (fun a => Data.matrix k a j) =
      fun a => Data.matrix (Data.next k i) a j
  root_coordinates : ∀ r : Fin 24,
    (Data.matrix (Data.rootRoute r)).mulVec (Data.cartan (Data.rootSimple r)) = Data.weights r
  reflection_matrix : ∀ r : Fin 24,
    Data.matrix (Data.refIndex r) * Data.matrix (Data.rootRoute r) =
      Data.matrix (Data.rootRoute r) * Data.matrix (Data.next 0 (Data.rootSimple r))
  ordinary_path : ∀ k, Data.kind k = none → Data.pathValid k (Data.path k)
  ordinary_witness : ∀ k x, x ∈ Data.path k →
    (Data.matrix k).mulVec x.2.2 - x.2.2 = (2:ℤ) • Data.weights x.1
  exception_index : ∀ k j, Data.kind k = some j → Data.exceptionIndex j = k
  exception_conjugate : ∀ j : Fin 16,
    Data.matrix (Data.exceptionIndex j) * Data.matrix (Data.exceptionConj j) =
      Data.matrix (Data.exceptionConj j) * Data.matrix Data.exceptional
  cube : ∀ i : Fin 2,
    (Data.matrix Data.exceptional).mulVec (Data.cubeWitness i) - Data.cubeWitness i =
      (3:ℤ) • (Pi.single (i.castLE (by decide)) 1 : Data.V)
  lines : Data.line = ![(Pi.single 0 1 : Data.V), Pi.single 1 1,
    Pi.single 1 1 - Pi.single 0 1, Pi.single 1 1 - (2:ℤ) • Pi.single 0 1]
  exceptional_path : ∀ i, Data.exceptionPathValid Data.exceptional (Data.exceptionPath i)
  exceptional_witness : ∀ i x, x ∈ Data.exceptionPath i →
    (Data.matrix Data.exceptional).mulVec x.2.2.2 - x.2.2.2 + x.2.2.1 • Data.line i =
      Data.weights x.1

end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer
