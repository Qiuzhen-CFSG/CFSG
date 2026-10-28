module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Data
/-!
# Explicit linear maps for quartic orbit transports

The columns are the witnesses in `../../source/orbit-witnesses.json`, discovered
by `generate_orbits.py`. Invertibility is proved on the standard basis using
explicit inverse columns. No permutation-group identification is required.
-/

@[expose] public section
namespace BinaryQuarticMathieu.RankRecognition.Orbits

def columnMap (c : Fin 10 → Nat) : U →ₗ[F] U where
  toFun v := ∑ i, v i • vector (c i)
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

theorem columnMap_basis (c : Fin 10 → Nat) (i : Fin 10) :
    columnMap c (basisVector i) = vector (c i) := by
  simp [columnMap, basisVector, Pi.single_apply]

def columnsA : Fin 10 → Nat := ![172,2,67,79,610,294,170,299,327,414]
def columnsB : Fin 10 → Nat := ![394,84,9,94,86,870,282,278,139,663]
def columnsBInv : Fin 10 → Nat := ![28,18,216,24,343,749,397,278,285,663]

theorem columnMap_inverse (c d : Fin 10 → Nat)
    (h : ∀ i, columnMap d (vector (c i)) = basisVector i) :
    (columnMap d).comp (columnMap c) = LinearMap.id := by
  apply (Pi.basisFun F (Fin 10)).ext
  intro i
  simp only [LinearMap.comp_apply, LinearMap.id_apply, Pi.basisFun_apply]
  change columnMap d (columnMap c (basisVector i)) = basisVector i
  rw [columnMap_basis, h]

private theorem inverseA_columns : ∀ i, columnMap columnsA (vector (columnsA i)) = basisVector i := by
  decide +kernel

private theorem inverseB_columns : ∀ i,
    columnMap columnsBInv (vector (columnsB i)) = basisVector i := by
  decide +kernel

private theorem inverseBInv_columns : ∀ i,
    columnMap columnsB (vector (columnsBInv i)) = basisVector i := by
  decide +kernel

/-- The first literal invertible linear map. -/
def generatorA : U ≃ₗ[F] U :=
  LinearEquiv.ofLinearMap (columnMap columnsA) (columnMap columnsA)
    (by exact columnMap_inverse _ _ inverseA_columns) (by exact columnMap_inverse _ _ inverseA_columns)

/-- The second literal invertible linear map. -/
def generatorB : U ≃ₗ[F] U :=
  LinearEquiv.ofLinearMap (columnMap columnsB) (columnMap columnsBInv)
    (by exact columnMap_inverse _ _ inverseBInv_columns) (by exact columnMap_inverse _ _ inverseB_columns)

/-- Specification in the standard coordinate basis, with the requested columns. -/
theorem generatorA_columns (i : Fin 10) :
    generatorA (basisVector i) = vector (![172,2,67,79,610,294,170,299,327,414] i) :=
  columnMap_basis columnsA i

/-- Specification in the standard coordinate basis, with the requested columns. -/
theorem generatorB_columns (i : Fin 10) :
    generatorB (basisVector i) = vector (![394,84,9,94,86,870,282,278,139,663] i) :=
  columnMap_basis columnsB i

theorem vector_xor (a b : Nat) : vector (Nat.xor a b) = vector a + vector b := by
  funext i
  change (if (a ^^^ b).testBit i.val then (1 : F) else 0) =
    (if a.testBit i.val then 1 else 0) + (if b.testBit i.val then 1 else 0)
  rw [Nat.testBit_xor]
  cases a.testBit i.val <;> cases b.testBit i.val <;> decide +kernel

theorem vector_zero : vector 0 = 0 := by decide +kernel

theorem vector_xor_fold (l : List Nat) :
    vector (l.foldr Nat.xor 0) = (l.map vector).sum := by
  induction l with
  | nil =>
    exact vector_zero
  | cons a l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, vector_xor, ih]

def packedAction (c : Fin 10 → Nat) (n : Nat) : Nat :=
  (List.ofFn (fun i : Fin 10 => if n.testBit i.val then c i else 0)).foldr Nat.xor 0

theorem vector_packedAction (c : Fin 10 → Nat) (n : Nat) :
    vector (packedAction c n) = columnMap c (vector n) := by
  rw [packedAction, vector_xor_fold, List.map_ofFn]
  simp only [List.sum_ofFn]
  change (∑ i, vector (if n.testBit i.val then c i else 0)) =
    ∑ i, (if n.testBit i.val then (1 : F) else 0) • vector (c i)
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all only [one_smul, zero_smul, vector_zero]

end BinaryQuarticMathieu.RankRecognition.Orbits
