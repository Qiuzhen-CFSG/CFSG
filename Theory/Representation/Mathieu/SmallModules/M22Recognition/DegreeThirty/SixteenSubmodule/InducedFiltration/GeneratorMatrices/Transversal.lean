module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.CosetModel
public import Mathlib.Data.Fin.VecNotation

/-!
# Explicit right-coset representatives for the native M22 point stabilizer

A table of 22 words of length at most eight gives representatives `t i` with
`t i • i = 0`. Right multiplication by `g` changes the source point to `g⁻¹ • i`
and contributes `t i * g * (t (g⁻¹ • i))⁻¹` in the zero stabilizer. Both the
representative permutations and the 44 generator corrections are executable.
The table identity is checked by the kernel, and the subgroup membership and
multiplication formulas are proved structurally.

This supplies the finite indexing for the induction calculation behind
Guralnick--Malle I, Proposition 5.1, pp.15--16; see also Aschbacher--Smith,
Chapter K, printed pp.451--452 and 457. It asserts no composition-factor result.
-/

@[expose] public section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.GeneratorMatrices

/-- The two executable native generator permutations, in ATLAS order. -/
def generatorPerm : Fin 2 → Equiv.Perm (Fin 22) :=
  ![m22GeneratorA, m22GeneratorB]

/-- The same two generators as elements of the certified native M22 group. -/
noncomputable def generator : Fin 2 → M22 :=
  ![m22GeneratorAInM22, m22GeneratorBInM22]

theorem generator_val (k : Fin 2) : (generator k).val = generatorPerm k := by
  fin_cases k <;> rfl

/-- Evaluate words as permutations; the rightmost letter acts first. -/
def wordPerm : List (Fin 2) → Equiv.Perm (Fin 22)
  | [] => 1
  | k :: w => generatorPerm k * wordPerm w

/-- Evaluate the same word inside the native group. -/
noncomputable def wordElement : List (Fin 2) → M22
  | [] => 1
  | k :: w => generator k * wordElement w

theorem wordElement_val (w : List (Fin 2)) : (wordElement w).val = wordPerm w := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change (generator k).val * (wordElement w).val = _
    rw [generator_val, ih]
    rfl

/-- Short words sending each indexed point to zero. -/
def transversalWord : Fin 22 → List (Fin 2) :=
  ![[],
    [1],
    [1, 0, 1, 1, 1],
    [1, 1, 1],
    [1, 0, 1],
    [1, 0, 1, 0, 1],
    [0],
    [0, 1, 1],
    [0, 1, 1, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 1, 0, 1, 1],
    [0, 1, 1, 1],
    [1, 0, 1, 0],
    [1, 0],
    [0, 1, 1, 1, 0],
    [0, 1],
    [1, 1, 1, 0],
    [0, 1, 1, 0],
    [1, 0, 1, 1],
    [0, 1, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 1, 1],
    [1, 1]]

/-- An executable permutation representative of each right coset. -/
def transversalPerm (i : Fin 22) : Equiv.Perm (Fin 22) := wordPerm (transversalWord i)

theorem transversalPerm_self (i : Fin 22) : transversalPerm i i = 0 := by
  revert i
  decide +kernel

/-- The certified representative, as a native group element. -/
noncomputable def transversal (i : Fin 22) : M22 := wordElement (transversalWord i)

theorem transversal_val (i : Fin 22) : (transversal i).val = transversalPerm i :=
  wordElement_val _

theorem transversal_smul_self (i : Fin 22) : transversal i • i = 0 := by
  change (transversal i).val i = 0
  rw [transversal_val, transversalPerm_self]

theorem transversal_inv_zero (i : Fin 22) : (transversal i)⁻¹ • (0 : Fin 22) = i := by
  rw [← transversal_smul_self i, inv_smul_smul]

/-- The exact stabilizer correction for right multiplication of representatives. -/
noncomputable def correction (g : M22) (i : Fin 22) :
    MulAction.stabilizer M22 (0 : Fin 22) :=
  ⟨transversal i * g * (transversal (g⁻¹ • i))⁻¹, by
    change (transversal i * g * (transversal (g⁻¹ • i))⁻¹) • (0 : Fin 22) = 0
    rw [mul_smul, transversal_inv_zero, mul_smul, smul_inv_smul, transversal_smul_self]⟩

theorem correction_mul_transversal (g : M22) (i : Fin 22) :
    (correction g i).val * transversal (g⁻¹ • i) = transversal i * g := by
  simp [correction, mul_assoc]

/-- The source block of output block `i`; this is the inverse generator action. -/
def generatorPoint (k : Fin 2) (i : Fin 22) : Fin 22 := (generatorPerm k)⁻¹ i

theorem generatorPoint_eq (k : Fin 2) (i : Fin 22) :
    generatorPoint k i = (generator k)⁻¹ • i := by
  change _ = ((generator k).val)⁻¹ i
  rw [generator_val]
  rfl

/-- The 44 native stabilizer elements whose binary adjoint matrices are required. -/
noncomputable def generatorCorrection (k : Fin 2) (i : Fin 22) :
    MulAction.stabilizer M22 (0 : Fin 22) := correction (generator k) i


/-- Executable permutations underlying the 44 stabilizer corrections. -/
def generatorCorrectionPerm (k : Fin 2) (i : Fin 22) : Equiv.Perm (Fin 22) :=
  transversalPerm i * generatorPerm k * (transversalPerm (generatorPoint k i))⁻¹

/-- The executable permutation is the literal native stabilizer element. -/
theorem generatorCorrection_val (k : Fin 2) (i : Fin 22) :
    (generatorCorrection k i).val.val = generatorCorrectionPerm k i := by
  change (transversal i).val * (generator k).val *
    ((transversal ((generator k)⁻¹ • i)).val)⁻¹ = _
  rw [transversal_val, generator_val, transversal_val, ← generatorPoint_eq]
  rfl

@[simp] theorem generator_zero : generator 0 = m22GeneratorAInM22 := rfl
@[simp] theorem generator_one : generator 1 = m22GeneratorBInM22 := rfl

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.GeneratorMatrices
