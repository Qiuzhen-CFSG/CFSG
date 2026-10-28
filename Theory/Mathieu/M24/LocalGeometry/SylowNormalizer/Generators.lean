module

public import Theory.Mathieu.M24.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Four marked generators for the M₂₄ Sylow calculation

These permutations are elements of the actual Witt-design group: explicit
words in its two certified standard generators prove membership. The subgroup
`candidate` is their generated subgroup, without any order or Sylow assertion
in its definition. Its order and automorphism group are separate computations.

The point tables below only accelerate kernel-checked calculations; their
agreement with the marked permutations is proved pointwise.

Source context: Aschbacher–Smith, printed p.511, and GLS3, Table 5.3e.
The words were found using GAP; GAP output is not used as a proof.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def generatorPerm : Fin 4 → Equiv.Perm (Fin 24)
  | 0 => List.formPerm [1,15,20,6] *
      List.formPerm [2,14,22,23] *
      List.formPerm [3,9,4,11] *
      List.formPerm [5,18] *
      List.formPerm [7,12] *
      List.formPerm [8,21,24,19] *
      List.formPerm [10,13] *
      List.formPerm [16,17]
  | 1 => List.formPerm [3,11] *
      List.formPerm [4,8] *
      List.formPerm [5,15] *
      List.formPerm [6,7] *
      List.formPerm [9,21] *
      List.formPerm [10,14] *
      List.formPerm [17,23] *
      List.formPerm [19,24]
  | 2 => List.formPerm [3,19] *
      List.formPerm [4,21] *
      List.formPerm [6,23] *
      List.formPerm [8,24] *
      List.formPerm [9,11] *
      List.formPerm [12,13] *
      List.formPerm [14,15] *
      List.formPerm [16,18]
  | 3 => List.formPerm [2,22] *
      List.formPerm [4,21] *
      List.formPerm [5,15] *
      List.formPerm [6,7] *
      List.formPerm [8,9] *
      List.formPerm [10,23] *
      List.formPerm [12,18] *
      List.formPerm [14,17]

def standardLetter (i : Fin 2) : Equiv.Perm (Fin 24) :=
  if i = 0 then m24GeneratorA else m24GeneratorB

def standardWord : List (Fin 2) → Equiv.Perm (Fin 24)
  | [] => 1
  | i :: w => standardLetter i * standardWord w

private theorem standardWord_mem (w : List (Fin 2)) : standardWord w ∈ M24 := by
  induction w with
  | nil => exact M24.one_mem
  | cons i w ih =>
    apply M24.mul_mem _ ih
    fin_cases i
    · exact m24GeneratorA_mem
    · exact m24GeneratorB_mem

def generatorWord : Fin 4 → List (Fin 2)
  | 0 => [1,0,1,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,0,1,1]
  | 1 => [1,1,0,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1]
  | 2 => [0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,0,1,1]
  | 3 => [0,1,0,1,0,1,1,0,1,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,1,0,1,0,1,0,1,1,0,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0,1,0,1,0,1,0,1,1]

theorem generatorPerm_eq_word (i : Fin 4) :
    generatorPerm i = standardWord (generatorWord i) := by
  fin_cases i <;> ext x <;> fin_cases x <;> decide +kernel

theorem generatorPerm_mem (i : Fin 4) : generatorPerm i ∈ M24 := by
  rw [generatorPerm_eq_word]
  exact standardWord_mem _

noncomputable def generator (i : Fin 4) : M24 :=
  ⟨generatorPerm i, generatorPerm_mem i⟩

/-- The generated subgroup on the fixed Witt-design carrier. -/
noncomputable def candidate : Subgroup M24 := Subgroup.closure (Set.range generator)

theorem generator_mem (i : Fin 4) : generator i ∈ candidate :=
  Subgroup.subset_closure ⟨i, rfl⟩

noncomputable def markedGenerator (i : Fin 4) : candidate :=
  ⟨generator i, generator_mem i⟩

def generatorPoint : Fin 4 → Fin 24 → Fin 24
  | 0 => ![19,15,14,9,11,18,1,12,21,4,13,3,7,10,22,20,17,16,5,8,6,0,23,2]
  | 1 => ![19,1,2,11,8,15,7,6,4,21,14,3,12,13,10,5,16,23,18,0,20,9,22,17]
  | 2 => ![8,1,2,19,21,5,23,7,0,11,10,9,13,12,15,14,18,17,16,3,20,4,22,6]
  | 3 => ![0,1,22,3,21,15,7,6,9,8,23,11,18,13,17,5,16,14,12,19,20,4,2,10]

theorem generatorPerm_apply : ∀ i x, generatorPerm i x = generatorPoint i x := by
  decide +kernel

def evaluatePoint : List (Fin 4) → Fin 24 → Fin 24
  | [], x => x
  | i :: w, x => generatorPoint i (evaluatePoint w x)

end Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer
