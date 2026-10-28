module

public import Theory.Mathieu.M24.LocalGeometry.Defs

/-!
# An explicit incident octad and sextet in W24

Starting with the tetrad {0,1,2,3}, the five octads containing it determine
the other five tetrads. Each pair union below is checked against an explicit
word of the certified Golay code and hence is an octad of the fixed design.
The verification uses the Lean kernel, not an external group identification.

This supplies concrete vertices for the local geometry of GLS, volume 3,
Table 5.3e. It does not yet determine their stabilizers or a Sylow subgroup.
-/

@[expose] public section

namespace Sporadic.Mathieu.M24LocalGeometry

/-- A labelled sextet in the coordinates of the fixed W24 design. -/
def standardTetrad : Fin 6 → Finset (Fin 24)
  | 0 => {0, 1, 2, 3}
  | 1 => {10, 16, 22, 23}
  | 2 => {7, 12, 15, 20}
  | 3 => {6, 9, 14, 19}
  | 4 => {4, 5, 11, 17}
  | 5 => {8, 13, 18, 21}

private def baseMessage : Fin 6 → Fin 4096
  | 0 => 0
  | 1 => 15
  | 2 => 143
  | 3 => 591
  | 4 => 1087
  | 5 => 2319

private theorem standardTetrad_union_word (i j : Fin 6) (hij : i ≠ j) :
    standardTetrad i ∪ standardTetrad j =
      m24GolayWord (m24GolayMessageXor (baseMessage i) (baseMessage j)) := by
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | decide +kernel

theorem standardTetrad_card (i : Fin 6) : (standardTetrad i).card = 4 := by
  fin_cases i <;> decide +kernel

theorem standardTetrad_disjoint (i j : Fin 6) (hij : i ≠ j) :
    Disjoint (standardTetrad i) (standardTetrad j) := by
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | decide +kernel

/-- Every two distinct tetrads have an octad as their union. -/
theorem standardTetrad_union_mem (i j : Fin 6) (hij : i ≠ j) :
    standardTetrad i ∪ standardTetrad j ∈ m24Blocks := by
  have hc : (standardTetrad i ∪ standardTetrad j).card = 8 := by
    rw [Finset.card_union_of_disjoint (standardTetrad_disjoint i j hij),
      standardTetrad_card, standardTetrad_card]
  rw [standardTetrad_union_word i j hij] at hc ⊢
  exact m24GolayWord_mem_blocks_of_card_eq_eight _ hc

/-- The concrete sextet, with all partition and octad conditions checked. -/
def standardSextet : Sextet where
  parts := Finset.univ.image standardTetrad
  card := by decide +kernel
  tetrad A hA := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    exact standardTetrad_card i
  disjoint A hA B hB hne := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    exact standardTetrad_disjoint i j (fun he => hne (congrArg standardTetrad he))
  cover := by decide +kernel
  octad A hA B hB hne := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    exact standardTetrad_union_mem i j (fun he => hne (congrArg standardTetrad he))

/-- An octad incident with the standard sextet. -/
def standardOctad : Octad :=
  ⟨standardTetrad 0 ∪ standardTetrad 1, standardTetrad_union_mem 0 1 (by decide)⟩

end Sporadic.Mathieu.M24LocalGeometry

end
