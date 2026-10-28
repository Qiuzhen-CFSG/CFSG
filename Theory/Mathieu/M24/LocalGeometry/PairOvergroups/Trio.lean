module

public import Theory.Mathieu.M24.LocalGeometry.Seed
public import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# A concrete octad trio and its stabilizers in M₂₄

A trio is a partition of the 24 points into three octads of the fixed Witt
design. Pairing consecutive tetrads of the checked standard sextet gives an
explicit trio. Its stabilizer, and every conjugate used below, are actual
subgroups of `Sporadic.Mathieu.M24`.

The stabilizers of translated partitions are conjugate by the same model
element. This gives the multiplicative equivalence needed to transport a
quotient calculation from the standard trio to a pair's eventual overgroup.
Neither the structure of that quotient nor placement of arbitrary Sylow pairs
is assumed or proved in this module.

Source: Aschbacher, *Sporadic Groups*, Chapter 7, §20, definition of a trio
and Lemma 20.2 (printed p.97); GLS3, Table 5.3e, E₆₄.N(3B).
-/

@[expose] public section

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups

open scoped Pointwise

/-- An unordered partition into three actual octads of W24. -/
structure Trio where
  parts : Finset (Finset (Fin 24))
  card : parts.card = 3
  octad : ∀ A ∈ parts, A ∈ m24Blocks
  disjoint : ∀ A ∈ parts, ∀ B ∈ parts, A ≠ B → Disjoint A B
  cover : parts.biUnion id = Finset.univ

/-- Every part of a trio has eight points, by the fixed design's block axiom. -/
theorem Trio.part_card (T : Trio) {A : Finset (Fin 24)} (hA : A ∈ T.parts) :
    A.card = 8 :=
  m24Blocks_card A (T.octad A hA)

/-- Setwise stabilization permits permutation of the three octads. -/
noncomputable def trioStabilizer (T : Trio) : Subgroup M24 :=
  MulAction.stabilizer M24 T.parts

theorem mem_trioStabilizer_iff (T : Trio) (g : M24) :
    g ∈ trioStabilizer T ↔ ∀ A ∈ T.parts, g • A ∈ T.parts :=
  MulAction.mem_stabilizer_finset'

/-- Pairing the six standard tetrads gives three labelled octads. -/
def standardTrioOctad : Fin 3 → Finset (Fin 24)
  | 0 => standardTetrad 0 ∪ standardTetrad 1
  | 1 => standardTetrad 2 ∪ standardTetrad 3
  | 2 => standardTetrad 4 ∪ standardTetrad 5

theorem standardTrioOctad_mem (i : Fin 3) : standardTrioOctad i ∈ m24Blocks := by
  fin_cases i <;> exact standardTetrad_union_mem _ _ (by decide)

theorem standardTrioOctad_disjoint (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (standardTrioOctad i) (standardTrioOctad j) := by
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | decide +kernel

/-- The standard trio has all partition and octad conditions checked. -/
def standardTrio : Trio where
  parts := Finset.univ.image standardTrioOctad
  card := by decide +kernel
  octad A hA := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    exact standardTrioOctad_mem i
  disjoint A hA B hB hne := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
    exact standardTrioOctad_disjoint i j (fun he => hne (congrArg standardTrioOctad he))
  cover := by decide +kernel

/-- The actual stabilizer of a translate of the standard octad partition. -/
noncomputable def conjugateTrioStabilizer (g : M24) : Subgroup M24 :=
  MulAction.stabilizer M24 (g • standardTrio.parts)

/-- Conjugation by the translating model element identifies the stabilizers. -/
noncomputable def conjugateTrioStabilizerEquiv (g : M24) :
    trioStabilizer standardTrio ≃* conjugateTrioStabilizer g :=
  MulAction.stabilizerEquivStabilizer rfl

theorem conjugateTrioStabilizer_eq_map (g : M24) :
    conjugateTrioStabilizer g =
      (trioStabilizer standardTrio).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g standardTrio.parts

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups

end
