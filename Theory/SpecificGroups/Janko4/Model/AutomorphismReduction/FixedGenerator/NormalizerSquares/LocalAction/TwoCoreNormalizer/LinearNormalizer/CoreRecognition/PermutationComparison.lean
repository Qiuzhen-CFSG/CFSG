module
public import Theory.Mathieu.M22.Properties.Order
public import Mathlib.Tactic.FinCases

/-!
# A checked permutation target for the binary core

The displayed degree-22 permutations generate the existing even automorphism
group of the hexad design. We prove this by explicit words in both directions
between this pair and the standard generators. Every permutation identity is
checked by the Lean kernel. This does not yet construct an action of the
binary matrix group on these 22 points.

The candidate pair comes from the scalar-line configuration recorded in
`source/projective-certificate.json`; the matrix source attribution is retained
in `../../LinearModel/source/`. GAP word lists use right actions, so their order
is reversed when evaluated as Lean permutation products.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Sporadic.Mathieu

/-- A concrete degree-22 permutation for comparison with the core action. -/
def corePermA : Equiv.Perm (Fin 22) where
  toFun := ![20, 0, 9, 12, 14, 17, 1, 3, 6, 5, 7, 15, 11, 16, 8, 19, 21, 10, 4, 2, 13, 18]
  invFun := ![1, 6, 19, 7, 18, 9, 8, 10, 14, 2, 17, 12, 3, 20, 4, 11, 13, 5, 21, 15, 0, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A concrete degree-22 permutation for comparison with the core action. -/
def corePermB : Equiv.Perm (Fin 22) where
  toFun := ![10, 17, 12, 11, 8, 5, 9, 13, 4, 6, 0, 3, 2, 7, 16, 15, 14, 1, 18, 19, 20, 21]
  invFun := ![10, 17, 12, 11, 8, 5, 9, 13, 4, 6, 0, 3, 2, 7, 16, 15, 14, 1, 18, 19, 20, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def evalWord {G : Type*} [Group G] (u v : G) (w : List (Fin 4)) : G :=
  (w.map ![u, v, u⁻¹, v⁻¹]).prod

private theorem evalWord_mem {G : Type*} [Group G] (H : Subgroup G)
    {u v : G} (hu : u ∈ H) (hv : v ∈ H) (w : List (Fin 4)) : evalWord u v w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih =>
    apply H.mul_mem _ ih
    fin_cases i
    · exact hu
    · exact hv
    · exact H.inv_mem hu
    · exact H.inv_mem hv

private def toA : List (Fin 4) := [2, 1, 2, 1, 2, 3, 2, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 3, 3, 2, 3, 3, 2, 1, 2, 1, 1, 0]

private def toB : List (Fin 4) := [1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0]

private def fromA : List (Fin 4) := [2, 3, 0, 1, 2, 2, 3, 0, 3, 2, 3]

private def fromB : List (Fin 4) := [2, 3, 2, 3, 2, 3, 2, 3, 0, 3, 0, 0, 3, 0, 3, 0, 3, 2, 2, 2, 2, 1, 2, 1, 2, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 3, 2]

private theorem toA_spec : evalWord m22GeneratorA m22GeneratorB toA = corePermA := by decide +kernel
private theorem toB_spec : evalWord m22GeneratorA m22GeneratorB toB = corePermB := by decide +kernel
private theorem fromA_spec : evalWord corePermA corePermB fromA = m22GeneratorA := by decide +kernel
private theorem fromB_spec : evalWord corePermA corePermB fromB = m22GeneratorB := by decide +kernel

/-- Both comparison permutations preserve the existing even hexad design. -/
theorem corePermA_mem_M22 : corePermA ∈ M22 := by
  rw [← toA_spec]
  exact evalWord_mem M22 m22GeneratorA_mem_M22 m22GeneratorB_mem_M22 toA

theorem corePermB_mem_M22 : corePermB ∈ M22 := by
  rw [← toB_spec]
  exact evalWord_mem M22 m22GeneratorA_mem_M22 m22GeneratorB_mem_M22 toB

/-- The comparison permutations generate the existing concrete Mathieu carrier. -/
theorem corePerm_closure_eq_M22 : Subgroup.closure {corePermA, corePermB} = M22 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact corePermA_mem_M22
    · exact corePermB_mem_M22
  · rw [← m22Atlas_eq_M22, m22Atlas, Subgroup.closure_le]
    have ha : corePermA ∈ Subgroup.closure {corePermA, corePermB} :=
      Subgroup.subset_closure (Or.inl rfl)
    have hb : corePermB ∈ Subgroup.closure {corePermA, corePermB} :=
      Subgroup.subset_closure (Or.inr rfl)
    rintro x (rfl | rfl)
    · rw [← fromA_spec]
      exact evalWord_mem _ ha hb fromA
    · rw [← fromB_spec]
      exact evalWord_mem _ ha hb fromB

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
