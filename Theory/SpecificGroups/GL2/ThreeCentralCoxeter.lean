module

public import Theory.SpecificGroups.GL2.ThreeBorelGenerators
public import Theory.Representation.GLTwoBruhat

/-!
# A concrete central A₃ triple in `GL₂(3)`

The three displayed involutions give the rank-three Coxeter relations used by
central lifts of the symmetric-four presentation.  The first and second
adjacent products have cube one, while the end product squares to the scalar
involution `-I`.  Their closure is all of `GL₂(3)`.  The generation proof uses
the already established upper-triangular Borel generators and the elementary
Bruhat decomposition, so no second finite enumeration of the forty-eight
matrices is needed.
-/

open Matrix
open scoped MatrixGroups

namespace Matrix.GeneralLinearGroup


/-- The coordinate-swap involution in the central `A₃` triple. -/
@[expose] public def threeCentralCoxeterA : GL (Fin 2) (ZMod 3) := GLTwo.borelWeyl (ZMod 3)

/-- A second involution in the central `A₃` triple. -/
@[expose] public def threeCentralCoxeterB : GL (Fin 2) (ZMod 3) :=
  mkOfDetNeZero !![(1 : ZMod 3),0;2,2] (by decide)

/-- The diagonal reflection from the standard upper Borel. -/
@[expose] public def threeCentralCoxeterC : GL (Fin 2) (ZMod 3) := threeReflection

private theorem coxeter_matrix_relations :
    threeCentralCoxeterA ^ 2 = 1 ∧
    threeCentralCoxeterB ^ 2 = 1 ∧
    threeCentralCoxeterC ^ 2 = 1 ∧
    (threeCentralCoxeterA * threeCentralCoxeterB) ^ 3 = 1 ∧
    (threeCentralCoxeterB * threeCentralCoxeterC) ^ 3 = 1 ∧
    (threeCentralCoxeterA * threeCentralCoxeterC) ^ 2 = threeCentral := by
  decide +kernel

private theorem coxeter_borel_words :
    (threeCentralCoxeterA * threeCentralCoxeterC) ^ 2 = threeCentral ∧
    threeCentralCoxeterA * threeCentralCoxeterC * threeCentralCoxeterB *
        threeCentralCoxeterA = threeUnipotent := by
  decide +kernel

/-- The three concrete involutions satisfy the central `A₃` relations. -/
public theorem threeCentralCoxeter_relations :
    threeCentralCoxeterA ^ 2 = 1 ∧
    threeCentralCoxeterB ^ 2 = 1 ∧
    threeCentralCoxeterC ^ 2 = 1 ∧
    (threeCentralCoxeterA * threeCentralCoxeterB) ^ 3 = 1 ∧
    (threeCentralCoxeterB * threeCentralCoxeterC) ^ 3 = 1 ∧
    (threeCentralCoxeterA * threeCentralCoxeterC) ^ 2 = threeCentral :=
  coxeter_matrix_relations

/-- The displayed triple generates the full actual matrix group. -/
public theorem threeCentralCoxeter_closure_eq_top :
    Subgroup.closure ({threeCentralCoxeterA, threeCentralCoxeterB,
      threeCentralCoxeterC} : Set (GL (Fin 2) (ZMod 3))) = ⊤ := by
  let H : Subgroup (GL (Fin 2) (ZMod 3)) := Subgroup.closure
    ({threeCentralCoxeterA, threeCentralCoxeterB, threeCentralCoxeterC} : Set (GL (Fin 2) (ZMod 3)))
  change H = ⊤
  have hA : threeCentralCoxeterA ∈ H := by
    exact Subgroup.subset_closure (show threeCentralCoxeterA ∈
      ({threeCentralCoxeterA, threeCentralCoxeterB, threeCentralCoxeterC} :
        Set (GL (Fin 2) (ZMod 3))) by simp)
  have hB : threeCentralCoxeterB ∈ H := by
    exact Subgroup.subset_closure (show threeCentralCoxeterB ∈
      ({threeCentralCoxeterA, threeCentralCoxeterB, threeCentralCoxeterC} :
        Set (GL (Fin 2) (ZMod 3))) by simp)
  have hC : threeCentralCoxeterC ∈ H := by
    exact Subgroup.subset_closure (show threeCentralCoxeterC ∈
      ({threeCentralCoxeterA, threeCentralCoxeterB, threeCentralCoxeterC} :
        Set (GL (Fin 2) (ZMod 3))) by simp)
  have hz : threeCentral ∈ H := by
    rw [← coxeter_borel_words.1]
    exact Subgroup.pow_mem H (Subgroup.mul_mem H hA hC) 2
  have hu : threeUnipotent ∈ H := by
    rw [← coxeter_borel_words.2]
    exact Subgroup.mul_mem H
      (Subgroup.mul_mem H (Subgroup.mul_mem H hA hC) hB) hA
  have hborel : GLTwo.borelSubgroup (ZMod 3) ≤ H := by
    rw [three_borel_eq_closure]
    exact (Subgroup.closure_le H).mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hz
      · exact hC
      · exact hu)
  apply le_antisymm le_top
  intro x hx
  rcases GLTwo.borel_bruhat x with hxB | ⟨left, right, hfactor⟩
  · exact hborel hxB
  · rw [hfactor]
    exact Subgroup.mul_mem H
      (Subgroup.mul_mem H (hborel left.property) hA) (hborel right.property)

end Matrix.GeneralLinearGroup
