module

public import Theory.SpecificGroups.PSL3Three.FiniteModel
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# The literal graph-fixed subgroup of PSL₃(3)

Inverse transpose fixes exactly the determinant-one orthogonal matrices.
Over the three-element field, a vector of norm one is a signed coordinate
vector. The three columns therefore identify this fixed subgroup with the
existing monomial subgroup, through the canonical SL-to-PSL projection.

Only the 216 choices of three signed coordinate columns are used in the
orthogonality certificate; we do not enumerate the full automorphism group.
This comparison supplies the literal fixed group for the centralizer and
normalizer calculations used in the elementary-eight reselection argument.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10.
-/

public section

namespace Matrix.PSL3Three.GraphWitnesses.EightCentralizers
open Matrix.PSL3.OuterSolvable

private def signedVector : Fin 6 → Fin 3 → ZMod 3 :=
  ![![1, 0, 0], ![2, 0, 0], ![0, 1, 0], ![0, 2, 0], ![0, 0, 1], ![0, 0, 2]]

private theorem signedVector_surjective : ∀ v : Fin 3 → ZMod 3,
    v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 → ∃ i, signedVector i = v := by decide

private def signedMatrix (v : Fin 3 → Fin 6) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  fun i j => signedVector (v j) i

private theorem signedMatrix_orthogonal : ∀ v : Fin 3 → Fin 6,
    (signedMatrix v).det = 1 → (signedMatrix v).transpose * signedMatrix v = 1 := by
  decide +kernel

theorem graphSL_fixed_iff_monomial (x : SL) :
    graphSL (ZMod 3) x = x ↔ x ∈ monomialSL := by
  have hfixed : graphSL (ZMod 3) x = x ↔ x.val.transpose * x.val = 1 := by
    constructor
    · intro h
      have ht : SpecialLinearGroup.transpose x * x = 1 := by
        change (SpecialLinearGroup.transpose x)⁻¹ = x at h
        calc
          _ = SpecialLinearGroup.transpose x * (SpecialLinearGroup.transpose x)⁻¹ :=
            congrArg (SpecialLinearGroup.transpose x * ·) h.symm
          _ = 1 := mul_inv_cancel _
      exact congrArg Subtype.val ht
    · intro h
      have ht : SpecialLinearGroup.transpose x * x = 1 := Subtype.ext h
      exact (eq_inv_of_mul_eq_one_right ht).symm
  rw [hfixed, mem_monomialSL_iff_columns]
  constructor
  · intro h j
    have hj := congrArg (fun m : Matrix (Fin 3) (Fin 3) (ZMod 3) => m j j) h
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      Matrix.one_apply_eq, pow_two] using hj
  · intro hc
    have he (j : Fin 3) : ∃ i, signedVector i = fun k => x.val k j :=
      signedVector_surjective _ (hc j)
    choose v hv using he
    have hm : signedMatrix v = x.val := by
      ext i j
      exact congrFun (hv j) i
    simpa only [hm] using signedMatrix_orthogonal v (hm ▸ x.property)

theorem graph_fixed_eq_monomial : (graph (ZMod 3)).fixedSubgroup = monomial := by
  ext x
  obtain ⟨s, rfl⟩ := project_surjective x
  rw [MulAut.mem_fixedSubgroup]
  have h : graph (ZMod 3) (project s) = project (graphSL (ZMod 3) s) := rfl
  rw [h, project_injective.eq_iff, graphSL_fixed_iff_monomial]
  constructor
  · intro hs
    exact ⟨s, hs, rfl⟩
  · rintro ⟨t, ht, he⟩
    exact project_injective he ▸ ht

end Matrix.PSL3Three.GraphWitnesses.EightCentralizers
