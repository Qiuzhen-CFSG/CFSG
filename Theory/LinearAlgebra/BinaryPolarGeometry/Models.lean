module

public import Theory.LinearAlgebra.BinaryPolarGeometry
public import Theory.SpecificGroups.PSp4Three.MatrixModel

/-!
# Actual symplectic models of the binary reconstruction hypotheses

The nonzero vectors of any nondegenerate alternating binary space satisfy
the geometric hypotheses: the third point is the sum, and orthogonality to
the sum gives the one-or-all rule. In particular the smallest model has
three points and reconstructs dimension two, while the six-space model has
63 points and reconstructs dimension six. Cardinality is therefore essential
to the C₃ conclusion; the one-or-all rule alone does not specify the rank.

These checks concern the reconstruction interface, not a replacement for
the D-system hypotheses in Aschbacher–Smith I.5.1.
-/

public noncomputable section
namespace Theory.LinearAlgebra.BinaryPolarGeometry
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary_one_or_all (a b : ZMod 2) :
    (a = 0 ∧ b = 0 ∧ a + b = 0) ∨
    (a = 0 ∧ b ≠ 0 ∧ a + b ≠ 0) ∨
    (a ≠ 0 ∧ b = 0 ∧ a + b ≠ 0) ∨
    (a ≠ 0 ∧ b ≠ 0 ∧ a + b = 0) := by
  revert a b
  decide

theorem data_of_form (B : LinearMap.BilinForm (ZMod 2) V)
    (hAlt : B.IsAlt) (hN : B.Nondegenerate) :
    Data (fun x y : {v : V // v ≠ 0} => B x y = 0) := by
  classical
  have hself (v : V) : v + v = 0 := by
    simpa only [add_smul, one_smul, zero_smul] using
      congrArg (fun a : ZMod 2 => a • v) (show (1 : ZMod 2) + 1 = 0 from rfl)
  refine ⟨fun x => hAlt x, fun h => hAlt.isRefl _ _ h, ?_, ?_⟩
  · intro x
    by_contra h
    apply x.property
    apply hN.1
    intro y
    by_cases hy : y = 0
    · subst y; exact map_zero (B x)
    · exact not_not.mp (fun hn => h ⟨⟨y, hy⟩, hn⟩)
  · intro x y hxy
    have hz : x.val + y.val ≠ 0 := by
      intro h
      apply hxy
      apply Subtype.ext
      exact (eq_neg_of_add_eq_zero_left h).trans
        (neg_eq_of_add_eq_zero_left (hself y.val))
    refine ⟨⟨x.val + y.val, hz⟩, ?_⟩
    intro w
    change (B w x = 0 ∧ B w y = 0 ∧ B w (x.val + y.val) = 0) ∨ _
    simp only [map_add]
    exact binary_one_or_all _ _

theorem standard_model (n : ℕ) : Data
    (fun x y : {v : Matrix.PSp4Three.Vector n (ZMod 2) // v ≠ 0} =>
      Matrix.PSp4Three.form x.val y.val = 0) :=
  data_of_form _ Matrix.PSp4Three.form_alternating Matrix.PSp4Three.form_nondegenerate

theorem standard_three_points :
    Nat.card {v : Matrix.PSp4Three.Vector 1 (ZMod 2) // v ≠ 0} = 3 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  norm_num [Matrix.PSp4Three.Vector, Matrix.PSp4Three.Index, Fintype.card_fun]

theorem standard_sixtyThree_points :
    Nat.card {v : Matrix.PSp4Three.Vector 3 (ZMod 2) // v ≠ 0} = 63 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  norm_num [Matrix.PSp4Three.Vector, Matrix.PSp4Three.Index, Fintype.card_fun]

theorem smallest_reconstructed_dimension : Module.finrank (ZMod 2) (Space
    (fun x y : {v : Matrix.PSp4Three.Vector 1 (ZMod 2) // v ≠ 0} =>
      Matrix.PSp4Three.form x.val y.val = 0)) = 2 :=
  (standard_model 1).space_finrank 2 (by rw [standard_three_points]; decide)

theorem six_reconstructed_dimension : Module.finrank (ZMod 2) (Space
    (fun x y : {v : Matrix.PSp4Three.Vector 3 (ZMod 2) // v ≠ 0} =>
      Matrix.PSp4Three.form x.val y.val = 0)) = 6 :=
  (standard_model 3).space_finrank 6 (by rw [standard_sixtyThree_points]; decide)

end Theory.LinearAlgebra.BinaryPolarGeometry
