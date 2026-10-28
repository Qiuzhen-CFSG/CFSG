module

public import Theory.SpecificGroups.PSL3Three.Basic
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions

/-!
# An order-thirteen element inverted by the graph automorphism of PSL₃(3)

A symmetric determinant-one matrix of order thirteen gives a literal element
inverted by inverse transpose. Its determinant, symmetry and thirteenth power
are small kernel-checked calculations over `ZMod 3`. The injective canonical
SL₃(3) projection preserves its order. Transport by an actual automorphism
then supplies the same witness for every conjugate of inverse transpose.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10. The conjugacy of arbitrary outer involutions is a separate
input; this module proves the concrete inversion calculation and its transport.
-/

public section

namespace Matrix.PSL3Three.GraphWitnesses
open Matrix

private def symmetricSinger : SL :=
  ⟨!![0, 0, 1; 0, 2, 1; 1, 1, 0], by decide⟩

private theorem orderOf_symmetricSinger : orderOf symmetricSinger = 13 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide) (by decide)

private theorem symmetricSinger_transpose :
    SpecialLinearGroup.transpose symmetricSinger = symmetricSinger := by
  decide

/-- Inverse transpose inverts an explicit order-thirteen element of PSL₃(3). -/
theorem graph_inverts_thirteen :
    ∃ x : PSL, orderOf x = 13 ∧
      Matrix.PSL3.OuterSolvable.graph (ZMod 3) x = x⁻¹ := by
  refine ⟨project symmetricSinger, ?_, ?_⟩
  · rw [orderOf_injective project project_injective]
    exact orderOf_symmetricSinger
  · change Matrix.PSL3.OuterSolvable.graph (ZMod 3)
      (QuotientGroup.mk symmetricSinger) = (project symmetricSinger)⁻¹
    rw [Matrix.PSL3.OuterSolvable.graph_mk, symmetricSinger_transpose]
    exact map_inv project symmetricSinger

/-- Conjugating inverse transpose preserves its order-thirteen inverter. -/
theorem inverts_thirteen_of_graph_conjugate (b : MulAut PSL)
    (hc : ∃ u : MulAut PSL,
      b = u * Matrix.PSL3.OuterSolvable.graph (ZMod 3) * u⁻¹) :
    ∃ x : PSL, orderOf x = 13 ∧ b x = x⁻¹ := by
  obtain ⟨u, rfl⟩ := hc
  obtain ⟨x, hx, hg⟩ := graph_inverts_thirteen
  refine ⟨u x, (u.orderOf_eq x).trans hx, ?_⟩
  change u (Matrix.PSL3.OuterSolvable.graph (ZMod 3) (u.symm (u x))) = (u x)⁻¹
  rw [u.symm_apply_apply, hg, map_inv]

end Matrix.PSL3Three.GraphWitnesses
