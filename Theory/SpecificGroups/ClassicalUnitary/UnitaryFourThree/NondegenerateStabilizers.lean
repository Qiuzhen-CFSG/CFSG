module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Geometry
public import Mathlib.GroupTheory.Solvable

/-!
# Reduction of nondegenerate stabilizers in PSU₄(3)

The geometric dimension formula leaves dimensions one, two and three.
Orthogonal complementation preserves the actual projective stabilizer and
turns dimension three into dimension one. Coordinate transport and the two
coordinate stabilizer calculations then give the required alternative.

The assembly below is conditional. Its three premises are the remaining
mathematical obligations: arbitrary-subspace transport to coordinates, the
projective line stabilizer identification with PSU₃(3), and solvability of the
projective plane stabilizer. In particular, an SU block calculation alone does
not supply the projective line premise: its order-four scalar kernel must be
accounted for. The unconditional stabilizer theorem remains to be assembled
when those obligations have been proved.

Source: Aschbacher–Smith, Theorem 0.1.2(4) and condition K, printed pp.4,482
of `refs/quasithin.pdf`; unitary model conventions in GLS3, chapter 2.
-/

open Module
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers

/-- Coordinate transport and the two coordinate stabilizer calculations suffice for
all nonzero proper nondegenerate subspaces, including dimension three. -/
theorem stabilizer_alternative_of_coordinate_models
    (htransport : ∀ (W : Submodule FiniteField.Nine (Space 4)) (d : ℕ),
      (d = 1 ∨ d = 2) → radical W = ⊥ → finrank FiniteField.Nine W = d →
        Nonempty (projectiveStabilizer W ≃* projectiveStabilizer (coordinateSubspace d)))
    (hline : Nonempty (projectiveStabilizer (coordinateSubspace 1) ≃* Carrier 3))
    (hplane : Group.IsSolvable (projectiveStabilizer (coordinateSubspace 2)))
    (W : Submodule FiniteField.Nine (Space 4))
    (h0 : W ≠ ⊥) (ht : W ≠ ⊤) (hr : radical W = ⊥) :
    Group.IsSolvable (projectiveStabilizer W) ∨
      Nonempty (projectiveStabilizer W ≃* Carrier 3) := by
  have line_case (L : Submodule FiniteField.Nine (Space 4))
      (hL : radical L = ⊥) (hd : finrank FiniteField.Nine L = 1) :
      Nonempty (projectiveStabilizer L ≃* Carrier 3) := by
    obtain ⟨e⟩ := htransport L 1 (Or.inl rfl) hL hd
    obtain ⟨f⟩ := hline
    exact ⟨e.trans f⟩
  rcases finrank_cases W h0 ht with h1 | h2 | h3
  · exact Or.inr (line_case W hr h1)
  · obtain ⟨e⟩ := htransport W 2 (Or.inr rfl) hr h2
    let : Group.IsSolvable (projectiveStabilizer (coordinateSubspace 2)) := hplane
    exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · apply Or.inr
    have hdim : finrank FiniteField.Nine (orthogonal W) = 1 := by
      rw [finrank_orthogonal, h3]
    have h := line_case (orthogonal W) ((radical_orthogonal W).trans hr) hdim
    rwa [projectiveStabilizer_orthogonal] at h

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers
