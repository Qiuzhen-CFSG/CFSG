module

public import Theory.Combinatorics.SimpleGraph.QuadrangleTwentySeven.Canonical
public import Theory.Combinatorics.SimpleGraph.QuadrangleTwentySeven.Bound

/-!
# Recognition of the 27-point quadrangle

This source-facing module re-exports the coordinate recognition and the
51840 automorphism bound for finite SRG graphs with parameters `(27,10,1,5)`.
The native U₄(2) consumer supplies these parameters from its two residue types.
-/

public section
namespace Theory.Combinatorics.QuadrangleTwentySeven

/-- The complete finite-geometry interface used by the U₄(2) recognition. -/
theorem source_recognition {V : Type*} [Fintype V] (Γ : SimpleGraph V)
    [DecidableRel Γ.Adj] (h : Γ.IsSRGWith 27 10 1 5) :
    Nonempty (canonical ≃g Γ) ∧ Nat.card (Γ ≃g Γ) ≤ 51840 := by
  exact ⟨exists_coordinateIso Γ h, automorphism_card_le h⟩

end Theory.Combinatorics.QuadrangleTwentySeven
