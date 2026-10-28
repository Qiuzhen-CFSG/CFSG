module

public import Theory.AlgebraicGroup.Solvable.TorusComplementConjugacy

/-!
# Maximal-torus conjugacy in connected solvable groups

Any two maximal subtori of a connected solvable algebraic group are conjugate.
This is the conjugacy assertion of Borel, *Linear Algebraic Groups*, Chapter III,
Theorem 10.6(4), and is the solvable input to Corollary 11.3(1).

The proof first constructs a maximal torus complement to the connected
unipotent radical.  The complement-conjugacy argument applies more generally
to any maximal torus, so each given torus is conjugate to this common
complement by a point of the radical.  Composing the two conjugations gives the
claimed ambient conjugacy.  The module uses the low-level `IsMaximalTorus`
predicate from `Tori.Basic` and remains below `Tori.Maximal` in the import
graph.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Maximal subtori of a connected solvable algebraic group are conjugate. -/
public theorem maximalTori_conjugate_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    {T₁ T₂ : ClosedSubgroup G}
    (hT₁ : IsMaximalTorus T₁) (hT₂ : IsMaximalTorus T₂) :
    ∃ g : Variety.Point G, T₂ = T₁.conjugate g := by
  obtain ⟨U, hUrad, _hUconnected, M, hMcomplement, _hMmaximal⟩ :=
    exists_maximalTorus_complement_of_solvable_connected
      hsolvable hconnected
  obtain ⟨u₁, _hu₁U, hT₁M⟩ :=
    maximalTorus_conjugate_to_torusComplement_by_unipotentRadical
      hsolvable hconnected U M T₁ hUrad hMcomplement hT₁
  obtain ⟨u₂, _hu₂U, hT₂M⟩ :=
    maximalTorus_conjugate_to_torusComplement_by_unipotentRadical
      hsolvable hconnected U M T₂ hUrad hMcomplement hT₂
  refine ⟨u₂⁻¹ * u₁, ?_⟩
  calc
    T₂ = (T₂.conjugate u₂).conjugate u₂⁻¹ := by
      rw [ClosedSubgroup.conjugate_conjugate, inv_mul_cancel,
        ClosedSubgroup.conjugate_one]
    _ = M.conjugate u₂⁻¹ := by rw [hT₂M]
    _ = (T₁.conjugate u₁).conjugate u₂⁻¹ := by rw [hT₁M]
    _ = T₁.conjugate (u₂⁻¹ * u₁) :=
      ClosedSubgroup.conjugate_conjugate T₁ u₁ u₂⁻¹

end Theory.AlgebraicGroup
