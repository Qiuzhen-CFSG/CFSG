module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.MaximalParabolics

/-!
# Maximality of the marked first full-Ree parabolic

The native binary octagonal datum identifies the original Suzuki parabolic
with one of its two maximal standard parabolics.
Source: Aschbacher–Smith J.5.3, printed p.445, and GLS3 2.6.5.
-/

public section
namespace Tits.ExceptionalParabolics.FullRee

/-- The actual marked first parabolic is maximal in the full binary Ree carrier. -/
theorem first_isCoatom : IsCoatom first := by
  obtain ⟨D⟩:=ReeF4.Octagon.Binary.exists_native_datum
  rw [first_eq_parabolic]
  apply D.parabolic_isCoatom_of_two (j:=.linear) (by decide)
  intro k
  cases k <;> simp

end Tits.ExceptionalParabolics.FullRee
