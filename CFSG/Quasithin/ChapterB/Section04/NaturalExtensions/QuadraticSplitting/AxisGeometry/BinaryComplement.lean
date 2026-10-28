module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Displacement

/-!
# The binary coordinate complement

In defining-field degree one, the marked quotient axis supplies exactly the
three orbit facts used by the displacement construction: the canonical line
vector has trivial axis-group stabilizer, it is outside the fixed space, and
every quotient vector is a binary multiple of it plus one axis displacement.
Together with a fixed lift, these facts feed the general complement theorem.

Source: Aschbacher–Smith B.4.9(1), printed p.93, combined manuscript of
1 March 2004. The upstairs fixed-lift premise remains explicit here; it is
provided by the independent Levi-lifting argument.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ}

namespace QuotientCoordinates

variable (m : QuotientCoordinates d) (j : Fin n)

/-- The marked binary quotient orbit gives a complement from any fixed lift of
the canonical line vector. -/
theorem binary_coordinate_complement (hF : F.degree = 1) (hn : 2 ≤ n)
    (hq : IsQuadratic ρ (m.Q j)) (hf : m.FixedLifts j) :
    ∃ v : V, v ∈ fixedSpace ρ (m.K j) ∧
      IsCompl d.space.toSubmodule
        (localSpace ρ (m.Q j) hq v) := by
  obtain ⟨v, hvK, hv⟩ := m.exists_fixed_lineVector j hf
  refine ⟨v, hvK, ?_⟩
  apply localSpace_isCompl ρ (m.Q j) hq v d.space
  · intro x hx
    apply m.lineVector_free j x
    rw [← hv]
    exact hx
  · intro h
    apply m.lineVector_not_fixed j hn
    rw [← hv]
    exact h
  · intro z
    simpa only [hv] using m.binary_lineVector_cover j hF z

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
