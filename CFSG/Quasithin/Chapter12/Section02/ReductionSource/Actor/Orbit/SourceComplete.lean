module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.GuardedSource318
public import CFSG.Quasithin.Chapter3.Section01.Source318Complete

/-!
# The chosen-module orbit bound from the proved source theorem

The original simple QTKE hypothesis supplies guarded Theorem 3.1.8(1).
The existing intrinsic quotient identification then bounds the whole
chosen-module orbit. The standing outside-maximal-local condition is
retained exactly where the source uses the post-2.1.1 standing assumption.

Source: Aschbacher--Smith 3.1.8(1), 3.2.5 and 12.2.2, pp.576,580,794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual chosen-module orbit satisfies the source cubic bound. -/
theorem orbit_cubicRatio_le_source (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hout : ∀ M : Subgroup G, IsMaximalTwoLocal M → (T : Subgroup G) ≤ M →
      Chapter3.HasMaximalOutside T M) : cubicRatio D.orbitRepresentation ≤ 2 :=
  D.orbit_cubicRatio_le_of_guarded_source318 h
    (Chapter3.source_guardedTheorem318One h.simpleQTKE) hout

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
