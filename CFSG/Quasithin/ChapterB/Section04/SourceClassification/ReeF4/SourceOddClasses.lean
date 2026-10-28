module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.ReeF4.SourceFinite
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.Source
/-!
# The Ree FF source branch with its class bound discharged

The unconditional q² bound on the literal finite Ree carrier now closes the
finite Steinberg-family exhaustion used in the original B.4 action. The
single independent earlier algebraic-group input still displayed is the
maximal-torus containment of centers of connected semisimple groups; its
separate source assembly supplies F4 universality. No representation,
conjugacy-class, torus-placement or connected-centralizer premise remains.

Source: Aschbacher–Smith B.4.2; Steinberg (1963), §§3.9 and 12.2.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.AlgebraicGroup ReeF4.BinaryDegree.ExceptionalTensor
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
theorem reeF4_excluded_of_semisimple_centers
    (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    {m : ℕ} (hm : 0 < m) (e : L ⧸ center L ≃* _root_.ReeF4.Model m)
    (hcenters : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
      ∀ (H : Variety F) [AlgebraicGroup H], IsSemisimpleAlgebraicGroup H →
        ∀ T : ClosedSubgroup H, IsMaximalTorus T →
          Subgroup.center (Variety.Point H) ≤ T.toSubgroup) : False :=
  reeF4_excluded_of_class_bound_and_semisimple_centers h hff hm e hcenters
    (Classification.Steinberg.Geometry.OddClasses.model_odd_class_bound m)
end CFSG.Quasithin.ChapterB.SourceClassification
