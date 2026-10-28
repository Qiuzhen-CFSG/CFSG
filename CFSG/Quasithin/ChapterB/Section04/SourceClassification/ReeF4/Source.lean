module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.ReeF4.SourceOddClasses
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.Source

/-!
# The complete Ree branch of the original B.4.2 FF exclusion

The actual Ree carrier, original component quotient and original action are
retained. Finite tensor irreducibility, distinction, exhaustion, torus placement,
odd-order class counting and algebraic universality are all proved upstream.
There is no additional model or earlier-classification certificate in this
source endpoint. Source: Aschbacher--Smith B.4.2; Guralnick--Malle II, 8.8.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.AlgebraicGroup
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- A genuine Ree component is excluded from the original source FF action. -/
theorem reeF4_excluded
    (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    {m : ℕ} (hm : 0 < m) (e : L ⧸ center L ≃* _root_.ReeF4.Model m) : False :=
  reeF4_excluded_of_semisimple_centers h hff hm e
    (fun _ _ _ _ _ _ hH _ hT =>
      SemisimpleCenterContainment.center_le_maximalTorus_of_semisimple hH hT)

end CFSG.Quasithin.ChapterB.SourceClassification
