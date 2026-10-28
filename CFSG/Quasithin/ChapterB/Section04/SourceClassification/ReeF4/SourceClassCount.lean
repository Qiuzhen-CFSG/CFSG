module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.Counting
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.ReeF4.SourceFinite
/-!
# Original Ree FF exclusion through the proved class-coordinate count

The actual Ree odd-order class injection discharges the previous class-bound
input of the full finite Steinberg-family exhaustion. This is applied to the
original B.4 action and central quotient. Two separate earlier algebraic-group
statements remain explicit: maximal-torus containment of semisimple-group
centers, and connectedness of actual odd semisimple F4 point centralizers.
All representation-theoretic, torus-coordinate and counting conclusions are
proved by the imported source families.

Source: Aschbacher–Smith B.4.2; Steinberg (1963), §§3.9 and 12.2.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.AlgebraicGroup ReeF4.BinaryDegree.ExceptionalTensor
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v w
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem reeF4_excluded_of_semisimple_centers_and_connected_centralizers
    (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    {m : ℕ} (hm : 0 < m) (e : L ⧸ center L ≃* _root_.ReeF4.Model m)
    (hcenters : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
      ∀ (H : Variety F) [AlgebraicGroup H], IsSemisimpleAlgebraicGroup H →
        ∀ T : ClosedSubgroup H, IsMaximalTorus T →
          Subgroup.center (Variety.Point H) ≤ T.toSubgroup)
    {F : Type w} [Field F] [IsAlgClosed F] [CharP F 2]
    (f : _root_.ReeF4.CoefficientField m →+* F)
    (hconnected : ∀ x : _root_.ReeF4.Model m, (¬ 2 ∣ orderOf x) →
      Variety.IsConnected (Classification.Steinberg.Geometry.SemisimpleCentralizers.pointCentralizer
        (Classification.Steinberg.modelEmbedding f x)).carrierVariety) : False := by
  exact reeF4_excluded_of_class_bound_and_semisimple_centers h hff hm e hcenters
    (Classification.Steinberg.Geometry.OddClasses.model_odd_class_bound_of_connected_centralizers
      m f hconnected)
end CFSG.Quasithin.ChapterB.SourceClassification
