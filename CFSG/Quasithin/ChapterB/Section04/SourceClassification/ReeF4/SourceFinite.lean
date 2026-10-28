module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.ReeF4.UniversalSource
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction

/-!
# The Ree FF source branch with every finite module classification clause proved

Actual native root actions and invariant pairings prove finite irreducibility.
The intrinsic highest line, native torus characters and Weyl-word zero-column
markers distinguish the binary tensor parameters. The modular simple-family
count then exhausts all finite irreducible modules on the literal Ree carrier.
This supplies all three finite Steinberg clauses in the original B.4.2 action.

Two independent earlier-source results remain explicit: the genuine q² bound
on odd-order conjugacy classes of the original finite carrier, and center
containment in every maximal torus of a connected semisimple algebraic group.
The latter supplies actual F4 universality through the checked isogeny assembly.
There is no extra representation, fixed-space or local FF-exclusion premise.

Source: Aschbacher–Smith B.4.2; Steinberg (1963), 3.9 and 12.2;
GLS3 1.9.5(h), 1.12.5(b); Guralnick–Malle II, Lemma 8.8.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.AlgebraicGroup ReeF4.BinaryDegree.ExceptionalTensor
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The original source action is excluded using only the two independent
earlier algebraic and conjugacy-class inputs. -/
theorem reeF4_excluded_of_class_bound_and_semisimple_centers
    (h : ChapterK.RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    {m : ℕ} (hm : 0 < m) (e : L ⧸ center L ≃* _root_.ReeF4.Model m)
    (hcenters : ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
      ∀ (H : Variety F) [AlgebraicGroup H], IsSemisimpleAlgebraicGroup H →
        ∀ T : ClosedSubgroup H, IsMaximalTorus T →
          Subgroup.center (Variety.Point H) ≤ T.toSubgroup)
    (hclasses : Nat.card (ConjClasses.mk '' {g : _root_.ReeF4.Model m | ¬ 2 ∣ orderOf g}) ≤
      Nat.card (Classification.Steinberg.RestrictedWeight m)) : False := by
  apply reeF4_excluded_of_finite_distinction_classes_and_centers h hff hm e hcenters _ hclasses
  intro F _ _ _ B C hB hC he
  exact Classification.Steinberg.FiniteRootAction.exceptionalTensor_distinction
    m (Classification.Steinberg.Geometry.carrier_isUniversalVersion_of_semisimple_centers
      (hcenters F)) B C hB hC he

end CFSG.Quasithin.ChapterB.SourceClassification
