module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenCentralizers
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenTwoImage

/-!
# The actual A₇ local higher-Thompson and two-group-image bounds

The H.8 pair constructed from the original seed and conjugator discharges
the higher-Thompson premise of E.6.27 for every nonzero subspace of the
actual orbit. The earlier hyperplane result and the two-group Cartan bound
then discharge its other numerical premises. Only original 4.4.3's odd-local
normalizer control remains explicit in this branch.

These are source branches, not the completed r ≥ 6 theorem. The mixed
centralizer geometry and odd-normalizer control must still be proved.
Source: Aschbacher--Smith H.8, E.6.27 and 7.5.5, pp.389,257,701.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE
open Representation.AlternatingSevenConjugatePair.Model
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The first higher Thompson subgroup fixes the whole original orbit. -/
theorem sourceOrbit_seven_local_thompson
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit) :
    ChapterB.thompsonJ (normalizer (L : Set G) ⊓ centralizer (U : Set G)) 1 ≤
      normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) :=
  doubledSeven_local_thompson (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd)
    (D.sourceOrbit_seven_H8_parameters h hd σ hσ hmodel).2.2.2.2.1 hU hUW

/-- E.6.27 on the original local centralizer when its full image is a two-group. -/
theorem sourceOrbit_seven_two_image_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ normalizer (L : Set G))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (htwo : IsPGroup 2 (inducedAutomizer D.sourceOrbit
      (normalizer (L : Set G) ⊓ centralizer (U : Set G)))) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) :=
  doubledSeven_two_image_centralizer (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd)
    (D.sourceOrbit_seven_globalR_gt_one h hd σ hσ hmodel)
    (D.sourceOrbit_seven_H8_parameters h hd σ hσ hmodel).2.2.2.2.1 hodd hU hUW htwo

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
