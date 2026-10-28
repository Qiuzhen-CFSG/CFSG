module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesFixedInput
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.FixedInvarianceClassificationOuter

/-!
# The original chosen-seed fixed-space branch of 3.2.5

The complete B.5 fixed-component argument supplies the last input in the
faithful offender-action construction. Thus the original chosen seed, not
merely an isomorphic module or a quotient, equals its full normalizer orbit.
The multiple-overgroup version constructs the earlier Thompson commutator
equality. The final source assembly retains only the separate numerical
and moved-seed inputs owned by `qt-baumann-fsu`.

Source: Aschbacher--Smith 3.2.5, p.580, D.3.20, p.204, and12.2.2, pp.794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The exact fixed-space implication in the original source 3.2.5 assembly. -/
theorem normalizerOrbit_eq_of_fixedSpace_ne_bot
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hfix : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    componentOrbit V (normalizer (L : Set G)) = V :=
  D.normalizerOrbit_eq_of_fixedComponent h fixedComponentInput_knownSimple hcomm hfix

/-- The multiple-overgroup hypotheses supply the Thompson equality as well. -/
theorem normalizerOrbit_eq_of_fixedSpace_ne_bot_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfix : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    componentOrbit V (normalizer (L : Set G)) = V :=
  D.normalizerOrbit_eq_of_fixedComponent_of_many h hmany fixedComponentInput_knownSimple hfix

/-- The actual source assembly, with the fixed-space callback discharged.
The numerical and moved classification premises remain with `qt-baumann-fsu`. -/
theorem source325_of_earlier_inputs_of_many_fixed_complete
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : D.NormalizerOrbitCubicBound h.toHypothesis1221)
    (hmoved : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.MarkedDoubled) :
    D.Source325Alternatives :=
  D.source325_of_fixedComponent_of_earlier_inputs_of_many h hmany
    fixedComponentInput_knownSimple hfull hmoved

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
