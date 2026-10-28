module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesAssembly
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.FixedInvarianceTransport

/-!
# The chosen fixed-space branch from the remaining B.5 input

Apply the faithful fixed-seed construction to the exact Chapter 12 choice.
The earlier A/C uniqueness theorem, the equality L=L₀, and all subgroup
identifications are discharged. The many-overgroup application also supplies
the proved Thompson commutator. Only the explicitly named B.5 fixed-component
classification implication remains; these are conditional consumers, not a
proof of unconditional source 3.2.5.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
3.2.5, printed p.580, and its use in12.2.2, pp.794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The exact requested normalizer-orbit equality, conditional only on the
remaining B.5 implication and the original earlier Thompson equality. -/
theorem normalizerOrbit_eq_of_fixedComponent
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hclass : FixedComponentInput.{u,u})
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hfix : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    componentOrbit V (normalizer (L : Set G)) = V := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he := Chapter3.Section02.FundamentalSetup.fullModule_eq_seed_of_fixedComponent
    hclass (D.fundamentalSetup h) hu D.localOrbit_eq hcomm
    (by rwa [D.fundamentalSetup_seed])
  rwa [D.fundamentalSetup_fullModule, D.fundamentalSetup_seed] at he

/-- The actual multiple-overgroup branch constructs its Thompson premise. -/
theorem normalizerOrbit_eq_of_fixedComponent_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hclass : FixedComponentInput.{u,u})
    (hfix : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    componentOrbit V (normalizer (L : Set G)) = V :=
  D.normalizerOrbit_eq_of_fixedComponent h.toHypothesis1221 hclass
    (D.thompson_commutator_of_many_of_fixedSpace_ne_bot h hmany hfix) hfix

/-- The source assembly now takes the precise B.5 input in place of the
entire fixed-space invariance callback. Its proof remains to be supplied. -/
theorem source325_of_fixedComponent_of_earlier_inputs_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hclass : FixedComponentInput.{u,u})
    (hfull : D.NormalizerOrbitCubicBound h.toHypothesis1221)
    (hmoved : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ →
      V < componentOrbit V (T : Subgroup G) → D.MarkedDoubled) :
    D.Source325Alternatives :=
  D.source325_of_earlier_inputs_of_many h hmany hfull
    (D.normalizerOrbit_eq_of_fixedComponent h.toHypothesis1221 hclass) hmoved

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
