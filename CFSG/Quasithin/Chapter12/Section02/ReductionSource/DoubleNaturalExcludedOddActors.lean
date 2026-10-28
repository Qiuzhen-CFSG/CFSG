module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.Escaping
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.JankoExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedOddCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedWeakClosure

/-!
# The original escaping actors and their doubled-branch consumer

The relative Sylow and Cartan construction supplies the actual odd actor
for every escaping subspace centralizer. The completed nonsingular theorem
discharges its rank input. In degree five, the completed pure-point theorem
and first weak-closure bound discharge every earlier premise of that
construction. Degree four retains precisely the original marked omega
premise from the existing pure-fusion/MS producers.

The exclusion theorems below remove the escaping-actor callback from the
terminal argument: the literal fixed spaces give r ≥ n+2, the second
weak-closure bound gives w > 2, and E.3.35 gives the contradiction.
Odd-normalizer control (12.1.9(1)) remains an explicit, unproved source
input. Its proof and the final unconditional assembly remain with
qt-d-1222-double-natural; these are not unconditional 12.1.11 theorems.
Source: Aschbacher--Smith, 12.1.8--11, printed pp.792--794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
include D h

/-- Both degrees have the required escaping actors once the first weak-closure
bound is available; the rank input is supplied by the original centralizer theorem. -/
theorem doubledOrbit_escapingOddActors_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hw : (1 : ℕ∞) < globalW (componentOrbit V (T : Subgroup G)) T) :
    EscapingOddActors (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) := by
  exact D.doubledOrbit_escapingOddActors_of_many_of_rank h hmany B hw
    (D.doubleNatural_nonsingular_controls_of_many h hmany B).2.1

/-- The original degree-five escaping-actor assertion, with all of its
centralizer, rank and weak-closure inputs discharged. -/
theorem doubledFive_escapingOddActors_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    EscapingOddActors (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) := by
  let := D.doubledOrbit_elementary h
  obtain ⟨hc,hp,hw⟩ := D.doubleNatural_five_conclusions_of_many h hmany B
  have hr := B.globalR_ge (D.doubledOrbit_normalizer_eq h B.orbit_eq) hc
  exact D.doubledOrbit_escapingOddActors_of_many h hmany B
    (D.doubled_globalW_gt_one_of_many h hmany B hp hw hr)

/-- In degree four only the original marked omega premise remains in the
escaping-actor construction; the full original core is retained. -/
theorem doubledFour_escapingOddActors_of_omega_fixed_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) →
    EscapingOddActors (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G)) := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  obtain ⟨hc,hp,hw⟩ := D.doubleNatural_conclusions_of_omega_fixed_of_many h hmany B
    (fun _ => hfixed)
  have hr := B.globalR_ge (D.doubledOrbit_normalizer_eq h B.orbit_eq) hc
  exact D.doubledOrbit_escapingOddActors_of_many h hmany B
    (D.doubled_globalW_gt_one_of_many h hmany B hp hw hr)

/-- Actual fixed-space and generation application with the escaping-actor
premise proved. The remaining odd-normalizer premise is 12.1.9(1). -/
theorem doubleNatural_excluded_of_many_of_odd_control
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hodd : OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    letI := D.doubledOrbit_elementary h
    B.PureIntersectionCentralizes →
    0 < globalW (componentOrbit V (T : Subgroup G)) T → False := by
  let := D.doubledOrbit_elementary h
  intro hp hw
  obtain ⟨hc,hr,_⟩ := D.doubleNatural_nonsingular_controls_of_many h hmany B
  have hw1 := D.doubled_globalW_gt_one_of_many h hmany B hp hw hr
  have ha := D.doubledOrbit_escapingOddActors_of_many h hmany B hw1
  obtain ⟨hf,_,hg⟩ := D.doubledOrbit_parameters_of_many_of_odd_inputs h hmany B hw1 hodd ha hc
  exact D.doubleNatural_excluded_of_many_of_source_geometry h hmany B hg hp hw hc hf

/-- Degree five now retains only odd-normalizer control: every initial
centralizer/pure-point input, escaping actor and weak-closure bound is proved. -/
theorem doubleNatural_five_excluded_of_many_of_odd_control
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hodd : OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    False := by
  let := D.doubledOrbit_elementary h
  obtain ⟨_,hp,hw⟩ := D.doubleNatural_five_conclusions_of_many h hmany B
  exact D.doubleNatural_excluded_of_many_of_odd_control h hmany B hodd hp hw

/-- The separate degree-four implication retains exactly the earlier marked
omega premise, in addition to the still-open odd-normalizer source theorem. -/
theorem doubleNatural_four_excluded_of_many_of_omega_fixed_of_odd_control
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (hodd : OddNormalizerControl (componentOrbit V (T : Subgroup G)) (normalizer (L : Set G))) :
    letI := D.doubledOrbit_elementary h
    (∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) → False := by
  let := D.doubledOrbit_elementary h
  intro hfixed
  obtain ⟨_,hp,hw⟩ := D.doubleNatural_conclusions_of_omega_fixed_of_many h hmany B
    (fun _ => hfixed)
  exact D.doubleNatural_excluded_of_many_of_odd_control h hmany B hodd hp hw

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
