module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.Assembly
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.MinimalLift
public import FeitThompson.FinalTheorem
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.PrimeAutomizer.Source

/-!
# The source cover reduced to prime-field automizer geometry

The odd-rank bound makes the nonnormal component normalizer an index-two
normal subgroup. The component orbit supplies the exact Sylow image and
its supplement in N(K)/C(K). Thus automizer minimality lifts to ambient
minimality, with no additional input in that branch.

The prime-field automizer dichotomy supplies either minimality or a
generating family of solvable subgroups invariant under the full prescribed
Sylow image. Together with the minimality lift, it discharges the structural
cover unconditionally. The conditional interface remains available.

Source: Aschbacher--Smith E.1.11--14, paired E.2.2 and 10.3.3,
printed pp.212--216 and 756--757.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
universe u

/-- The ambient minimality input is discharged for the original moved component. -/
theorem movedAutomizerMinimalLift : MovedAutomizerMinimalLift.{u} := by
  intro H _ _ hH _ S K hK hs hn hgen R hR hmin
  let := hs
  let := hK.2
  have heven : 2 ∣ Nat.card K := by
    by_contra he
    have hodd : Odd (Nat.card K) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using he)
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K hodd)
  have hN : (normalizer (K : Set H)).Normal := by
    rcases hK.normal_or_index_two_of_odd_rank_le_two hH.stronglyQuasithin with h | h
    · exact (hn h).elim
    · exact normal_of_index_eq_two h
  have ho := ChapterE.Structure.generating_component_orbit_eq_residual
    hH.stronglyQuasithin S hK hgen
  have hsup : NormalizerAction.componentImage K ⊔ (R : Subgroup _) = ⊤ := by
    rw [hR]
    exact component_automizer_sylow_supplement S hK ho
  exact minimalParabolic_of_component_automizer S hK heven hN hgen R hR hsup hmin

/-- The only remaining cover input is the concrete prime-field automizer geometry.
This conditional theorem does not assert the unconditional source contract. -/
theorem coreFreeMovedPrimeCover_of_primeAutomizerDichotomy
    (hmodels : PrimeAutomizerCoverDichotomy.{u}) : CoreFreeMovedPrimeCover.{u} :=
  coreFreeMovedPrimeCover_of_automizer_inputs hmodels movedAutomizerMinimalLift

/-- The structural cover for the original core-free moved odd-prime configuration.
The automizer geometry and the ambient minimality lift are both discharged. -/
theorem coreFreeMovedPrimeCover : CoreFreeMovedPrimeCover.{u} :=
  coreFreeMovedPrimeCover_of_primeAutomizerDichotomy primeAutomizerCoverDichotomy

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
