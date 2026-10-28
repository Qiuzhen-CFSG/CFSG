module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Data
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Cover
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Recovery
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets
public import Theory.GroupTheory.DoubleCosetGeneratorRecovery
import Mathlib.Tactic.Group

/-!
# Absolute maximality of Held max5: assembly of two finite checks

The existing 4,831-double-coset cover is transported into max5 coordinates.
The proposed left factors are in max5 precisely when they commute with its
central involution; their right factors are words in the two max5 generators.
Thus CoverChecks reduces every outside element to one of 33 fixed outside
representatives. RecoveryChecks recovers b from each representative and
max5. Since adjoining b generates Held, every strict overgroup is the whole
group. This is maximality among all subgroups, without any simplicity premise.

The conditional assembly retains its two finite checking premises explicitly.
The final theorem `max5_isCoatom` discharges both with the kernel-checked
certificates from `Cover` and `Recovery`. It supplies the literal maximality
premise of `RankOneLocalPair.maximalOvergroups_of_realization_and_max5`;
the matrix quotient and automorphism realization are separate inputs there.
Source: ATLAS HeG1-max5W1; the application is the Held maximal local used in
Aschbacher–Smith E.1.14(4), refs/quasithin.pdf, printed p.214.
-/

public section

open Subgroup Theory.GroupTheory.DoubleCosetTransitions
open Held Held.TwoLocalCandidates
open Held.LocalPairs.PairCoverage.SylowOvergroups
namespace Held.RankOneLocalPair.ConcreteMaximality

theorem rightFactor_mem (j : Fin 4831) : rightFactor j ∈ max5 := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  cases i
  · exact max5First_mem
  · exact max5Second_mem

theorem representative_covered (h : CoverChecks) (j : Fin 4831) :
    Covered max5 shortRepresentative (transport (representative j)) := by
  have hl : leftFactor j ∈ max5 := by
    rw [← InvolutionFixedData.TwoB.centralizer_eq_max5]
    exact mem_centralizer_singleton_iff.mpr (h j)
  refine ⟨coverIndex j, leftFactor j, rightFactor j, hl, rightFactor_mem j, ?_⟩
  unfold leftFactor
  group

theorem covers_of_checks (h : CoverChecks) (g : He) :
    Covered max5 shortRepresentative g := by
  obtain ⟨j, u, v, hu, hv, hg⟩ := DoubleCosets.covers (transport.symm g)
  have he : g = transport u * transport (representative j) * transport v := by
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg transport hg
  rw [he]
  exact ((representative_covered h j).mul_left
    (marked_le (mem_map_of_mem transport.toMonoidHom hu))).mul_right
    (marked_le (mem_map_of_mem transport.toMonoidHom hv))

/-- Both finite certificates imply absolute maximality; their discharge remains explicit. -/
theorem max5_isCoatom_of_checks (hc : CoverChecks) (hr : RecoveryChecks) :
    IsCoatom max5 := by
  apply isCoatom_of_doubleCoset_generator_recovery max5 b proper generation
    shortRepresentative
  · intro g _
    obtain ⟨j,u,v,hu,hv,hg⟩ := covers_of_checks hc g
    exact ⟨j,u,hu,v,hv,hg⟩
  · intro i
    refine Fin.cases ?_ (fun j _ => hr j) i
    intro hi
    exact False.elim (hi (by rw [shortRepresentative_zero]; exact max5.one_mem))

/-- The literal ATLAS max5 is maximal among all subgroups of the actual Held carrier. -/
theorem max5_isCoatom : IsCoatom max5 :=
  max5_isCoatom_of_checks coverChecks recoveryChecks

end Held.RankOneLocalPair.ConcreteMaximality
