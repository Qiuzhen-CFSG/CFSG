module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarMarkedFiveComponent
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarPairedFiveCentralizer
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarSolvableCentralizer

/-!
# The full centralizer of the original H-star omega orbit

The solvable branch uses the actual cubic residual models. In the remaining
single and paired marked-five rows the original component calculations remove
the full odd central kernel. Thus every noncentral H-star member has precisely
its two-core as the centralizer of its original omega orbit.

This discharges the centralizer premise of the original Cartan-join calculation.
It does not exclude the nonsolvable marked-five rows or assert solvability.
Source: Aschbacher--Smith 6.1.5, printed pp.666--667.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The literal orbit centralizer is the two-core, in every surviving row. -/
theorem hstar_omega_orbit_centralizer_eq_core
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    centralizer
      ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H :
        Set H) = pCore 2 H := by
  by_cases hs : Group.IsSolvable H
  · exact h.hstar_omega_orbit_centralizer_eq_core_of_solvable hout hH
      (h.omega_natural_fixed_quotient_of_hstar_moves hout hH hZH) hZH hs
  · rcases (h.hstar_marked_five_component_or_pair hout hH hZH hs).2 with
      ⟨_, _, _, _, _, hc⟩ | hpair
    · exact hc
    · exact h.hstar_paired_five_centralizer_eq_core hout hH hZH hs hpair

/-- The actual left Cartan join now has its core and centralizers without
an additional orbit-kernel or natural-module premise. -/
theorem exists_hstar_left_cartan_full_centralizer_geometry
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    ∃ A : Subgroup G, A ≤ RankOneGeneric.localBorel T L ∧
      IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (RankOneGeneric.localBorel T L)) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      A ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ ∧
      A ⊔ H ∈ Chapter1.HOver G (T : Set G) ∧
      (let X := A ⊔ H
       let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
       X.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (U : Set G) ∧
       H ⊓ centralizer (U : Set G) = X.pCoreIn 2 ∧
       (A ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) = X.pCoreIn 2 ∧
       Chapter1.IsSylowIn 2 (X.pCoreIn 2) (X ⊓ centralizer (U : Set G))) :=
  h.exists_hstar_left_cartan_centralizer_geometry hout hH
    (h.omega_natural_fixed_quotient_of_hstar_moves hout hH hZH) hZH
    (h.hstar_omega_orbit_centralizer_eq_core hout hH hZH)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
