module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarE23
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.FrattiniSource

/-!
# The H-star orbit centralizer lies in the minimal-parabolic core

The E.2.3 reduction of a noncentral H-star member gives a reduced normal
omega orbit moved by the intrinsic Thompson subgroup.  B.6.10 then puts its
centralizer in the normal core of the unique maximal overgroup of the Sylow
subgroup.  This adapter keeps the literal Chapter 6 carriers and the source
noncentrality premise visible.

Source: Aschbacher--Smith 6.1.5, p.666, using B.2.18 and B.6.10.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The centralizer of the literal H-star omega orbit is in the
normal core of its minimal parabolic. -/
theorem hstar_omega_orbit_centralizer_le_core
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    centralizer
        (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
          Set H) ≤
      ChapterB.minimalParabolicCore (T.subtype hH.1.1.2)
        (RankOneGeneric.Input.hstar_minimal_parabolic
          (h.rankOneInput hout)
          (h.maximal_eq_normalizer_L ▸ hH)) := by
  let hinput := h.rankOneInput hout
  let hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy
    (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := hinput.hstar_omega_orbit_reduced hH'
  let := hU.normal
  let := hU.elementary
  have hmove : ¬ elementaryAbelianMaxJ S ≤ centralizer (U : Set H) :=
    hinput.hstar_thompson_moves_omega_orbit hH' hZH
  exact ChapterB.RankOneBaumann.reduced_centralizer_le_core S
    (hinput.hstar_minimal_parabolic hH') U hU hmove

/-- The same bound after intersecting with the two-residual, in the form used
by the Baumann Frattini arguments. -/
theorem hstar_omega_orbit_residual_centralizer_le_coreFrattini
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    pResidual 2 H ⊓ centralizer
        (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
          Set H) ≤
    ChapterB.BaumannArgument.coreFrattini (pResidual 2 H) := by
  let hinput := h.rankOneInput hout
  let hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy
    (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := hinput.hstar_omega_orbit_reduced hH'
  let := hU.normal
  let := hU.elementary
  have hmove : ¬ elementaryAbelianMaxJ S ≤ centralizer (U : Set H) :=
    hinput.hstar_thompson_moves_omega_orbit hH' hZH
  exact ChapterB.RankOneBaumann.residual_centralizer_le_coreFrattini S
    (hinput.hstar_minimal_parabolic hH') U hU hmove

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
