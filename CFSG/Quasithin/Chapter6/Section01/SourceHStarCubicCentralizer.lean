module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarResidualCentralizer
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarOverlap
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SolvableResidualCommutator

/-!
# The cubic residual model closes the H-star centralizer step

The E.2.1 cubic residual alternatives now supply the actual Thompson
commutator identity for `O²(C_H(⟨Ω₁(Z(T))ᴴ⟩))`. The checked ambient
two-perfect elimination therefore proves the full centralizer equality,
and the original solvable E.2.3 consumer gives `H ∩ M = T`.

Solvability and the cubic residual alternatives remain explicit preceding
source premises. No identification of an unspecified source witness with
the canonical residual is assumed.
Source: Aschbacher--Smith 6.1.5, printed p.666, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The original orbit-centralizer residual has the required commutator
identity under the actual cubic residual model alternatives. -/
theorem hstar_omega_orbit_residual_commutator_of_cubic_models
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hsolv : Group.IsSolvable H)
    (hmodels : ChapterE.SolvableMinimalParabolic.CubicResidualModels H) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let C := centralizer (U : Set H)
    let X := (pResidual 2 C).map C.subtype
    X = ⁅X,elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H)⁆ := by
  let hinput := h.rankOneInput hout
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  have hsq := Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1
  exact ChapterE.ThompsonAction.source_centralizer_residual_commutator_of_cubic_models
    (T.subtype hH.1.1.2) (hinput.hstar_minimal_parabolic hH') _
    (hinput.hstar_omega_orbit_reduced hH')
    (hinput.hstar_thompson_moves_omega_orbit hH' hZH)
    (hsq.stronglyQuasithin 3 (by decide) (by decide)) hsolv hmodels

/-- The source cubic models remove the commutator premise from the full
orbit-centralizer equality in H. -/
theorem hstar_omega_orbit_centralizer_eq_core_of_cubic_models
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hsolv : Group.IsSolvable H)
    (hmodels : ChapterE.SolvableMinimalParabolic.CubicResidualModels H) :
    centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H :=
  h.hstar_omega_orbit_centralizer_eq_core_of_residual_commutator hout hH hm hZH
    (h.hstar_omega_orbit_residual_commutator_of_cubic_models hout hH hZH hsolv hmodels)

/-- The literal final overlap on p.666, with the centralizer equality
discharged by the cubic residual source branch. -/
theorem hstar_inf_maximal_eq_sylow_of_cubic_models
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hsolv : Group.IsSolvable H)
    (hmodels : ChapterE.SolvableMinimalParabolic.CubicResidualModels H) :
    H ⊓ M = (T : Subgroup G) :=
  h.hstar_inf_maximal_eq_sylow_of_solvable_centralizer hout hH hZH hsolv
    (h.hstar_omega_orbit_centralizer_eq_core_of_cubic_models hout hH hm hZH hsolv hmodels)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
