module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarE23

/-!
# Thompson factorization in the opening of 6.1.5

For the original H-star omega orbit, the preceding source interface supplies
minimal parabolicity, reducedness and Thompson movement. E.2.3 therefore gives
`O²(H) ≤ J(H)`, `H = J(H)T` and `C_T(⟨Z^H⟩) = O₂(H)`.

The stronger centralizer equality and the overlap `H ∩ M = T` still require
the natural-module argument of 6.1.5. The applications below retain the
original source hypotheses and do not assert those stronger conclusions.

Source: Aschbacher–Smith, Lemma 6.1.5, printed p.666, and E.2.3(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher

namespace CFSG.Quasithin.Chapter6.Source

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W M V H : Subgroup G} {n : ℕ}

namespace RankOneGeneric.Input

/-- E.2.3 gives the original residual containment and whole-H factorization. -/
theorem hstar_thompson_factorization
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    pResidual 2 H ≤ elementaryAbelianMaxJ (⊤ : Subgroup H) ∧
      elementaryAbelianMaxJ (⊤ : Subgroup H) ⊔
        (T.subtype hH.1.1.2 : Subgroup H) = ⊤ := by
  exact ChapterE.ThompsonAction.residual_le_thompson
    (T.subtype hH.1.1.2) (h.hstar_minimal_parabolic hH) _
    (h.hstar_omega_orbit_reduced hH) (h.hstar_thompson_moves_omega_orbit hH hZH)

/-- The proved centralizer conclusion concerns its intersection with the
original Sylow subgroup. -/
theorem hstar_omega_orbit_sylow_centralizer_eq_core
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    (T.subtype hH.1.1.2 : Subgroup H) ⊓ centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H := by
  exact (ChapterE.ThompsonAction.reduced_centralizer_sylow
    (T.subtype hH.1.1.2) (h.hstar_minimal_parabolic hH) _
    (h.hstar_omega_orbit_reduced hH)
    (h.hstar_thompson_moves_omega_orbit hH hZH)).1

end RankOneGeneric.Input

namespace Hypothesis611

variable (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The literal source 6.1.1 specialization, retaining its original `M`. -/
theorem hstar_thompson_factorization
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    pResidual 2 H ≤ elementaryAbelianMaxJ (⊤ : Subgroup H) ∧
      elementaryAbelianMaxJ (⊤ : Subgroup H) ⊔
        (T.subtype hH.1.1.2 : Subgroup H) = ⊤ := by
  exact (h.rankOneInput hout).hstar_thompson_factorization
    (h.maximal_eq_normalizer_L ▸ hH) hZH

/-- Source 6.1.1 supplies the original two-core as `C_T(⟨Z^H⟩)`. -/
theorem hstar_omega_orbit_sylow_centralizer_eq_core
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    (T.subtype hH.1.1.2 : Subgroup H) ⊓ centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H := by
  exact (h.rankOneInput hout).hstar_omega_orbit_sylow_centralizer_eq_core
    (h.maximal_eq_normalizer_L ▸ hH) hZH

end Hypothesis611
end CFSG.Quasithin.Chapter6.Source
