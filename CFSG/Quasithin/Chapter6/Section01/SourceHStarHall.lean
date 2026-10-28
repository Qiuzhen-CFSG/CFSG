module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarE23
public import CFSG.Quasithin.Chapter3.Section01.HStarOmegaCentralizer

/-!
# Hall-faithful H-star centralizers

This is the source-faithful local interface used after the odd Hall action has
been proved faithful on the Sylow omega-center.  It packages the Chapter 3
centralizer lemma on the literal Chapter 6 carriers.  The Hall and
faithfulness hypotheses remain explicit: this module does not assert the
unconditional 6.1.5 conclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}

/-- Direct Chapter 6 interface for the Hall-faithful H-star centralizer. -/
theorem hstar_omega_center_centralizer_eq_sylow_of_hall
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (B : Subgroup H) (hBM : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hfaith : B.map H.subtype ⊓
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥) :
    centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H) := by
  exact Chapter3.HStar.omega_center_centralizer_eq_sylow_of_hall
    hH hZH B hBM hHall hfaith

namespace Hypothesis611

variable (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The same interface for an H-star witness presented over the original
maximal two-local subgroup `M`.  The already proved `M = N_G(L)` identity is
the only transport used here. -/
theorem hstar_omega_center_centralizer_eq_sylow_of_hall
    (_hout : Chapter3.HasMaximalOutside T M)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (B : Subgroup H) (hBM : B ≤ M.subgroupOf H)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes
      (B.subgroupOf (M.subgroupOf H)))
    (hfaith : B.map H.subtype ⊓
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥) :
    centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H) := by
  have hM : M = normalizer (L : Set G) := h.maximal_eq_normalizer_L
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    hM ▸ hH
  apply CFSG.Quasithin.Chapter6.Source.hstar_omega_center_centralizer_eq_sylow_of_hall
    hH' hZH B
  · simpa [hM] using hBM
  · rw [← hM]
    exact hHall
  · exact hfaith

end Hypothesis611
end CFSG.Quasithin.Chapter6.Source
