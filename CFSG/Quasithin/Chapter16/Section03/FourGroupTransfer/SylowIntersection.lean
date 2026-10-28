module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import Theory.GroupTheory.SylowCenterCardinalityBound

/-!
# The Sylow-center obstruction in 16.3.4

Relative normality from 16.2.4 makes T normalize C_T(L). The independent
Sylow-center bound then contradicts the strict order inequality supplied by
the actual model calculation. The five model calculations remain separate
obligations; this module proves the common elimination argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.4, printed p.1178 / PDF p.1195.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {z t i : G} {L K : Subgroup G}

/-- Normalizing L makes T normalize its actual centralizer intersection T_C. -/
theorem sylow_normalizes_commutingSylow
    (hn : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer (commutingSylow T L : Set G) :=
  (le_inf (T : Subgroup G).le_normalizer
    (hn.trans (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf

variable [Finite G]

/-- The geometric data in the model calculation are incompatible with the
relative normality output of 16.2.4. -/
theorem no_excludedSylowGeometry (h : CentralComponentSetup T z L)
    (hn : (L.subgroupOf (involutionCentralizer z)).Normal)
    (hgeometry : ExcludedSylowGeometry T L K) : False := by
  obtain ⟨V, R, hTV, hd, ⟨S, hS⟩, hcenter, hcard⟩ := hgeometry
  have hR : IsPGroup 2 R := hS ▸ S.isPGroup'.map K.subtype
  have hbound := sylow_center_card_bound T (commutingSylow T L) V R
    inf_le_left (sylow_normalizes_commutingSylow (h.sylow_le_normalizer_of_normal hn))
    hTV hd hR hcenter
  exact (not_lt_of_ge hbound) hcard

/-- The common argument of 16.3.4, conditional on the genuine model geometry.
The earlier tables and the construction of V and its Sylow center are not
proved by this conditional theorem. -/
theorem not_excludedSimple_of_geometry (h : ExclusionSetup T z L K t i)
    (models : IsExcludedSimple K → ExcludedSylowGeometry T L K) :
    ¬ IsExcludedSimple K := fun hK =>
  no_excludedSylowGeometry h.localSetup h.normal (models hK)

end CFSG.Quasithin.Chapter16.FourGroupTransfer
