module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.PointAction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.LinearData
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# From the Co₃ fixed-point quotient to the symplectic central quotient

The actual involution, centralizing numerator and surjection onto its 36-point
image have been constructed. This module connects two independent
matrix results: a faithful action agreeing with the three point permutations,
and generation of the full symplectic group by the three displayed matrices.
Together they identify the actual image and give the required surjection onto
PSp₆(2), with no splitting or whole-centralizer assertion.

This comparison interface keeps the matrix premises explicit. The completed
construction in `CentralizerSection.Quotient` discharges them using
`LinearAction` and `LinearGeneration`, retaining this module as their common
comparison layer. Source: GLS3 Table 5.3j and Aschbacher--Smith A.2.19, pp.40--41.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Co3.CentralizerSection

/-- The literal central quotient, definitionally the ATLAS `PSp 3 (ZMod 2)`. -/
abbrev SymplecticQuotient := LinearData.Sp ⧸ Subgroup.center LinearData.Sp

variable (ρ : LinearData.Sp →* Equiv.Perm (Fin 36))
    (hρ : Function.Injective ρ)
    (hvalues : ∀ i, ρ (LinearData.generator i) = Tables.pointGenerator i)
    (hgenerate : Subgroup.closure (Set.range LinearData.generator) = ⊤)

include hvalues hgenerate in
/-- Exact image equality follows from the two actual generating sets. -/
theorem linearAction_range : ρ.range = pointGroup := by
  rw [MonoidHom.range_eq_map, ← hgenerate, MonoidHom.map_closure]
  change Subgroup.closure (ρ '' Set.range LinearData.generator) =
    Subgroup.closure (Set.range Tables.pointGenerator)
  congr 1
  rw [← Set.range_comp]
  exact congrArg Set.range (funext hvalues)

/-- Actual comparison with the full matrix group, conditional on its action and generation. -/
noncomputable def pointGroupEquiv : pointGroup ≃* LinearData.Sp :=
  ((MonoidHom.ofInjective hρ).trans
    (MulEquiv.subgroupCongr (linearAction_range ρ hvalues hgenerate))).symm

/-- The central quotient map does not posit a complement to the double cover. -/
noncomputable def symplecticQuotientMap : numerator →* SymplecticQuotient :=
  (QuotientGroup.mk' (Subgroup.center LinearData.Sp)).comp
    ((pointGroupEquiv ρ hρ hvalues hgenerate).toMonoidHom.comp pointQuotient)

theorem symplecticQuotientMap_surjective :
    Function.Surjective (symplecticQuotientMap ρ hρ hvalues hgenerate) :=
  (QuotientGroup.mk'_surjective _).comp
    ((pointGroupEquiv ρ hρ hvalues hgenerate).surjective.comp pointQuotient_surjective)

end Sporadic.LeechRelated.Co3.CentralizerSection
