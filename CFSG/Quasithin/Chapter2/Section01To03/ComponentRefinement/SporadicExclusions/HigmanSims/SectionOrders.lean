module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HigmanSims.Reduction
public import Theory.GroupTheory.GeneralizedFitting.DirectPowerComponents
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# The subnormal-section obstruction for the HS local calculation

In a direct power of the actual binary matrix group SL₃(2), every quasisimple
subnormal subgroup is isomorphic to one coordinate factor and has order 168.
Every nontrivial subnormal subgroup has order divisible by 168, so none has
order three. These facts discharge the section-order premise of `Reduction`.
The short-block quotient alternatives then exclude every χ₀ block in the
specified local section, including in nonsplit extensions with a two-core.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526. The model-specific local
geometry is still required: this module does not construct the HS normalizer
or assert the unconditional block cover. Simplicity of SL₃(2) is imported from
the attributed ATLAS port, through its actual matrix carrier.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims
open Subgroup Theory.GroupTheory

/-- The direct-power section calculation, with no further model hypotheses. -/
theorem linearThreeSectionOrders : LinearThreeSectionOrders := by
  intro n I hI
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  constructor
  · intro hq
    obtain ⟨e⟩ := (show IsComponent _ I from ⟨hI, hq⟩).equiv_factor_of_directPower
      Atlas.Comparisons.Exceptional.sl3Two_center_eq_bot
    exact (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_SL
  · intro h3
    have hne : I ≠ ⊥ := by
      intro he
      rw [he, Subgroup.card_bot] at h3
      contradiction
    have hd := I.card_dvd_of_isSubnormal_directPower hI hne
    rw [Matrix.PSL3Two.card_SL, h3] at hd
    norm_num at hd

/-- Only the actual HS local geometry remains to be constructed. The
subnormal-section and χ₀-block calculations are discharged here. -/
noncomputable def centralizerBlockCover_of_geometry
    {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .hs)
    (g : LocalGeometry ((S : Subgroup H).map H.subtype) d) :
    CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z :=
  centralizerBlockCover_of_localGeometry h d g linearThreeSectionOrders

end CFSG.Quasithin.Chapter2.ComponentRefinement.HigmanSims
