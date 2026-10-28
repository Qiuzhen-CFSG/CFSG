module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Components.Conjugator
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Components.Residual
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Components.Endgame

/-!
# Excluding ordinary components in the L₃ hyperplane centralizer

The faithful cubic and its actual lifted normalizer involution construct the
plane U intersect U^l. The original component is the embedded three-residual
of that plane centralizer's ordinary layer. Since the same l normalizes the
plane, it normalizes this residual and hence K. Thus K centralizes U and U^l,
whose join is V, contradicting the original escaping-component conclusion.
No characteristic-two or odd-core case is used.
Source: Aschbacher--Smith 12.4.8, ordinary-component branch, printed p.815.
-/
public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
universe u

/-- The full ordinary-component contradiction, with the model, actor,
conjugator, component comparison and residual equality all constructed. -/
theorem Configuration.component_false
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V U : Subgroup G} (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G))) : False := by
  obtain ⟨x,l,hxL,hx,hxN,hxC,hl,hlX,hm,hsq⟩ := c.exists_component_conjugator
  have hsU : l ^ 2 ∈ normalizer (U : Set G) :=
    Subgroup.centralizer_le_normalizer _ ((centralizer_le c.le_module) hsq)
  have hg := c.conjugate_plane_geometry hl hm hsU
  have ha := c.cubic_on_conjugate_plane hl hm hsU hxL hxN hxC hlX
  have he := c.component_eq_plane_layer_residual hK inf_le_left hg.2.2.1 hx ha.1 ha.2
  exact c.false_of_component_plane_residual hK hl hm hsU he

/-- The ordinary-component case contract consumed by the original 12.4.8
centralizer-bound assembly. -/
theorem ordinaryComponentExclusion : ComponentExclusion.{u} := by
  intro G _ _ T L V U c hcomp
  obtain ⟨K,hK⟩ := hcomp
  exact c.component_false hK
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
