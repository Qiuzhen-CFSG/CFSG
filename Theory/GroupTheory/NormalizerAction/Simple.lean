module
public import Theory.GroupTheory.NormalizerAction.Sylow
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.CComponent.RadicalFree
/-!
# The simple component inside its faithful normalizer action

For a centerless subgroup the literal map to N(K)/C(K) embeds K.
The action sends that copy to Inn(K), whose centralizer is trivial.
When K is simple and perfect, any solvable normal subgroup must centralize
this copy, so the whole normalizer action has trivial solvable radical.

Source application: Aschbacher–Smith E.2.2, reduction of a paired component
to a normal simple component, printed p.216. All maps retain their original
normalizer and centralizer domains.
-/

public section
noncomputable section
open Subgroup
namespace Subgroup.NormalizerAction
variable {H : Type*} [Group H] (K : Subgroup H)

/-- The actual component embedding is injective when its center is trivial. -/
theorem componentMap_injective_of_center_eq_bot (hz : center K = ⊥) :
    Function.Injective (componentMap K) :=
  (MonoidHom.ker_eq_bot_iff _).mp ((componentMap_ker K).trans hz)

/-- The original factor and its literal automizer image have the same coordinates. -/
def componentEquivOfCenterEqBot (hz : center K = ⊥) : K ≃* componentImage K :=
  (MonoidHom.ofInjective (componentMap_injective_of_center_eq_bot K hz)).trans
    (MulEquiv.subgroupCongr (componentMap_range K))

/-- The actual inner image is self-centralizing in the normalizer action. -/
theorem centralizer_componentImage_eq_bot (hz : center K = ⊥) :
    centralizer (componentImage K : Set (Star K)) = ⊥ := by
  apply bot_unique
  intro a ha
  have hac : action K a ∈ centralizer (MulAut.innerSubgroup K : Set (MulAut K)) := by
    rw [← action_map_componentImage K]
    rintro _ ⟨b,hb,rfl⟩
    simpa only [map_mul] using congrArg (action K) (ha b hb)
  rw [MulAut.centralizer_innerSubgroup_eq_bot hz,mem_bot] at hac
  exact mem_bot.mpr ((action_injective K) (hac.trans (map_one (action K)).symm))

/-- The faithful automizer of a centerless simple perfect factor is radical-free. -/
theorem solvableRadical_star_eq_bot [Finite H] [IsSimpleGroup K] [Group.IsPerfect K]
    (hz : center K = ⊥) : solvableRadical (Star K) = ⊥ := by
  let D := componentImage K
  let e := componentEquivOfCenterEqBot K hz
  let : IsSimpleGroup D := e.symm.isSimpleGroup
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hD : D.IsSubnormal := (inferInstance : D.Normal).isSubnormal
  rcases simple_subnormal_normal_dichotomy D (solvableRadical (Star K)) hD with h | h
  · have hs : Group.IsSolvable D :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective h)
    let : Nontrivial D := inferInstance
    exact (Group.IsPerfect.not_isSolvable D hs).elim
  · apply bot_unique
    rw [commutator_comm] at h
    exact (commutator_eq_bot_iff_le_centralizer.mp h).trans (centralizer_componentImage_eq_bot K hz).le
end Subgroup.NormalizerAction
