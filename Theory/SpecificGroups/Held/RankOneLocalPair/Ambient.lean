module

public import Theory.SpecificGroups.Held.Model.Perfect
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The actual automorphism overgroup attached to a Held component

For finite G with F*(G) simple and equivalent to Held, the generalized
Fitting centralizer theorem puts C_G(F*(G)) inside its center. Perfectness
of the concrete Held carrier excludes an abelian simple component, so this
center is trivial. Transported conjugation therefore gives a faithful
action whose range contains the whole inner automorphism group.

The range equivalence retains the component and the source relation
G = F*(G)T. No automorphism realization, splitting or identification of G
with He or He:2 is assumed. Concrete local construction in this range is
a separate obligation.

Source: Aschbacher--Smith E.1.14, printed p.214; the generalized Fitting
centralizer theorem and the checked Held presentation relations.
-/

@[expose] public section

namespace Held.RankOneLocalPair
open Subgroup

open Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- The genuine generalized Fitting subgroup has trivial centralizer in the Held case. -/
theorem fitting_centralizer_eq_bot [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* He) :
    centralizer (generalizedFitting G : Set G) = ⊥ := by
  let L := generalizedFitting G
  have : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L) inferInstance with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp h)).elim
  apply bot_unique
  intro c hc
  let l : L := ⟨c, centralizer_generalizedFitting_le G hc⟩
  have hl : l ∈ center L := by
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (hc x x.property)
  have heq : l = 1 := by simpa only [hz, mem_bot] using hl
  exact congrArg Subtype.val heq

/-- Conjugation on F*(G), transported along the given Held equivalence. -/
noncomputable def ambientAction (e : generalizedFitting G ≃* He) : G →* MulAut He :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := generalizedFitting G))

/-- Self-centralization of F*(G) makes this actual action faithful. -/
theorem ambientAction_injective [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* He) : Function.Injective (ambientAction e) :=
  (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot _ (fitting_centralizer_eq_bot e))

/-- The restriction to F*(G) is the literal inner action in the Held coordinates. -/
theorem ambientAction_inner (e : generalizedFitting G ≃* He) (x : generalizedFitting G) :
    ambientAction e x = MulAut.conj (e x) := by
  change MulAut.congr e (MulAut.conjNormal (x : G)) = _
  rw [MulAut.conjNormal_val, MulAut.congr_conj]

/-- The full component maps onto Inn(He), not merely into an abstract simple subgroup. -/
theorem ambientAction_map_fitting (e : generalizedFitting G ≃* He) :
    (generalizedFitting G).map (ambientAction e) = MulAut.innerSubgroup He := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e ⟨x, hx⟩, (ambientAction_inner e ⟨x, hx⟩).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨e.symm x, (e.symm x).property, ?_⟩
    rw [ambientAction_inner, e.apply_symm_apply]

/-- The faithful ambient image contains every inner automorphism. -/
theorem inner_le_ambientAction_range (e : generalizedFitting G ≃* He) :
    MulAut.innerSubgroup He ≤ (ambientAction e).range := by
  rw [← ambientAction_map_fitting e]
  exact map_le_range _ _

/-- The original group is equivalent to the actual range of its conjugation action. -/
noncomputable def ambientEquiv [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* He) : G ≃* (ambientAction e).range :=
  MonoidHom.ofInjective (ambientAction_injective e)

/-- Inside that range, the component is precisely the relative inner subgroup. -/
theorem ambientEquiv_map_fitting [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* He) :
    (generalizedFitting G).map (ambientEquiv e).toMonoidHom =
      (MulAut.innerSubgroup He).subgroupOf (ambientAction e).range := by
  apply map_injective (ambientAction e).range.subtype_injective
  rw [map_subgroupOf_eq_of_le (inner_le_ambientAction_range e), map_map]
  exact ambientAction_map_fitting e

/-- The source relation G = F*(G)T survives in the actual automorphism overgroup. -/
theorem ambientEquiv_sylow_join [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* He) (T : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    (MulAut.innerSubgroup He).subgroupOf (ambientAction e).range ⊔
      (T : Subgroup G).map (ambientEquiv e).toMonoidHom = ⊤ := by
  rw [← ambientEquiv_map_fitting e, ← Subgroup.map_sup, hgen]
  exact map_top_of_surjective (ambientEquiv e).toMonoidHom (ambientEquiv e).surjective

end Held.RankOneLocalPair
