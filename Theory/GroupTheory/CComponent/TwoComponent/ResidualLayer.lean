module

public import Theory.GroupTheory.CComponent.TwoComponent.Involution

/-!
# Two-components in groups with reductive solvable residual

A C-component contained in the ordinary layer is an ordinary component.
Indeed, unless it equals one of the components generating that layer, the
component dichotomy makes every generator centralize it, contradicting its
nontrivial perfectness. Consequently a solvable residual contained in the
ordinary layer suffices to make all C-components quasisimple.

For involution fixed groups this gives a second route to B₂, alongside a
trivial odd core. The alternatives below are structural inputs, not an
assertion that any particular family satisfies them. They isolate the
finite centralizer calculations needed from GLS III §§3.1, 4.2, 4.5 and 4.9
for GLS II, Definition 2.4 and Lemma 5.28.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace Subgroup.IsCComponent
variable {G : Type*} [Group G] {L : Subgroup G}

/-- A minimal perfect subnormal subgroup inside E(G) is an ordinary component. -/
theorem isComponent_of_le_componentLayer (hL : L.IsCComponent)
    (hle : L ≤ componentLayer G) : IsComponent G L := by
  classical
  by_contra hnot
  have hc : componentLayer G ≤ centralizer (L : Set G) := by
    apply sSup_le
    intro K hK
    rcases hK.subnormal_dichotomy L hL.subnormal with h | h
    · have he := hK.isCComponent.eq_of_le hL h
      exact (hnot (he ▸ hK)).elim
    · exact commutator_eq_bot_iff_le_centralizer.mp h
  let := hL.perfect
  have he : ⁅L, L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hle.trans hc)
  exact hL.ne_bot ((commutator_eq_self (H := L)).symm.trans he)

/-- The terminal derived subgroup controls every C-component. -/
theorem isComponent_of_solvableResidual_le_componentLayer (hL : L.IsCComponent)
    (hG : solvableResidual G ≤ componentLayer G) : IsComponent G L := by
  let := hL.perfect
  exact hL.isComponent_of_le_componentLayer
    ((le_solvableResidual_of_isPerfect L).trans hG)

end Subgroup.IsCComponent

namespace Theory.GroupTheory

/-- Two structural alternatives used in finite involution centralizers.
The second retains solvable small Lie factors and noncentral solvable radicals. -/
def FixedGroupLayerAlternative (G : Type*) [Group G] : Prop :=
  pPrimeCore 2 G = ⊥ ∨ solvableResidual G ≤ componentLayer G

namespace FixedGroupLayerAlternative
variable {G : Type*} [Group G] [Finite G]

/-- Neither alternative assumes that the given two-component is ordinary. -/
theorem isQuasisimple (hG : FixedGroupLayerAlternative G)
    {L : Subgroup G} (hL : L.IsTwoComponent) : IsQuasisimple L := by
  rcases hG with h | h
  · exact (hL.isComponent_of_oddCore_eq_bot h).2
  · exact (hL.1.isComponent_of_solvableResidual_le_componentLayer h).2

end FixedGroupLayerAlternative

/-- Apply the structural calculation at every actual involution fixed subgroup. -/
theorem HasInvolutoryB2.of_fixedGroupLayerAlternative
    {G : Type*} [Group G] [Finite G]
    (h : ∀ a : MulAut G, orderOf a = 2 → FixedGroupLayerAlternative a.fixedSubgroup) :
    HasInvolutoryB2 G := by
  intro a ha L hL
  exact (h a ha).isQuasisimple hL

end Theory.GroupTheory
