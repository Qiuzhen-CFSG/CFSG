module

public import Theory.SpecificGroups.ExoticTwoGroup.LocalStructure
public import Theory.ElementaryAbelian.Basic

/-!
# Intrinsic conjugacy coverage for the exotic special core

The elementary sixteens containing the normal four determine the fusion
calculation at the start of Janko--Thompson, Math. Z. 113 (1970), p.396.
The required intrinsic assertion is that every involution in the special
core is conjugate into the normal four or into any commuting disjoint four.
Ambient fusion follows by composing this conjugacy with the supplied
conjugacy between the two fours.

The predicate here only specifies that finite calculation. It does not
assert it from the presentation; its constructor is a separate obligation.
-/

namespace ExoticTwoGroup.Presentation

variable {P : Type*} [Group P]

/-- Every core involution is conjugate into one of two commuting disjoint fours. -/
public def CoreFusionCover (d : ExoticTwoGroup.Presentation P) : Prop :=
  ∀ V : Subgroup P, IsElementaryAbelian 2 V → Nat.card V = 4 →
    Disjoint d.four V → V ≤ Subgroup.centralizer (d.four : Set P) →
    ∀ x : P, x ∈ d.core → orderOf x = 2 →
      ∃ y : P, (y ∈ d.four ∨ y ∈ V) ∧ IsConj x y

/-- Introduce intrinsic coverage from its pointwise defining property. -/
public theorem CoreFusionCover.of_forall {d : ExoticTwoGroup.Presentation P}
    (h : ∀ V : Subgroup P, IsElementaryAbelian 2 V → Nat.card V = 4 →
      Disjoint d.four V → V ≤ Subgroup.centralizer (d.four : Set P) →
      ∀ x : P, x ∈ d.core → orderOf x = 2 →
        ∃ y : P, (y ∈ d.four ∨ y ∈ V) ∧ IsConj x y) : d.CoreFusionCover := h

/-- The displayed central involution belongs to the displayed normal four. -/
public theorem centralInvolution_mem_four (d : ExoticTwoGroup.Presentation P) :
    d.centralInvolution ∈ d.four := by
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

/-- The intrinsic coverage predicate at a chosen commuting four. -/
public theorem CoreFusionCover.apply {d : ExoticTwoGroup.Presentation P}
    (h : d.CoreFusionCover) (V : Subgroup P) [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 4) (hd : Disjoint d.four V)
    (hc : V ≤ Subgroup.centralizer (d.four : Set P))
    (x : P) (hx : x ∈ d.core) (ho : orderOf x = 2) :
    ∃ y : P, (y ∈ d.four ∨ y ∈ V) ∧ IsConj x y :=
  h V inferInstance hV hd hc x hx ho

end ExoticTwoGroup.Presentation
