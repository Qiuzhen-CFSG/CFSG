module

public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The literal wreath action of a marked normal A₄ pair

Conjugation on the original normal subgroup is transported through its
specified A₄² marking and the proved full automorphism equivalence. The
resulting homomorphism retains the original kernel, inner-subgroup image,
and the precise images of conjugate subgroups. This connects the actual
source block orbit to the finite wreath-product calculations.

Source: Aschbacher--Smith 14.1.10, printed p.978.
-/

@[expose] public section
open Subgroup
namespace AlternatingFourPair
variable {G : Type*} [Group G]

/-- The action on the original normal pair, in the literal wreath coordinates. -/
noncomputable def normalPairAction (N : Subgroup G) [N.Normal] (e : N ≃* Model) : G →* W :=
  pairAutEquiv'.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)

theorem normalPairAction_injective (N : Subgroup G) [N.Normal] (e : N ≃* Model)
    (hc : centralizer (N : Set G) = ⊥) : Function.Injective (normalPairAction N e) :=
  pairAutEquiv'.injective.comp ((MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot N hc))

/-- The original normal subgroup maps onto the marked inner automorphisms. -/
theorem normalPairAction_map_self (N : Subgroup G) [N.Normal] (e : N ≃* Model) :
    N.map (normalPairAction N e) =
      (MulAut.innerSubgroup Model).map pairAutEquiv'.toMonoidHom := by
  have hm : N.map (MulAut.conjNormal : G →* MulAut N) = MulAut.innerSubgroup N := by
    ext a
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,MulAut.conjNormal_val.symm⟩
    · rintro ⟨x,rfl⟩
      exact ⟨x,x.property,MulAut.conjNormal_val⟩
  rw [normalPairAction,←map_map,←map_map,hm,MulAut.map_innerSubgroup_congr]

/-- Pointwise compatibility uses the same element of the original ambient group. -/
theorem normalPairAction_apply (N : Subgroup G) [N.Normal] (e : N ≃* Model)
    (g : G) (x : N) :
    wreathAut (normalPairAction N e g) (e x) = e (MulAut.conjNormal g x) := by
  have h : wreathAut (normalPairAction N e g) = (MulAut.congr e) (MulAut.conjNormal g) :=
    pairAutEquiv.apply_symm_apply _
  rw [h]
  change e (MulAut.conjNormal g (e.symm (e x))) = _
  rw [e.symm_apply_apply]

/-- The marking carries the conjugate of the original subgroup to the actual wreath image. -/
theorem normalPairAction_map_conjugate (N X : Subgroup G) [N.Normal]
    (hXN : X ≤ N) (e : N ≃* Model) (g : G) :
    ((X.subgroupOf N).map e.toMonoidHom).map
        (wreathAut (normalPairAction N e g)).toMonoidHom =
      ((X.map (MulAut.conj g).toMonoidHom).subgroupOf N).map e.toMonoidHom := by
  apply le_antisymm
  · rintro y ⟨v,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨MulAut.conjNormal g x,?_,?_⟩
    · exact ⟨x,hx,rfl⟩
    · exact (normalPairAction_apply N e g x).symm
  · rintro y ⟨v,hv,rfl⟩
    obtain ⟨x,hx,hgx⟩ := hv
    let xN : N := ⟨x,hXN hx⟩
    have hg : MulAut.conjNormal g xN = v := Subtype.ext hgx
    refine ⟨e xN,⟨xN,hx,rfl⟩,?_⟩
    exact (normalPairAction_apply N e g xN).trans (congrArg e hg)

end AlternatingFourPair
