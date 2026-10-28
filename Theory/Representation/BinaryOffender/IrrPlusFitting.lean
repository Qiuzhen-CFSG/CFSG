module
public import Theory.Representation.BinaryOffender.Homogeneous.Core
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleOddActor
public import Theory.GroupAction.Quotient

/-!
# Generalized Fitting subgroups of faithful Irr⁺ actions

For a normal semisimple or odd-prime actor, A.1.41 makes the two-core
fix a faithful Irr⁺ module. The actor is therefore exactly F* when its
quotient is a two-group. Applying this to the literal stabilizer image
also handles a seed that is not invariant under the whole group.

Source: Aschbacher–Smith, A.1.41 and D.3.4(5), pp.31 and 194.
-/

public section
open Subgroup Theory.GroupTheory
open Representation.BinaryOffender.Homogeneous
namespace Representation.BinaryOffender
theorem generalizedFitting_eq_of_faithful_irrPlus
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (X : Subgroup G) [X.Normal] (hf : Function.Injective ρ)
    (hi : IsIrrPlus ρ X ⊤)
    (hshape : componentLayer X = ⊤ ∨ ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p X)
    (hq : IsPGroup 2 (G ⧸ X)) : generalizedFitting G = X := by
  have hc : pCore 2 G = ⊥ := by
    have hfix := IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes ρ hi
      pCore_isPGroup (twoCore_centralizes_of_normal_layer_or_odd X hshape)
      (le_subspaceStabilizer ρ ⊤ (fun _ _ _ _ => Submodule.mem_top))
    apply bot_unique
    intro g hg
    apply mem_bot.mpr
    apply hf
    ext v
    simpa only [map_one, Module.End.one_apply, MonoidHom.comp_apply, Subgroup.subtype_apply] using hfix Submodule.mem_top ⟨g, hg⟩
  exact generalizedFitting_eq_of_le_two_quotient X (normal_layer_or_odd_le_generalizedFitting X hshape) hq hc


end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem seed_image_fitting_of_shape
    (X : Subgroup G) [X.Normal] (I : Submodule (ZMod 2) V)
    (hi : IsIrrPlus ρ X I)
    (hshape : componentLayer (restrictedSubgroup ρ I X) = ⊤ ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p (restrictedSubgroup ρ I X))
    (hp : IsPGroup 2 (G ⧸ X)) :
    generalizedFitting (subspaceActionImage ρ I) = restrictedSubgroup ρ I X := by
  let A := subspaceStabilizer ρ I
  let L := subspaceActionImage ρ I
  let f : A →* L := subspaceActionHom ρ I
  have hf : Function.Surjective f :=
    (stabilizerRepresentation ρ I).asGroupHom.rangeRestrict_surjective
  let : Finite L := Finite.of_surjective f hf
  let Xbar := restrictedSubgroup ρ I X
  let : Xbar.Normal := Normal.map inferInstance f hf
  have hXI : X ≤ A := hi.choose
  refine generalizedFitting_eq_of_faithful_irrPlus (subspaceImageRepresentation ρ I)
    Xbar (subspaceImageRepresentation_injective ρ I) ?_ hshape ?_
  · simpa only [Submodule.comap_subtype_self] using hi.restricted ρ hXI le_rfl
  · have hpA : IsPGroup 2 (A ⧸ X.subgroupOf A) :=
      (hp.to_subgroup (A.map (QuotientGroup.mk' X))).of_equiv
        (quotientSubgroupRangeEquiv A X).symm
    have hx : X.subgroupOf A ≤ Xbar.comap f := fun x hx => mem_map_of_mem f hx
    let f' := QuotientGroup.map (X.subgroupOf A) Xbar f hx
    have hf' : Function.Surjective f' := QuotientGroup.map_surjective_of_surjective _ _ f
      ((QuotientGroup.mk'_surjective Xbar).comp hf) hx
    exact hpA.of_surjective f' hf'
end Representation.BinaryOffender
