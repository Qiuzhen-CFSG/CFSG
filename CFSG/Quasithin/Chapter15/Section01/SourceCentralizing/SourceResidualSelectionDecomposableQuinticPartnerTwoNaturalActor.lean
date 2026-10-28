module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionComponentNatural
public import Theory.Representation.BinaryFullLinearRecognition

/-!
# The full actor of a binary natural component

The natural binary special-linear subgroup already contains every linear
automorphism of the whole space, since every binary determinant is one.
Faithfulness therefore forces that subgroup to be the entire actor. The
result retains the original natural coordinates and upgrades the subgroup
marking to a marking of the full group.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.QuasisimpleSource
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]

/-- A faithful actor containing the full binary natural linear group has
no further elements outside that same subgroup. -/
theorem subgroup_eq_top_of_binary_natural
    (σ : Representation (ZMod 2) G W) (hf : Function.Injective σ)
    (L : Subgroup G) (n : ℕ)
    (e : ActionEquiv (σ.comp L.subtype) (linearNatural BinaryField.two n)) : L = ⊤ := by
  let a := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)).trans
    (BinaryLinear.OuterCyclic.slEquivLinear n).symm
  let φ : G →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) := a.toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv e.linearEquiv).toMonoidHom.comp σ.asGroupHom)
  have hφ : Function.Injective φ := by
    apply a.injective.comp
    apply (LinearMap.GeneralLinearGroup.congrLinearEquiv e.linearEquiv).injective.comp
    intro x y h
    exact hf (congrArg Units.val h)
  have hc : Nat.card G ≤ Nat.card L := by
    have hh := Nat.card_le_card_of_injective φ hφ
    exact hh.trans_eq (Nat.card_congr e.groupEquiv.toEquiv).symm
  exact L.eq_top_of_card_eq (Nat.le_antisymm (Nat.card_le_card_of_injective
    L.subtype L.subtype_injective) hc)

/-- The same original natural marking extends to the full faithful actor. -/
theorem whole_actor_natural_of_subgroup
    (σ : Representation (ZMod 2) G W) (hf : Function.Injective σ)
    (L : Subgroup G) (n : ℕ)
    (e : ActionEquiv (σ.comp L.subtype) (linearNatural BinaryField.two n)) :
    Nonempty (ActionEquiv σ (linearNatural BinaryField.two n)) := by
  have hL := subgroup_eq_top_of_binary_natural σ hf L n e
  let j : G ≃* L := {
    toFun := fun g => ⟨g,hL ▸ mem_top g⟩
    invFun := Subtype.val
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  refine ⟨⟨j.trans e.groupEquiv,e.linearEquiv,?_⟩⟩
  intro g w
  exact e.intertwines (j g) w

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
