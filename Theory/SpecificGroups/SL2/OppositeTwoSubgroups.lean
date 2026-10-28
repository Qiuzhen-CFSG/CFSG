module
public import Theory.SpecificGroups.SL2.FiveGeneratorRecognition

/-!
# Opposite two-subgroups cover a linear quotient

Two two-subgroups of order q, disjoint from the kernel of a map into
SL₂(q) in characteristic two, map to Sylow subgroups. If their images
are distinct and the subgroups generate the domain, the map is onto.
The field may have order two. No finiteness of an ambient completion
or normality of the two generating subgroups is used.

Source application: DGS, *Groups and Graphs* (1985), (14.3)(a), p.212.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]

/-- A root-sized two-subgroup embeds onto a defining-characteristic Sylow. -/
theorem two_subgroup_image_is_sylow
    (f : X →* SL(2,F)) (R : Subgroup X) (hR : IsPGroup 2 R)
    (hcard : Nat.card R = Nat.card F) (hker : R ⊓ f.ker = ⊥) :
    ∃ T : Sylow 2 SL(2,F), (T : Subgroup SL(2,F)) = R.map f := by
  have hi : Function.Injective (f.comp R.subtype) := by
    apply (f.comp R.subtype).ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    exact show (x:X) ∈ (⊥ : Subgroup X) from hker ▸ ⟨x.property,hx⟩
  have hc : Nat.card (R.map f) = Nat.card F := by
    have he : (f.comp R.subtype).range = R.map f := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [←he, ←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    exact hcard
  obtain ⟨T,hT⟩ := (hR.map f).exists_le_sylow
  refine ⟨T,(eq_of_le_of_card_ge hT ?_).symm⟩
  rw [hc, ←Nat.card_congr (sylowEquivAdditive F 2 T).toEquiv]
  rfl

/-- Two distinct full root images generate the entire linear target. -/
theorem surjective_of_opposite_two_subgroups
    (f : X →* SL(2,F)) (R S : Subgroup X)
    (hR : IsPGroup 2 R) (hS : IsPGroup 2 S)
    (hRc : Nat.card R = Nat.card F) (hSc : Nat.card S = Nat.card F)
    (hRk : R ⊓ f.ker = ⊥) (hSk : S ⊓ f.ker = ⊥)
    (hne : R.map f ≠ S.map f) (hgen : R ⊔ S = ⊤) :
    Function.Surjective f := by
  obtain ⟨P,hP⟩ := two_subgroup_image_is_sylow f R hR hRc hRk
  obtain ⟨Q,hQ⟩ := two_subgroup_image_is_sylow f S hS hSc hSk
  have hpq : P ≠ Q := by
    intro he
    exact hne (hP.symm.trans ((congrArg Sylow.toSubgroup he).trans hQ))
  have ht := sylow_sup_eq_top 2 P Q hpq
  rw [hP,hQ,←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map] at ht
  exact MonoidHom.range_eq_top.mp ht

end Matrix.SpecialLinearGroup
