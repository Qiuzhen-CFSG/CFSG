module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension
public import Theory.SpecificGroups.ProjectiveLinear.FourTwoPGroupBound

/-!
# The actual L₄(2) order obstruction in 14.4.13

Recognition identifies the generated subgroup G₀ with L₄(2). A two-subgroup
T contained in G₀ has order at most 64, contradicting U ≤ T and |U| > 512.
The first two lemmas apply to the literal subgroup G₀ inside the ambient G;
they require no assertion G₀ = G. The final lemma discharges the numerical
premise of the existing A₃ assembly after its configuration has been
restricted to the group to which I.5.1 applies.

The source constructions of that configuration and its core-free condition
remain required. See Aschbacher--Smith, *The Classification of Quasithin
Groups*, §14.4, printed p. 1012.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension

universe u

variable {G : Type u} [Group G] [Finite G]

/-- Recognition of the actual overgroup supplies the concrete two-subgroup bound. -/
theorem l4TwoSylowBound_of_recognized_overgroup
    {T G₀ : Subgroup G} (hT : IsPGroup 2 T) (hTG₀ : T ≤ G₀)
    (e : G₀ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :
    L4TwoSylowBound T := by
  exact ⟨Matrix.PSL4Two.card_twoGroup_le_sixtyFour hT
    (e.toMonoidHom.comp (Subgroup.inclusion hTG₀))
    (e.injective.comp (Subgroup.inclusion_injective hTG₀))⟩

/-- The numerical contradiction in 14.4.13 takes place inside G₀. -/
theorem no_large_two_subgroup_of_recognized_overgroup
    {U T G₀ : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T) (hTG₀ : T ≤ G₀)
    (hU : 512 < Nat.card U)
    (e : G₀ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) : False := by
  exact no_large_two_group_of_L4_bound hU
    (Nat.card_le_card_of_injective (Subgroup.inclusion hUT)
      (Subgroup.inclusion_injective hUT))
    (l4TwoSylowBound_of_recognized_overgroup hT hTG₀ e).card_le

/-- The existing A₃ assembly needs no independent model-order premise. -/
theorem large_dimension_elimination_of_recognition
    {L T L₁ L₂ X M : Subgroup G}
    (hA3 : A3AssemblyInput L T L₁ L₂ X M)
    (U : Subgroup G) (hU : 512 < Nat.card U)
    (hUT : Nat.card U ≤ Nat.card T)
    (recognition : ∀ (K : Type u) [Group K] [Finite K],
      Quasithin.I5.DSystem .A3 K →
        Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :
    False := by
  have hT : IsPGroup 2 T := by
    have h := hA3.toDSystem.T_isTwoGroup
    change IsPGroup 2 (Quasithin.I5.chamberSubgroup
      (![L ⊔ T, L₁ ⊔ X ⊔ T, localJoin L₂ X ⊔ T])) at h
    rwa [hA3.chamber_eq] at h
  apply large_dimension_elimination hA3 U hU hUT recognition
  intro e
  exact ⟨Matrix.PSL4Two.card_twoGroup_le_sixtyFour hT
    (e.toMonoidHom.comp T.subtype) (e.injective.comp Subtype.val_injective)⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension
