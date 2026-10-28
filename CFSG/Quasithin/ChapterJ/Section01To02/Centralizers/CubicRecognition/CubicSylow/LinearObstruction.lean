module

public import Theory.SpecificGroups.LinearThreeTernary.NoOrder208
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.Basic

/-!
# The linear obstruction in the elementary-abelian cubic branch

For the actual ambient image of a Sylow three-subgroup of N_G(B), the
quotient of its ambient normalizer by that image cannot have order 208,
or order divisible by five, if it acts faithfully on a ternary three-space.
The homomorphism below is from this literal quotient into its actual linear
automorphism group. Construction and faithfulness of the action, and the
orbit argument forcing order 208, remain with the cubic Sylow assembly.

Source: Aschbacher–Smith, final paragraph of J.2.7, printed p.437 (PDF p.448).
-/

public section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The source normalizer quotient has no factor five under its faithful
three-dimensional action. This supplies the order restriction for the
point-orbit calculation in J.2.7. -/
theorem normalizerQuotient_not_five_dvd_card (R : Sylow 3 c.NB)
    (f : (Subgroup.normalizer (ambient c R : Set G)) ⧸
      (ambient c R).subgroupOf (Subgroup.normalizer (ambient c R : Set G)) →*
        ((Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)))
    (hf : Function.Injective f) :
    ¬ 5 ∣ Nat.card ((Subgroup.normalizer (ambient c R : Set G)) ⧸
      (ambient c R).subgroupOf (Subgroup.normalizer (ambient c R : Set G))) :=
  LinearThreeTernary.not_five_dvd_card_of_injective f hf

/-- The quotient order forced by the source orbit calculation is incompatible
with the faithful action on E₂₇. -/
theorem normalizerQuotient_card_ne_208 (R : Sylow 3 c.NB)
    (f : (Subgroup.normalizer (ambient c R : Set G)) ⧸
      (ambient c R).subgroupOf (Subgroup.normalizer (ambient c R : Set G)) →*
        ((Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)))
    (hf : Function.Injective f) :
    Nat.card ((Subgroup.normalizer (ambient c R : Set G)) ⧸
      (ambient c R).subgroupOf (Subgroup.normalizer (ambient c R : Set G))) ≠ 16 * 13 :=
  LinearThreeTernary.card_ne_208_of_injective f hf

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
