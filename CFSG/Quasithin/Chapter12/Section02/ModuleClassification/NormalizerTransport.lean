module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.ActorComparison
public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# Full normalizers of the same literal action image

A surjective change of actors leaves the actual linear image unchanged.
Consequently the full-normalizer FF witness for the original component
action is precisely the witness used by the offender-supplement construction.
Source: Aschbacher--Smith B.1.11--13 and 12.2.2, pp.72--73,795.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification
variable {A B W : Type*} [Group A] [Group B] [AddCommGroup W] [Module (ZMod 2) W]

theorem normalizer_ff_iff_of_surjective
    (ρ : Representation (ZMod 2) A W) (σ : Representation (ZMod 2) B W)
    (f : A →* B) (hf : Function.Surjective f) (he : ∀ a, σ (f a) = ρ a) :
    IsFFModule (normalizerRepresentation ρ) ↔ IsFFModule (normalizerRepresentation σ) := by
  have hi : actionImage ρ = actionImage σ := by
    ext u
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨f a,Units.ext (he a)⟩
    · rintro ⟨b,rfl⟩
      obtain ⟨a,rfl⟩ := hf b
      exact ⟨a,Units.ext (he a).symm⟩
  unfold normalizerRepresentation linearNormalizer
  rw [hi]

end CFSG.Quasithin.Chapter12.Section02.ModuleClassification

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

omit [Finite G] in
theorem chosen_normalizer_ff_iff_seedComponent :
    IsFFModule (normalizerRepresentation D.chosenAction) ↔
      IsFFModule (normalizerRepresentation (D.seedRepresentation.comp D.componentImage.subtype)) :=
  ModuleClassification.normalizer_ff_iff_of_surjective _ _ D.componentHom
    D.componentHom_surjective D.componentHom_action

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
