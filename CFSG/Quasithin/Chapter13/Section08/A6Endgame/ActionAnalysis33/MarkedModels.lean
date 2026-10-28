module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.IntersectionBalance.Models
import all CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.IntersectionBalance.Models

/-!
# Access to the marked alternatives used in the case-one argument

This is an internal API extension of `IntersectionBalance.Models` in the
same package. Its intentional `import all` allows the eliminator to retain
both the action and seed marking of `CompatibleModel`, whose existing
`action_cases` theorem forgets the latter. The definition body and the
existing public interface remain unchanged. The actual case-one cover
exclusion consumes these markings in `SourceCompletion.CaseOne.Cover`.
-/

public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance
open Representation.SixLetterRadicalDisplacement
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G : Type*} [Group G] {H V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Retain the plane marking as well as the whole-module coordinates. -/
theorem CompatibleModel.marked_cases
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e) :
    (∃ F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6),
      (∀ g v, F (tildeRepresentation H _ V₁ a g v) =
        naturalRepresentation (Fin 6) (e g) (F v)) ∧
      (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap = canonicalPlane) ∨
    (∃ F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] U,
      (∀ g v, F (tildeRepresentation H _ V₁ a g v) =
        coreRepresentation (Fin 6) (e g) (F v)) ∧
      (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap = W) := model

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance
