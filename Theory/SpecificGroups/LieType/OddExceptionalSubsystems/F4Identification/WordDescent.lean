module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.Words
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.Eigenspaces

/-!
# Descent of marked F4 words through the two folded diagram blocks

The actual folded matrix action splits into its two diagram eigenspaces when
2 is invertible. A representation of the F4 cover on either space that agrees
on every signed simple curve agrees on every word. If both representations
are supplied, an identity word of the cover acts identically on both blocks
and hence on the whole E6 space.

The central-word application additionally needs triviality of the cover's
center. This is not the quotient-center theorem in `OddCenter`. The two
representation constructions and the cover-center theorem remain explicit
premises here; no unconditional word descent or F4 identification is claimed.
The independent adjoint restriction supplies the fixed-space comparison, and
the complementary representation requires a separate construction that must
include characteristic three without assuming irreducibility.

Source: the F4 inclusions in Aschbacher--Smith A.2.17, printed p.39 of
`refs/quasithin.pdf`, and GLS3 §§2.2--2.6 for the actual root-group pinning.
-/

public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification
open WordDescent

variable (F : Type*) [Field F]

/-- Agreement on the literal signed simple curves extends to the whole word group. -/
theorem eigenspaceAction_evaluation_of_simple (a : F)
    (ρ : Cover F →* (eigenspace F a ≃ₗ[F] eigenspace F a))
    (hsimple : ∀ (s : Bool) (i : Fin 4) (t : F),
      ρ (coverSimple F s i t) = eigenspaceAction F a (f4Simple F s i t))
    (w : Word F) :
    ρ (coverEvaluation F w) = eigenspaceAction F a (foldedEvaluation F w) := by
  have he : ρ.comp (coverEvaluation F) =
      (eigenspaceAction F a).comp (foldedEvaluation F) := by
    apply FreeGroup.ext_hom
    rintro ⟨s, i, t⟩
    simpa only [MonoidHom.comp_apply, coverEvaluation_of, foldedEvaluation_of] using
      hsimple s i t
  exact DFunLike.congr_fun he w

/-- Actual block representations suffice for identity-word descent. Their marked
generator equations retain both signs, the reversed node order, and the parameter. -/
theorem foldedEvaluation_eq_one_of_blockRepresentations (htwo : (2 : F) ≠ 0)
    (ρfixed : Cover F →* (fixedSpace F ≃ₗ[F] fixedSpace F))
    (ρcomplement : Cover F →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hfixed : ∀ (s : Bool) (i : Fin 4) (t : F),
      ρfixed (coverSimple F s i t) = eigenspaceAction F 1 (f4Simple F s i t))
    (hcomplement : ∀ (s : Bool) (i : Fin 4) (t : F),
      ρcomplement (coverSimple F s i t) = eigenspaceAction F (-1) (f4Simple F s i t))
    (w : Word F) (hw : coverEvaluation F w = 1) : foldedEvaluation F w = 1 := by
  apply eq_one_of_eigenspaceActions F htwo
  · rw [← eigenspaceAction_evaluation_of_simple F 1 ρfixed hfixed, hw, map_one]
  · rw [← eigenspaceAction_evaluation_of_simple F (-1) ρcomplement hcomplement,
      hw, map_one]

/-- The exact central-word contract, conditional on the two genuine block
representations and triviality of the *cover's* center. These premises still
have to be proved before applying the parent identification assembly. -/
theorem foldedEvaluation_eq_one_of_central_of_blockRepresentations
    (htwo : (2 : F) ≠ 0) (hcenter : Subgroup.center (Cover F) = ⊥)
    (ρfixed : Cover F →* (fixedSpace F ≃ₗ[F] fixedSpace F))
    (ρcomplement : Cover F →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hfixed : ∀ (s : Bool) (i : Fin 4) (t : F),
      ρfixed (coverSimple F s i t) = eigenspaceAction F 1 (f4Simple F s i t))
    (hcomplement : ∀ (s : Bool) (i : Fin 4) (t : F),
      ρcomplement (coverSimple F s i t) = eigenspaceAction F (-1) (f4Simple F s i t))
    (w : Word F) (hw : coverEvaluation F w ∈ Subgroup.center (Cover F)) :
    foldedEvaluation F w = 1 := by
  rw [hcenter, Subgroup.mem_bot] at hw
  exact foldedEvaluation_eq_one_of_blockRepresentations F htwo
    ρfixed ρcomplement hfixed hcomplement w hw

end TwistedE6.FoldedSubsystem.F4Identification
