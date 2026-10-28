module

public import Theory.Alternating.Theorem523A6

/-!
# Lifted Suzuki generators for the marked alternating-six presentation

Four marked lifts satisfying Suzuki's defining relators induce a homomorphism
from the presented group. Its values are marked against the canonical
projection to `A₆`. The theorem deliberately stops at the presentation:
identifying the presented group with `A₆` requires the reverse normal-closure
theorem, which is a separate source obligation.
-/

public noncomputable section
namespace Representation.BinaryAlternatingSixExtensions

private noncomputable def liftHom {E : Type*} [Group E]
    (lift : Fin 4 → E)
    (hrel : ∀ r : GLS3.Chapter5.SchurPresentation.SuzukiRelator 1,
      FreeGroup.lift lift r.word = 1) :
    GLS3.Chapter5.SchurPresentation.SuzukiPresentedGroup 1 →* E :=
  PresentedGroup.toGroup
    (fun r hr => by
      obtain ⟨s, rfl⟩ := hr
      exact hrel s)

/-- Four marked Suzuki lifts satisfying all defining relators induce a
homomorphism from the finite Suzuki presentation. -/
theorem exists_marked_suzuki_presentation_lift
    {E : Type*} [Group E] (q : E →* alternatingGroup (Fin 6)) (lift : Fin 4 → E)
    (hvalues : ∀ i, q (lift i) =
      GLS3.Chapter5.SchurPresentation.alternatingSuzukiGenerator 1 i)
    (hrel : ∀ r : GLS3.Chapter5.SchurPresentation.SuzukiRelator 1,
      FreeGroup.lift lift r.word = 1) :
    ∃ s : GLS3.Chapter5.SchurPresentation.SuzukiPresentedGroup 1 →* E,
      q.comp s = GLS3.Chapter5.SchurPresentation.suzukiPresentedProjection 1 ∧
      ∀ i, s (PresentedGroup.of i) = lift i := by
  let s := liftHom lift hrel
  refine ⟨s, ?_, ?_⟩
  · apply PresentedGroup.ext
    intro i
    rw [MonoidHom.comp_apply]
    dsimp [s, liftHom]
    rw [PresentedGroup.toGroup.of]
    simpa only [GLS3.Chapter5.SchurPresentation.suzukiPresentedProjection_of] using
      hvalues i
  · intro i
    simp only [s, liftHom, PresentedGroup.toGroup.of]

/-- If the canonical Suzuki projection is injective, the presentation-level
lift descends to an actual marked section of `A₆`. The injectivity input is
kept explicit because it is exactly the unresolved reverse normal-closure
step for the Suzuki relator family. -/
theorem exists_marked_alternating_six_section_of_projection_injective
    {E : Type*} [Group E] (q : E →* alternatingGroup (Fin 6)) (lift : Fin 4 → E)
    (hvalues : ∀ i, q (lift i) =
      GLS3.Chapter5.SchurPresentation.alternatingSuzukiGenerator 1 i)
    (hrel : ∀ r : GLS3.Chapter5.SchurPresentation.SuzukiRelator 1,
      FreeGroup.lift lift r.word = 1)
    (hproj : Function.Injective
      (GLS3.Chapter5.SchurPresentation.suzukiPresentedProjection 1)) :
    ∃ s : alternatingGroup (Fin 6) →* E, q.comp s = MonoidHom.id _ := by
  obtain ⟨s, hs, _⟩ := exists_marked_suzuki_presentation_lift q lift hvalues hrel
  let p := GLS3.Chapter5.SchurPresentation.suzukiPresentedProjection 1
  let e : GLS3.Chapter5.SchurPresentation.SuzukiPresentedGroup 1 ≃*
      alternatingGroup (Fin 6) := MulEquiv.ofBijective p
    ⟨hproj, GLS3.Chapter5.SchurPresentation.suzukiPresentedProjection_surjective 1⟩
  refine ⟨s.comp e.symm.toMonoidHom, ?_⟩
  rw [← MonoidHom.comp_assoc, hs]
  apply MonoidHom.ext
  intro x
  exact e.apply_symm_apply x

end Representation.BinaryAlternatingSixExtensions
