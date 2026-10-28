module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAlternatingCovers
public import Theory.SpecificGroups.Alternating.EightQuasisimpleQuotient

/-!
# Recovering the original alternating-eight actor

The canonical map from L/O₂(L) to L/C_L(V), followed by the supplied A₈
marking, is surjective. Quasisimplicity and the trivial two-core of L/O₂(L)
make this very map injective by the alternating multiplier bound. Thus the
original quotient action, and then the ambient action on V, have the full
augmentation-core model. Neither simplicity nor equality of the two action
kernels is assumed.

Source: Aschbacher–Smith, 12.2.2(3d), p.795; 12.2.16, p.800,
using I.1.3, p.407.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Recover the original two-core actor, preserving its actual projection. -/
theorem alternatingEight_quotientAction_of_faithfulAction
    (D : ChosenModule T L V) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) :
    Nonempty (ActionEquiv D.quotientAction
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) := by
  let := D.actionCentralizer_normal
  let := hq
  let f := e.groupEquiv.toMonoidHom.comp D.coreToFaithful
  have hf : Function.Surjective f := e.groupEquiv.surjective.comp D.coreToFaithful_surjective
  have hi := AlternatingEightQuasisimple.surjection_injective
    (pCore_quotient_pCore_eq_bot 2) f hf
  let E := MulEquiv.ofBijective f ⟨hi,hf⟩
  refine ⟨⟨E,e.linearEquiv,?_⟩⟩
  intro q v
  have he := e.intertwines (D.coreToFaithful q) v
  change e.linearEquiv ((D.faithfulAction.comp D.coreToFaithful) q v) = _ at he
  rwa [D.faithfulAction_comp_coreToFaithful] at he

/-- The faithful core marking gives the full original ambient conjugation model. -/
theorem alternatingEight_conjugationModel_of_faithfulAction
    (D : ChosenModule T L V) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (e : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (BinaryPermutation.alternatingCoreRepresentation (Fin 8))) :
    Chapter6.Source.IsConjugationModel L V
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)) := by
  obtain ⟨E⟩ := alternatingEight_quotientAction_of_faithfulAction D hq e
  exact D.conjugationModel_of_quotientAction E
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
