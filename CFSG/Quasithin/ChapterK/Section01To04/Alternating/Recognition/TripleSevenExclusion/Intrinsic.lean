module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSevenExclusion.AssemblyInputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.SevenExclusion.Degree
public import Theory.Alternating.SevenElementaryGeneration

/-!
# Intrinsic exclusion of the genuine triple cover of A₇

Generating conjugates of an elementary subgroup in A₇ lift through the actual
odd central covering map. Their fixed spaces force a faithful irreducible
binary module with cubic ratio at most two to have degree at most eight.
The independent lower bound twelve then gives a contradiction.

The elementary conjugate-generation theorem supplies the full numerical
budget, so the intrinsic exclusion retains no additional representation or
generation hypothesis. `OuterBound` handles the ambient extension separately.

Source: Aschbacher–Smith, K.1, printed p.452/PDF p.463, invoking
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3; the proof uses the
fixed-space method of Guralnick–Malle (2.5)–(2.6).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open GLS3.Chapter5.OddCentralCovers
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion
universe u v

/-- The intrinsic exclusion needs only a concrete conjugate-generation bound in A7. -/
theorem tripleSevenIntrinsicExclusion_of_generation
    (hgen : ElementaryConjugateBudget (alternatingGroup (Fin 7)) 4) :
    RecognitionInputs.TripleSevenIntrinsicExclusion.{v} := by
  intro V _ _ _ τ hf hi hsmall
  let : Nontrivial TripleSeven := tripleSevenProjection_surjective.nontrivial
  have hlow := finrank_ge_twelve τ hf hi
  have hhigh := finrank_le_of_cubicRatio_of_central_cover τ hf hi
    tripleSevenProjection tripleSevenProjection_surjective
    tripleSevenCovering.ker_le_center
    (show Nat.Coprime 2 (Nat.card tripleSevenProjection.ker) from by
      change Nat.Coprime 2 (Nat.card tripleSevenCovering.toMonoidHom.ker)
      rw [tripleSevenCovering_kernel_card]
      decide) hgen hsmall
  norm_num at hhigh
  omega

/-- A faithful irreducible binary module for the genuine triple cover of A₇
cannot have cubic ratio at most two. -/
theorem tripleSevenIntrinsicExclusion :
    RecognitionInputs.TripleSevenIntrinsicExclusion.{v} :=
  tripleSevenIntrinsicExclusion_of_generation
    alternatingGroup.SevenElementaryGeneration.elementaryConjugateBudget

end CFSG.Quasithin.ChapterK.Alternating
