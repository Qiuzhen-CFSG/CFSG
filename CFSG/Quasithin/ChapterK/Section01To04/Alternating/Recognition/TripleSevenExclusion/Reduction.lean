module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSevenExclusion
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition

/-!
# Triple-seven exclusion from elementary subgroup generation in A7

A conjugate-generation budget of four in the actual A7 quotient forces a
faithful irreducible binary triple-cover module of cubic ratio at most two
to have degree at most eight. The proved lower bound twelve excludes it.
The outer restriction theorem gives the ambient exclusion and its actual
application to the K.1 Recognition consumer.

These conditional reductions preserve the explicit finite A7 generation
premise. The imported `tripleSevenExclusion` discharges that premise using
the proved generation theorem; `Source` applies it to Recognition.

Source: Aschbacher--Smith K.1, printed p.452, and the fixed-space method of
Guralnick--Malle, *Classification of 2F-modules I*, (2.5)--(2.6).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open GLS3.Chapter5.OddCentralCovers
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.ComponentRecognition.AlternatingCovers.SevenExclusion
universe u v

/-- The proved outer restriction gives the full ambient exclusion from that same bound. -/
theorem tripleSevenExclusion_of_generation
    (hgen : ElementaryConjugateBudget (alternatingGroup (Fin 7)) 4) :
    RecognitionInputs.TripleSevenExclusion.{u,v} :=
  tripleSevenExclusion_of_intrinsic (tripleSevenIntrinsicExclusion_of_generation hgen)
    tripleSevenRestrictionBound

/-- The actual Recognition consumer with only the A7 group-generation input left in this branch. -/
theorem recognition_of_tripleSeven_generation
    (h6 : RecognitionInputs.SixRecognition.{u,v})
    (h7 : RecognitionInputs.SevenRecognition.{u,v})
    (h36 : RecognitionInputs.TripleSixDegree.{u,v})
    (hgen : ElementaryConjugateBudget (alternatingGroup (Fin 7)) 4)
    {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}
    {L : Subgroup G} (h : Input ρ K L) : RecognizedAction ρ L :=
  recognition_of_branches h6 h7 h36 (tripleSevenExclusion_of_generation hgen) ρ h

end CFSG.Quasithin.ChapterK.Alternating
