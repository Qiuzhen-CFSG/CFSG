module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Branches
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Hexacode

/-!
# Assembling the representation recognition in K.1

The actual central-cover reduction has four branches. The two ordinary
alternating branches supply their module and ambient-action identifications.
For the triple six branch, the degree-six input feeds the proved intrinsic
hexacode recognition and marked extension theorem. The remaining triple
seven branch requires an exclusion at cubic ratio two.

The branch inputs below are explicit unfinished source obligations; this
conditional assembly does not assert the missing GM02 representation results.
The unconditional `recognition` theorem is reserved for their final discharge.

Source: Aschbacher–Smith, K.1–K.1.3, printed pp.452–453.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Alternating
open RecognitionInputs

universe u v

/-- Exhaust the genuine cover alternatives and construct the corresponding
action witnesses. All remaining source classifications are explicit premises. -/
theorem recognition_of_branches
    (h6 : SixRecognition.{u,v}) (h7 : SevenRecognition.{u,v})
    (h36 : TripleSixDegree.{u,v}) (h37 : TripleSevenExclusion.{u,v})
    {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {L : Subgroup G}
    (h : Input ρ K L) : RecognizedAction ρ L := by
  rcases h.cover_alternatives with he | he | he | he
  · obtain ⟨e⟩ := he
    obtain ⟨a⟩ := h6 ρ K L h e
    exact .six a
  · obtain ⟨e⟩ := he
    rcases h7 ρ K L h e with ha | ha
    · obtain ⟨a⟩ := ha
      exact .sevenNatural a
    · obtain ⟨hL, ha⟩ := ha
      obtain ⟨a⟩ := ha
      exact .sevenFour hL a
  · obtain ⟨e⟩ := he
    obtain ⟨a⟩ := hexacodeAction_of_dimension ρ h e (h36 ρ K L h e)
    exact .tripleSix a
  · obtain ⟨_, he⟩ := he
    obtain ⟨e⟩ := he
    exact (h37 ρ K L h e).elim

end CFSG.Quasithin.ChapterK.Alternating
