module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.NaturalLayerRecognition
/-!
# The natural Sp4(4) moving-section predicate

This predicate records the exact canonical moved/fixed section and the
field degree. Keeping its instance parameters at this representation
boundary avoids repeatedly synthesizing nested quotient-module structures
in the original Chapter 10 subgroup tower.
Source: MS93 (3.2)(vi).
-/
public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource
/-- The actual moving section is natural symplectic over a field of order four. -/
@[expose] def HasNaturalMovingSection {J V : Type*} [Group J]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) J V) (C : Subgroup J) [C.Normal] : Prop :=
  ∃ F : BinaryField, F.degree = 2 ∧
    Nonempty (ActionEquiv ((MovedSection.ofNormal ρ C).action.comp C.subtype)
      (binarySymplectic F))
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
