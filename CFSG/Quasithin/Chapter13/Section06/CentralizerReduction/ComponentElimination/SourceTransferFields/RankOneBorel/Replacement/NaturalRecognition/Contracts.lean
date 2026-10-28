module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.Action
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement

/-!
# The rank-one action alternatives and the seed exclusion

The classification target keeps the quotient natural action separate from
an alternating-five action on the moved space itself. Its actor is a marked
component of the full faithful action, which need not itself be generated
by offenders. This target must be obtained from the corrected universal
B.5 classification, not supplied as a replacement for that classification.

The exclusion below states 13.6.15 on the literal seed span inside W_K.
It excludes equivariant permutation-module coordinates on a member of Irr⁺;
an abstract identification of the actor with A₅ does not exclude a module.
Neither of these definitions proves the corresponding source implication.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.1 and
B.5.6, pp.99–105; 13.6.15 and 13.6.18, pp.930–931 (PDF pp.947–948).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
open ChapterB.QuasisimpleSource ComponentSelection

/-- The module conclusions to extract for an actual rank-one component.
The natural branch retains its central quotient; the permutation branch
identifies the whole moved space and retains membership in Irr⁺. -/
inductive RankOneComponentCase {D V : Type*} [Group D] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
    (C : Subgroup D) (F : BinaryField) : Prop
  | natural (sectionData : MovedSection ρ C)
      (coordinates : ActionEquiv (sectionData.action.comp C.subtype) (linearNatural F 2))
  | alternatingFive (sectionData : MovedSection ρ C)
      (irrPlus : IsIrrPlus ρ C sectionData.space.toSubmodule)
      (coordinates : ActionEquiv (sectionData.space.toRepresentation.comp C.subtype)
        (alternatingNatural 5))

variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]

/-- The literal ⟨z^K⟩, regarded as a binary subspace of W_K. -/
noncomputable def seedSpace : Submodule (ZMod 2) (Additive (WK K L T z v)) :=
  AddSubgroup.toZModSubmodule 2
    ((conjugateSpanBy (zpowers z) K).subgroupOf (WK K L T z v)).toAddSubgroup

/-- The exact module exclusion in 13.6.15. Coordinates here include an
isomorphism K⁺ ≃ A₅, so its conditional actor hypothesis is retained. The
assertion is on a constituent inside ⟨z^K⟩, not on an arbitrary quotient. -/
def ExcludesAlternatingFiveSeed : Prop :=
  ∀ I : Subrepresentation (componentRepresentation K L T z v hL hz),
    I.toSubmodule ≤ seedSpace K L T z v →
    IsIrrPlus (componentRepresentation K L T z v hL hz) ⊤ I.toSubmodule →
    ¬ Nonempty (ActionEquiv I.toRepresentation (alternatingNatural 5))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
end
