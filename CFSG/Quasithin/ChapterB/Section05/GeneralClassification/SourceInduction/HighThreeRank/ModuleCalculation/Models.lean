module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.Contracts

/-!
# The moved-module alternatives to construct in B.5.7

The source first obtains the natural S6 or S7 action on the reduced moved
section. The moved space itself is natural, or is the five-dimensional
six-point augmentation core. `SymmetricMovedModel` records these actions
on the literal [V,L] inside the restricted LA representation. The marked
equivalence identifies the original embedded L with the model alternating
subgroup under the same actor isomorphism and module intertwiner.

This is an intermediate output contract, not an earlier-source assumption.
The cover/model comparison must construct it from B.5.1 and the actual
lifted cover. The subsequent module calculation may work from this output
independently, but final assembly must supply the witness. Neither the
three-core model nor a centralizer equality is part of this contract.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the two middle
paragraphs of the proof of B.5.7, printed p.106. In particular the
five-dimensional core is retained without splitting off its fixed line.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation
open QuasisimpleSource
universe u v
variable {D : Type u} [Group D]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- The natural six/seven action, or the six-point augmentation core, on
the actual moved space. The marking is relative to the full actor. -/
inductive SymmetricMovedAction (σ : Representation (ZMod 2) D V)
    (L : Subgroup D) (s : MovedSection σ L) : Prop
  | natural (n : ℕ) (degree : n = 6 ∨ n = 7)
      (equiv : MarkedActionEquiv s.space.toRepresentation ⊤ L
        (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))
  | coreSix (equiv : MarkedActionEquiv s.space.toRepresentation ⊤ L
      (BinaryPermutation.coreRepresentation (Fin 6)) (alternatingGroup (Fin 6)))

/-- The representation and its moved section are those of the original LA,
with the component embedded by the original inclusion. -/
structure SymmetricMovedModel (ρ : Representation (ZMod 2) D V)
    (L A : Subgroup D) where
  sectionData : MovedSection (ρ.comp (L ⊔ A).subtype) (L.subgroupOf (L ⊔ A))
  action : SymmetricMovedAction (ρ.comp (L ⊔ A).subtype)
    (L.subgroupOf (L ⊔ A)) sectionData

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation
