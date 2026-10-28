module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Sp4Four.Inputs

/-!
# The binary subfield Sylow centralizer calculation

Inside the field-involution fixed Sp₄(2), let P be a Sylow two-subgroup of
its actual embedded derived A₆. The remaining calculation says that every
element centralizing P centralizes a Sylow subgroup of the ambient Sp₄(4).
The S₆ centralizer of P is a four-group; an order-two bound is not asserted.
A coordinate proof can place it in the center of a binary unipotent group,
then extend that unipotent group to the four-element coefficient field.

This is an outstanding proof contract, independent of automorphism
classification and central-cover rigidity. `FieldCoverGeometry` proves how
it is used, retaining those two separate obligations in the final assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.6.8(2),
printed pp.247–248, and the two-central actor step of E.6.23, p.254
(PDF p.265). The literal field-fixed embedding is the one in 16.1.4(4),
pp.1171–1172.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Sp4Four

/-- The remaining concrete matrix calculation, keeping the binary derived subgroup. -/
def FixedGroupSylowGeometry : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
    ∀ P : Sylow 2 (FieldComponent.embedded (F := F) 1), ∀ g : Sp F,
      DiagramAutomorphisms.FieldFixedResidual.representative 1 g = g →
      (∀ x ∈ (P : Subgroup (FieldComponent.embedded (F := F) 1)),
        MulAut.conj g (x : Sp F) = x) →
      ∃ Q : Sylow 2 (Sp F), ∀ x ∈ (Q : Subgroup (Sp F)), MulAut.conj g x = x

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Sp4Four
