module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Inputs

/-!
# The remaining central-cover geometry in the Sp₄(4) field branch

The action is on a finite quasisimple central two-cover, with its actual A₆
component and pointwise fixed component Sylow subgroup. Its distinguished
involution descends, under a genuine quotient equivalence, to the field
involution subgroup of Sp₄(4). The outstanding calculation must produce a
nonidentity actor fixing a Sylow subgroup of the whole cover.

This is a proof contract, not an established model fact. In particular it
neither discards central two-covers nor asserts that the component Sylow is
Sylow in the cover. `Sp4Four` proves the source exclusion conditional on
this contract and retains responsibility for its discharge.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.6.23,
printed p.254 (PDF p.265), with E.6.5 and E.6.8, pp.246–248. Compare the
explicit field-involution fixed group in 16.1.4(4), pp.1171–1172.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Sp4Four
universe u

/-- Outstanding intrinsic geometry for the genuine field exception. -/
def FieldCoverSylowGeometry : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] [IsQuasisimple D],
    IsPGroup 2 (center D) →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
    ∀ e : (D ⧸ center D) ≃* Sp F, ∀ s : FixedSixAction D,
      ((zpowers s.involution).map (quotientAut (center D))).map
          (MulAut.congr e).toMonoidHom =
        zpowers (DiagramAutomorphisms.FieldFixedResidual.representative 1) →
      ∃ a : MulAut D, a ∈ s.actors ∧ a ≠ 1 ∧
        ∃ P : Sylow 2 D, ∀ x ∈ (P : Subgroup D), a x = x

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Sp4Four
