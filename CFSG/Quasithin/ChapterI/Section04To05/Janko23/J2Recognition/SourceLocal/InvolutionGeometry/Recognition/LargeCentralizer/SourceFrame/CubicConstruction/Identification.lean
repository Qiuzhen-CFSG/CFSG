module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.Contracts
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel

/-!
# Marking the source normalizer in the coordinate extension

`NormalizerIdentification` requires an actual isomorphism of the full N_G(R)
with the explicit split extension, carrying the literal subgroup R to the
normal root group. It is a construction contract, not an existence theorem.
It contains no selected involution or assertion about its full centralizer.

Restricting this isomorphism to R and transporting centers proves Z(R) = E:
the existing returning pair gives E ≤ Z(R) and |E| = 4, while the coordinate
root group has center of order four. The source recognition and the model's
cubic-action calculation can therefore be developed independently with this
same marked interface.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3 and 46.14, printed
pp.251 and 257–258.
-/

@[expose] public section
open Subgroup Matrix.PSL3Four

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

structure NormalizerIdentification (P : ReturningPair D) where
  equiv : normalizer (P.R : Set G) ≃* RootNormalizerModel.Model
  root_eq : (P.R.subgroupOf (normalizer (P.R : Set G))).map equiv.toMonoidHom =
    RootNormalizerModel.root

namespace NormalizerIdentification

variable {P : ReturningPair D} (I : NormalizerIdentification P)

/-- Restriction to the marked root subgroup, including the ambient subtype map. -/
noncomputable def rootEquiv : P.R ≃* RootNormalizerModel.root :=
  (subgroupOfEquivOfLe (le_normalizer : P.R ≤ normalizer (P.R : Set G))).symm.trans
    ((I.equiv.subgroupMap _).trans (MulEquiv.subgroupCongr I.root_eq))

/-- The actual canonical product receives UT₃(F₄) coordinates. -/
noncomputable def coordinates : P.R ≃* SylowModel.U :=
  I.rootEquiv.trans RootNormalizerModel.rootEquiv.symm

theorem center_card (I : NormalizerIdentification P) : Nat.card (center P.R) = 4 :=
  (Nat.card_congr (centerCongr I.rootEquiv).toEquiv).trans
    RootNormalizerModel.root_center_card

/-- The marked four-group is the full center, once the source normalizer
has been identified. The existence of that identification remains separate. -/
theorem E_center (I : NormalizerIdentification P) : (center P.R).map P.R.subtype = P.E := by
  apply (eq_of_le_of_card_ge P.E_le_center_image ?_).symm
  rw [card_map_of_injective P.R.subtype_injective, I.center_card, P.E_card]

end NormalizerIdentification
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame
