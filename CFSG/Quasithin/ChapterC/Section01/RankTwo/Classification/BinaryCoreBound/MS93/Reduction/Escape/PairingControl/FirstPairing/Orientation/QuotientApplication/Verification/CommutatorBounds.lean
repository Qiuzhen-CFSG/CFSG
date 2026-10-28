module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.Cyclic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicLocalization
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicNormalization

/-!
# The selected seed's two upper commutator bounds

The selected cyclic pairing has order at most four. Its untilded local
residual normalizes it, and the natural-section localization places it
in the Z-image. The relative-closure equality then transfers both bounds
to X = Z-image joined with the raw parabolic closure in G_alpha/D_alpha.

The final theorem discharges the normalization and localization premises
of the retained conditional helper. It uses the selected seed and earlier
module facts, without any later escape conclusion or (1.7) output.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.883, first
application of (1.7)(i), with the hypotheses on pp.847--848.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {a : Vertex R} {f : FrameAt a}

namespace SelectedSeed
variable (s : SelectedSeed geometry a f)

/-- Conditional assembly of both upper bounds from normalization and
localization of the original cyclic pairing. -/
theorem commutator_bounds_of_cyclic_control (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (ha : color R a = false)
    (hn : localResidual (parabolic (projection f) s.flag s.side) ≤ normalizer
      (⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ :
        Subgroup (LocalQuotient a)))
    (hZ : ⁅zpowers (quotientMap a s.element), quotientImage a (Q R a)⁆ ≤
      quotientImage a (Z R a)) :
    ⁅s.X, quotientImage a (Q R a)⁆ ≤ quotientImage a (Z R a) ∧
      Nat.card (⁅s.X, quotientImage a (Q R a)⁆ : Subgroup (LocalQuotient a)) ≤ 4 := by
  rw [s.X_commutator_Q_eq_cyclic_of_normalized hb ha
    (s.parabolic_le_normalizer_cyclic_of_residual source ha hn)]
  exact ⟨hZ, s.cyclic_commutator_card_le_four source hb modules ha⟩

/-- Both upper commutator bounds for the first application of MS93 (1.7).
The cyclic normalization and localization are proved from the source inputs,
so no pairing premise or bound on the parabolic closure is assumed. -/
theorem commutator_bounds (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (ha : color R a = false) :
    ⁅s.X, quotientImage a (Q R a)⁆ ≤ quotientImage a (Z R a) ∧
      Nat.card (⁅s.X, quotientImage a (Q R a)⁆ : Subgroup (LocalQuotient a)) ≤ 4 := by
  have hn := s.cyclic_commutator_normalized_residual source hb modules ha
  exact s.commutator_bounds_of_cyclic_control source hb modules ha hn
    (s.cyclic_commutator_le_Z_of_residual_normalized source hb modules ha hn)

end SelectedSeed
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
