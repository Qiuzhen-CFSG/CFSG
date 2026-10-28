module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration

/-!
# Assembly of the selected seed's remaining pairing hypotheses

The elementary and fixed-preimage calculations supply the Frattini and
seed-fixation clauses. Moving generation also forces nontriviality of the
pairing by normalization transfer. The cyclic commutator calculations give
containment in the Z-image and the order bound through the actual parabolic
closure. Natural generation supplies the moving containment and genuine
rank-one coordinates with exactly the fixed-preimage kernel C.

`pairingPremises_nonempty` discharges every remaining (1.7) hypothesis for
an explicit selected seed. Once that seed is supplied, neither initial
escape facts nor a separate same-orientation hypothesis is needed for
verification. Selection and the final application remain with the parent.

Source: Meierfrankenfeld--Stellmacher (1993), pp.847--848 and 883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R}

/-- Conditional assembly discharging the elementary, fixed-preimage and
nontriviality obligations. All remaining mathematical premises are explicit. -/
theorem pairingPremises_of_local_calculations
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (transfer : NormalizationTransfer R) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (f : FrameAt p.a) (s : SelectedSeed geometry p.a f)
    (hcomm : ⁅s.X, quotientImage p.a (Q R p.a)⁆ ≤ quotientImage p.a (Z R p.a))
    (hcard : Nat.card (⁅s.X, quotientImage p.a (Q R p.a)⁆ :
      Subgroup (LocalQuotient p.a)) ≤ 4)
    (hrank : RankOneFactor
      (localResidual (parabolic (projection f) s.flag (!s.side)))
      (localGenerated (parabolic (projection f) s.flag (!s.side)) s.X) s.C)
    (hmoving : quotientImage p.a (Vcirc R p.a) ≤ generated s.X) :
    Nonempty (PairingPremises s) := by
  exact ⟨{
    frattini_le := s.frattini_le source hb p.color_a
    commutator_le := hcomm
    commutator_nontrivial := s.commutator_nontrivial_of_moving_le hb transfer bad hmoving
    commutator_card_le := hcard
    seed_fixed := s.seed_fixed source hb p.color_a
    rank_one_natural := hrank
    moving_le := hmoving }⟩

/-- All remaining hypotheses of the first quotient application of (1.7),
including moving generation, follow from the earlier source inputs and the
explicit selected seed. No pairing premise is assumed. -/
theorem pairingPremises_nonempty
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (transfer : NormalizationTransfer R)
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (f : FrameAt p.a) (s : SelectedSeed geometry p.a f) :
    Nonempty (PairingPremises s) := by
  obtain ⟨hcomm, hcard⟩ := s.commutator_bounds source hb modules p.color_a
  obtain ⟨hrank⟩ := s.rankOneFactor_nonempty source hb p.color_a
  exact pairingPremises_of_local_calculations source hb transfer p bad f s
    hcomm hcard hrank (s.moving_le_generated source hb p.color_a)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
