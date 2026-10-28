module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification

/-!
# The first quotient application of the rank-one pairing

The shared inner marking selects an actual moving element and a compatible
flag. Verification supplies all the (1.7) hypotheses for the parabolic
closure enlarged by the Z-image, with W equal to the Q-image in G_alpha/D_alpha.
The genuine pairing theorem and commutator lifting then give both printed
bounds, including the precise bracket placement [V,[Q,Ltilde]].

`quotient_pairing` discharges selection and verification from the earlier
source inputs. The subsequent image-order argument excluding the shared
orientation belongs to the parent orientation theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), printed p.883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation
open QuotientApplication
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Conditional assembly of the actual pairing. Both producers must be
supplied before this becomes the source-only application at p.883. -/
theorem quotient_pairing_of_stages (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (transfer : NormalizationTransfer R)
    (select : ∀ p : Counterexample geometry,
      ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a →
      ∀ f : FrameAt p.a, f.SameOrientation → Nonempty (SelectedSeed geometry p.a f))
    (verify : ∀ p : Counterexample geometry,
      ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a →
      ∀ f : FrameAt p.a, f.SameOrientation →
      ∀ s : SelectedSeed geometry p.a f, Nonempty (PairingPremises s))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (f : FrameAt p.a) (same : f.SameOrientation) : BoundsAt geometry p.a := by
  obtain ⟨s⟩ := select p bad f same
  obtain ⟨h⟩ := verify p bad f same s
  exact bounds_of_selectedSeed hb modules transfer p.color_a s h

/-- The first actual application of original MS93 (1.7)(i) on p.883.
The shared orientation constructs the selected seed; its pairing premises
are proved, and both commutator bounds lift from G_alpha/D_alpha. -/
theorem quotient_pairing (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (transfer : NormalizationTransfer R)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (f : FrameAt p.a) (same : f.SameOrientation) : BoundsAt geometry p.a := by
  apply quotient_pairing_of_stages hb modules transfer
    (selectedSeed_nonempty hb modules transfer initial) _ p bad f same
  intro p bad f _ s
  exact pairingPremises_nonempty source hb modules transfer p bad f s

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation
