module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases

/-!
# Assembly of the first orientation argument

The earlier natural structures give coordinates on U and on the full moving
section of V/Z with a common quotient projection. In the shared-orientation
case, `QuotientApplication` constructs the actual seed in G_alpha/D_alpha
and applies (1.7)(i) with W equal to the image of Q_alpha. Both resulting
commutator bounds transport to every M-vertex. `ImageCases` excludes them
in each of the two possible image-order cases. The outer automorphism
calculation then constructs the actual opposite coordinates.

`moving_orientation` assembles step (2) from the earlier source inputs and
the contrary commutator hypothesis. It retains the full natural section and
its radical denominator Z[V,Q]; identifying this denominator with U belongs
to step (3). The conditional interface `moving_orientation_of_stages` is
preserved, with both of its mathematical premises discharged below.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), pp.883--884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
open Orientation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Conditional assembly, retaining both intermediate source deductions. The
conclusion contains actual contragredient coordinates, not a module label. -/
theorem moving_orientation_of_stages (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (quotient_pairing : ∀ p : Counterexample geometry,
      ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a →
      ∀ f : FrameAt p.a, f.SameOrientation → BoundsAt geometry p.a)
    (image_cases : ∀ p : Counterexample geometry,
      ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a →
      (∀ a, color R a = false → BoundsAt geometry a) → False)
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    Nonempty (MovingOrientationAt p.a) := by
  obtain ⟨ip⟩ := initial p
  obtain ⟨f⟩ := frame_nonempty modules p.a p.color_a ip.natural_section
  refine ⟨f.movingOrientation ?_⟩
  intro h
  exact image_cases p bad
    (bounds_everywhere hb p.color_a (quotient_pairing p bad f h))

/-- Original MS93 (4.3.2)(2), binary case: the moving natural section of V/Z
has the orientation opposite to U. The actual quotient pairing and both
image-order cases exclude a shared orientation, giving contragredient
coordinates with the original radical denominator and common marking. -/
theorem moving_orientation (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (transfer : NormalizationTransfer R)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    Nonempty (MovingOrientationAt p.a) :=
  moving_orientation_of_stages hb modules initial
    (Orientation.quotient_pairing hb modules transfer initial)
    (Orientation.ImageCases.image_cases source hb modules transfer initial) p bad

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
