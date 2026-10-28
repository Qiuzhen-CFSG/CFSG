module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Estimates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.LargeImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.SmallImage

/-!
# The first-pairing image cases from the two pairing bounds

In the large-image case the displacement bound on the original path gives a
moving-neighbor commutator bound at alpha+2, contradicting transported step (1).
In the small-image case a commutator-image lower bound of four fills the whole
moving commutator, whose order is at most four. Its containment in D_alpha then
contradicts step (1) at alpha.

Critical noncommutation excludes image order one, so these are the exhaustive
cases. `image_cases` constructs both estimates from the earlier source inputs
and the two explicit `BoundsAt` clauses. The quotient-pairing argument producing
those clauses remains with the parent orientation assembly.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), pp.883--884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : MS93.Geometry R}

/-- Step (1) at the second path vertex excludes the large-image estimate. -/
theorem large_image_false_of_estimate (hb : 2 < geometry.b R)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (path : FrontPath p) (estimate : LargeImageEstimate p path) : False := by
  obtain ⟨q, hqa, hbad⟩ := contrary_at p bad path.second path.second_color
  obtain ⟨iq⟩ := initial q
  have hmove : p.a ∈ movingNeighbors geometry q.a := by
    simpa only [hqa] using estimate.moving
  have hnot := moving_commutator_not_le_fixed hb transfer iq hbad hmove
  rw [hqa] at hnot
  exact hnot (path.start_commutator_le_edge.trans estimate.edge_le_fixed)

/-- The actual image lower bound identifies the whole moving commutator before
using the fixed-core bound. The cardinality premise is still a producer output. -/
theorem small_image_false_of_estimate (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (p : Counterexample geometry) (ip : InitialFacts p)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (estimate : SmallImageEstimate p) : False := by
  have heq := moving_commutator_eq_of_image_lower source hb modules p
    estimate.moving estimate.image_lower
  apply moving_commutator_not_le_fixed hb transfer ip bad estimate.moving
  rw [← heq]
  exact (commutator_mono (moving_Z_le_V estimate.moving) le_rfl).trans
    estimate.commutator_le_fixed

/-- Conditional assembly from the two estimates. The theorem `image_cases`
below constructs both estimates from the two pairing bounds. -/
theorem image_cases_of_estimates (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (large : 2 < (Q R p.a).relIndex (V R p.c) →
      ∀ path : FrontPath p, LargeImageEstimate p path)
    (small : (Q R p.a).relIndex (V R p.c) = 2 → Nonempty (SmallImageEstimate p)) :
    False := by
  obtain ⟨ip⟩ := initial p
  by_cases hi : 2 < (Q R p.a).relIndex (V R p.c)
  · let path := frontPath p ip.six_le
    exact large_image_false_of_estimate hb transfer initial p bad path (large hi path)
  · obtain ⟨estimate⟩ := small (image_order_eq_two source hb p hi)
    exact small_image_false_of_estimate source hb modules transfer p ip bad estimate

/-- Both image-order cases of MS93 (4.3.2)(2), printed p.884, contradict
step (1) once the two preceding pairing bounds hold at every M-vertex.
The original geodesic supplies the large-image estimate; the small-image
estimate retains the literal intersection and its commutator image. -/
theorem image_cases (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (bounds : ∀ a, color R a = false → BoundsAt geometry a) : False := by
  apply image_cases_of_estimates source hb modules transfer initial p bad
  · intro hi path
    exact large_image_estimate source hb modules initial p bad bounds hi path
  · intro hi
    exact small_image_estimate source hb modules transfer initial p bad bounds hi

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
