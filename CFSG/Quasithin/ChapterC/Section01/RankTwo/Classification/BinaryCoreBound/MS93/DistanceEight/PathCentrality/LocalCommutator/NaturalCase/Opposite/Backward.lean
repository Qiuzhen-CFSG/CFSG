module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Backward.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Backward.LowerBound

/-!
# The backward closing calculation from the forward family

The forward moving-span containment constructs the actual backward
choice, including both edges, its ordered-pair conjugator and noncontainment.
The good-conjugate cover constructs a full reselection at the prescribed
endpoint. Applying the supplied forward family there and transporting back
proves the order-four lower bound on the predecessor displacement. The edge
upper bound identifies this displacement with the original edge and supplies
BackwardClosing. Its consumer applies the proved second escape contradiction
to this constructed witness.

The final two theorems discharge the lower-bound premise of the retained
conditional adapters. They complete the backward source calculation for an
arbitrary SelectedPath and forward family. The initial selection and the
forward family remain the orientation theorem's independent source inputs;
this module does not assert that full orientation theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), claim (1), p.891.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
variable {M : Type*} [Group M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}

/-- Construct the backward witness from the forward family and the still
explicit source order-four lower bound. -/
theorem backwardClosing_of_card_lower [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (forward : ∀ {d e : Vertex R}, ∀ t : SelectedPath R geometry d e, t.ForwardFacts)
    (s : SelectedPath R geometry a c)
    (hlower : 4 ≤ Nat.card (⁅Z R s.start, V R s.predecessor⁆ ⊓
      Z R s.predecessor : Subgroup (FreeAmalgam R))) : Nonempty s.BackwardClosing := by
  obtain ⟨w⟩ := s.backwardChoice_nonempty common hb (forward s).moving_le_span
  exact ⟨{
    intermediate := w.intermediate
    vertex := w.vertex
    adjacent_start := w.adjacent_start
    adjacent_center := w.adjacent_center
    conjugator := w.conjugator
    start_image := w.start_image
    center_image := w.center_image
    noncontainment := w.noncontainment
    displacement := s.backward_displacement_eq_of_card_lower common hb hlower }⟩

/-- The constructed witness feeds the second escape contradiction. -/
theorem false_of_backward_card_lower [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (forward : ∀ {d e : Vertex R}, ∀ t : SelectedPath R geometry d e, t.ForwardFacts)
    (s : SelectedPath R geometry a c)
    (hlower : 4 ≤ Nat.card (⁅Z R s.start, V R s.predecessor⁆ ⊓
      Z R s.predecessor : Subgroup (FreeAmalgam R))) : False := by
  obtain ⟨w⟩ := backwardClosing_of_card_lower common hb forward s hlower
  exact w.false_of_closing common hb

/-- A correctly reselected configuration discharges the lower bound through
its actual forward commutator span, with both vertex identifications retained. -/
theorem backwardClosing_of_reselection [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (forward : ∀ {d e : Vertex R}, ∀ t : SelectedPath R geometry d e, t.ForwardFacts)
    (s : SelectedPath R geometry a c)
    {d e : Vertex R} (t : SelectedPath R geometry d e)
    (hcenter : t.center = s.start) (hendpoint : t.endpoint = s.predecessor) :
    Nonempty s.BackwardClosing := by
  apply backwardClosing_of_card_lower common hb forward s
  simpa only [hcenter, hendpoint] using (forward t).displacement_card_lower t

/-- Consumer of the reselected forward calculation through the backward
witness and the existing reversed-pair escape contradiction. -/
theorem false_of_backward_reselection [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (forward : ∀ {d e : Vertex R}, ∀ t : SelectedPath R geometry d e, t.ForwardFacts)
    (s : SelectedPath R geometry a c)
    {d e : Vertex R} (t : SelectedPath R geometry d e)
    (hcenter : t.center = s.start) (hendpoint : t.endpoint = s.predecessor) : False := by
  obtain ⟨w⟩ := backwardClosing_of_reselection common hb forward s t hcenter hendpoint
  exact w.false_of_closing common hb

/-- The forward family supplies both the backward choice and the order-four
lower bound, so no backward witness or displacement identity is assumed. -/
theorem backwardClosing_nonempty [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (forward : ∀ {d e : Vertex R}, ∀ t : SelectedPath R geometry d e, t.ForwardFacts)
    (s : SelectedPath R geometry a c) : Nonempty s.BackwardClosing :=
  backwardClosing_of_card_lower common hb forward s
    (s.backward_displacement_card_lower common hb forward)

/-- The completed backward calculation gives the second contradiction to
escape on the reversed actual critical pair, as on MS93 p.891. -/
theorem false_of_backward [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (forward : ∀ {d e : Vertex R}, ∀ t : SelectedPath R geometry d e, t.ForwardFacts)
    (s : SelectedPath R geometry a c) : False := by
  obtain ⟨w⟩ := backwardClosing_nonempty common hb forward s
  exact w.false_of_closing common hb

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
