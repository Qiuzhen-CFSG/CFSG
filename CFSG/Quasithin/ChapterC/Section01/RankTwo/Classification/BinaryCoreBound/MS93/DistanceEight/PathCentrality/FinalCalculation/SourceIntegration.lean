module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.SourceAssembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.SourceCriticalApplications
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Inputs

/-!
# The final MS93 (4.4) calculation and its core-factor input

Starting with b>4, the regular window of the actual extended path gives b>6.
The two local calculations then construct the full natural section of V/Z.
The selected-product and symmetric arguments give b=8, centrality in the
whole stabilizer, and both source edge indices. The moving span is transported
by the literal inverse-conjugation action to any M-vertex and supplies the
numerical bound on H. Finally these conclusions fill the actual (4.5) Earlier
input, retaining the earlier extended-path existence and prescribed replacement.

Only preceding source inputs remain explicit: full LocalCommutatorControl
from (4.4.1), critical-prefix nonnatural exclusion from its proof, prescribed
replacement (4.4.4), and the correctly marked ExtendedPath. Full local control
is used in the radius-image boundary calculation and the oppositely ordered
selected-commutator fixed-core estimate. Critical-prefix control is not claimed
to imply arbitrary-orbit control. The DistanceEight parent retains discharge
of these inputs through the LocalCommutator and RegularPaths source owners.
No natural section, final centrality, numerical bound or core-center structure
is assumed here. Source D is fixedCore, and source V in (4.4) is radius two.

Source: Meierfrankenfeld--Stellmacher (1993), Pushing up weak BN-pairs of rank
two, (4.4), printed p.890, and (4.4.5) and the final calculation, pp.894--895.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.SourceIntegration
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

variable (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
  (hlocal : LocalCommutatorControl R)
  (replacement : ∀ {c c'} (p : CriticalPath R geometry c c'),
    HasTurnConjugators R p → PrescribedReplacement R p)
  (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
    ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
    ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False)

include common hb exclude in
private theorem six_lt {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    6 < geometry.b R :=
  RegularPaths.CommutatorPropagation.SourceCriticalApplications.six_lt common hb exclude
    (e.window 0 (by decide) (by decide)) (e.window_regular 0 (by decide) (by decide))

include common hb hlocal exclude in
/-- Both literal local calculations of (4.4.5), with index zero at alpha-4.
The first is equality of the actual quotient-image order to two. -/
theorem local_calculations {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    (Q R (e.walk.getVert 4)).relIndex
        (V R (e.walk.getVert (2 + geometry.b R))) = 2 ∧
      ⁅Z R (e.walk.getVert 2),
        V R (e.walk.getVert (2 + geometry.b R)) ⊓ Q R (e.walk.getVert 4)⁆ ≤
        ⁅Z R (e.walk.getVert 2), Z R (e.walk.getVert (2 + geometry.b R))⁆ :=
  ⟨RadiusImage.source_image_eq_two common (six_lt common hb exclude e) hlocal e,
    ExtendedPath.firstCommutator_le_critical e common (six_lt common hb exclude e) exclude⟩

include common hb hlocal exclude in
/-- The full actual quotient action has one natural section at every M-vertex.
Both local calculation premises have been discharged. -/
theorem natural_section {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    {c : Vertex R} (hc : color R c = false) :
    Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)) :=
  RadiusImage.natural_section common (six_lt common hb exclude e) hlocal exclude e hc

include common hb hlocal replacement exclude in
/-- All clauses of source (4.4), with its full natural-section statement and
both relative indices, from only the earlier controls and extended path. -/
theorem conclusions {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    geometry.b R = 8 ∧
      (∀ c, color R c = false → Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c))) ∧
      (∀ c, color R c = false → ⁅V R c, Q R c⁆ ≤
        (center (stabilizer R c)).map (stabilizer R c).subtype) ∧
      (∀ c t, color R c = false → Adjacent R c t →
        (Z R t).relIndex (Z R c) = 2 ∧ (Q R c).relIndex (Q R t) = 4) := by
  obtain ⟨hd, hc, hi⟩ := Conclusion.SourceAssembly.conclusions common
    (six_lt common hb exclude e) hlocal replacement exclude e
  exact ⟨hd, fun _ hc => natural_section common hb hlocal exclude e hc, hc, hi⟩

include common hb hlocal replacement exclude in
/-- The distinguished alpha,beta application preserves the actual radius V,
full stabilizer center, Z-index and Q-index of the printed statement. -/
theorem alpha_beta {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    geometry.b R = 8 ∧
      Nonempty (Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R))) ∧
      ⁅V R (alpha R), Q R (alpha R)⁆ ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype ∧
      (Z R (beta R)).relIndex (Z R (alpha R)) = 2 ∧
      (Q R (alpha R)).relIndex (Q R (beta R)) = 4 := by
  obtain ⟨hd, hn, hc, hi⟩ := conclusions common hb hlocal replacement exclude e
  exact ⟨hd, hn _ rfl, hc _ rfl, hi _ _ rfl (base_adjacent R)⟩

include common hb hlocal exclude in
/-- The source alpha-2 span contains Vcirc at the actual center. -/
theorem moving_span {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    Vcirc R a ≤ localZSpan R (e.walk.getVert 2) a :=
  RadiusImage.moving_span common (six_lt common hb exclude e) hlocal exclude e

include common hb hlocal exclude in
/-- Transport the genuine distance-two span to any M-vertex, retaining the
literal local orbit span and the project's inverse-conjugation convention. -/
theorem exists_moving_span {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    {c : Vertex R} (hc : color R c = false) :
    ∃ d, (cosetGraph R).dist d c = 2 ∧ Vcirc R c ≤ localZSpan R d c := by
  obtain ⟨u, hu⟩ := exists_mVertex_of_color R (ExtendedPath.center_color e)
  obtain ⟨v, hv⟩ := exists_mVertex_of_color R hc
  let g := u⁻¹ * v
  have hg : act R g a = c := by rw [hu, act_mVertex, mul_inv_cancel_left, ← hv]
  refine ⟨act R g (e.walk.getVert 2), ?_, ?_⟩
  · rw [← hg, dist_act]
    exact ExtendedPath.backward_distance e
  · have hs := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (moving_span common hb hlocal exclude e)
    rwa [← Vcirc_act, ← LocalCommutator.CriticalCase.localZSpan_act, hg] at hs

include common hb hlocal replacement exclude in
/-- Actual numerical application: source centrality and the genuine transported
distance-two span discharge every hypothesis of the existing H bound. -/
theorem H_card_le_four {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)
    {c : Vertex R} (hc : color R c = false) : Nat.card (H R c) ≤ 4 := by
  obtain ⟨d, hd, hs⟩ := exists_moving_span common hb hlocal exclude e hc
  have hz := (conclusions common hb hlocal replacement exclude e).2.2.1 c hc
  exact Numerical.SourceCenterBound.DistanceGreaterFour.H_card_le_four_of_moving_span
    common hc hd hs hz

include common hb hlocal replacement exclude in
/-- The numerical input at alpha, even if the supplied extended path is
centered elsewhere. No H-order or local-centrality premise is retained. -/
theorem H_alpha_card_le_four {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    Nat.card (H R (alpha R)) ≤ 4 :=
  H_card_le_four common hb hlocal replacement exclude e rfl

include common hb hlocal replacement exclude in
/-- Fill the genuine (4.5) input from the completed final calculation. The
remaining extended-path existence and replacement fields are exactly the
preceding RegularPaths outputs, not assumptions of any (4.4) conclusion. -/
theorem earlier
    (extended : ∀ a, color R a = false →
      Nonempty (RegularPaths.ExtendedPath geometry a)) : CoreFactors.Earlier R geometry := by
  obtain ⟨e⟩ := extended (alpha R) rfl
  obtain ⟨hd, hn, hc, hi⟩ := conclusions common hb hlocal replacement exclude e
  exact {
    distance := hd
    natural_section := hn
    centrality := hc
    edge_Z_index := fun a t ha hat => (hi a t ha hat).1
    edge_Q_index := fun a t ha hat => (hi a t ha hat).2
    extended := extended
    replacement := fun _ _ p hp => replacement p hp }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.SourceIntegration
