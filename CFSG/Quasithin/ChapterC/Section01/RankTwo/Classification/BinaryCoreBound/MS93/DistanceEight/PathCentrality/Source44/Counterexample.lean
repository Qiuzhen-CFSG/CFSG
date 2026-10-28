module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.FixedLines.SourceVI
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.LocalControlTransport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.SourceCritical

/-!
# The full source counterexample on the literal terminal selections

MS93 assumes failure of both-clause local control before constructing its
backward and terminal choices.  The source critical-prefix natural branch
constructs the nonnatural hypothesis from that failure.  The actual selectors
then retain the full failure at the backward pair and at both later selected
pairs, together with the exact source-(2.1)(vi) obstruction.

This module does not assert an unconditional terminal contradiction or replace
the genuine Earlier interface.  In particular the first selected critical
image remains two, and its final contradiction is still a source obligation.

Source: MS93 (4.4.1), pp.890--892, especially the opening contrary assumption
on p.890 and the final two simultaneous choices on p.892.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- On an actual source critical prefix, the proved natural branch turns the
complete local-control failure into the source's nonnatural hypothesis. -/
theorem critical_prefix_failure_not_natural (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a e : Vertex R} (p : CriticalPath R geometry a e)
    (hn : ¬ ⁅Z R a,Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2))
    (hfail : ¬ LocalControlAt R a (p.walk.getVert 2)) :
    ¬ HasNaturalSection R a (p.walk.getVert 2) := by
  intro hnat
  exact hfail (NaturalCase.localControl_of_naturalSection_and_critical_prefix common hb p hn hnat)

/-- Both printed geometric choices are constructed while the complete original
counterexample is retained on the backward pair. -/
theorem critical_prefix_counterexample_configuration
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a e : Vertex R} (p : CriticalPath R geometry a e)
    (hn : ¬ ⁅Z R a,Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2))
    (hfail : ¬ LocalControlAt R a (p.walk.getVert 2)) :
    ∃ w : BackwardWitness R geometry a (p.walk.getVert 2),
      Nonempty (TerminalNeighbor w) ∧
      ¬ HasNaturalSection R w.backward (p.walk.getVert 2) ∧
      ¬ LocalControlAt R w.backward (p.walk.getVert 2) := by
  have htwo : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  have hc : color R (p.walk.getVert 2) = false := (p.vertex_color htwo).mpr (by decide)
  have hd : (cosetGraph R).dist a (p.walk.getVert 2) = 2 := p.dist_start htwo
  have hnone := critical_prefix_failure_not_natural common hb p hn hfail
  obtain ⟨w,hw⟩ := exists_terminal_configuration common hb p.start_color hc hd hn hnone
  exact ⟨w,hw,fun h => hnone (w.hasNaturalSection_iff.mp h),
    backward_localControlAt_failure w hfail⟩

/-- The first selection keeps the full original local-control failure and the
source-(2.1)(vi) obstruction, with its actual selected image of order two. -/
theorem first_selection_retains_source_failure
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) (hfail : ¬ LocalControlAt R a c)
    {t : Vertex R} (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hnot : ¬ edgeFixedNatural (R := R) w.backward t ≤ fixedCore R c) :
    ∃ g ∈ stabilizer R c,
      ¬ LocalControlAt R (act R g w.backward) c ∧
      (¬ Z R n.vertex ≤ normalizer
        (edgeFixedNatural (R := R) (act R g w.backward) (act R g t))) ∧
      (¬ Z R n.vertex ≤ normalizer
        (Z R (act R g w.backward) ⊔ Z R c : Subgroup (FreeAmalgam R))) ∧
      (Q R w.predecessor).relIndex (Z R (act R g w.backward)) = 2 ∧
      (¬ ⁅Z R (act R g w.backward),Z R n.vertex⁆ ≤
        ⁅⁅Z R (act R g w.backward),Q R c⁆,Z R n.vertex⁆ ⊔ Z R c) := by
  obtain ⟨g,hg,hF,hJ,hi⟩ := first_selection_index_two common hb ha hd w n hdt hct hnot
  have hgc : act R g c = c := hg
  have hdc : (cosetGraph R).dist (act R g w.backward) c = 2 := by
    simpa only [hgc] using (dist_act R g w.backward c).trans (w.backward_distance hd)
  refine ⟨g,hg,?_,hF,hJ,hi,selected_source_vi_commutator_not_le common hb ha hd w n hdc hJ⟩
  intro h
  exact backward_localControlAt_failure w hfail ((localControlAt_local_conjugator_iff hg).mp h)

/-- The reversed source selection moves the full failure to `(c,delta)`, with
the same transporter used for the fixed-line containment.  It is not asserted
at the oppositely ordered pair `(delta,c)`. -/
theorem second_selection_retains_source_failure
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) (hfail : ¬ LocalControlAt R a c)
    {t : Vertex R} (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hcore : edgeFixedNatural (R := R) w.backward t ≤ fixedCore R c) :
    ∃ g : FreeAmalgam R, act R g w.backward = c ∧
      (¬ LocalControlAt R c (act R g c)) ∧
      (¬ Z R n.vertex ≤ normalizer (edgeFixedNatural (R := R) c (act R g t))) ∧
      (¬ Z R n.vertex ≤ normalizer
        (Z R (act R g c) ⊔ Z R c : Subgroup (FreeAmalgam R))) ∧
      Nonempty (CriticalPath R geometry (act R g c) w.predecessor) ∧
      edgeFixedNatural (R := R) c (act R g t) ≤ fixedCore R (act R g c) := by
  obtain ⟨g,hg,hF,hJ,hp,hD⟩ := second_selection_core_transport common hb ha hd w n hdt hct hcore
  refine ⟨g,hg,?_,hF,hJ,hp,hD⟩
  intro h
  have hh : LocalControlAt R (act R g w.backward) (act R g c) := by simpa only [hg] using h
  exact backward_localControlAt_failure w hfail ((localControlAt_act_iff g w.backward c).mp hh)

/-- The retained full source counterexample has a crossing element on the
same index-two selection.  This is the literal remaining action witness,
inside the original local orbit, rather than a replacement normalizer claim. -/
theorem first_selection_failure_crossing
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) (hfail : ¬ LocalControlAt R a c)
    {t : Vertex R} (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hnot : ¬ edgeFixedNatural (R := R) w.backward t ≤ fixedCore R c) :
    ∃ g ∈ stabilizer R c,
      ¬ LocalControlAt R (act R g w.backward) c ∧
      (Q R w.predecessor).relIndex (Z R (act R g w.backward)) = 2 ∧
      ∃ x ∈ Z R (act R g w.backward), x ∉ Q R w.predecessor ∧
        ∃ z ∈ Z R n.vertex, ⁅x,z⁆ ∉ Z R c := by
  obtain ⟨g,hg,hfail',hF,hJ,hi,_⟩ :=
    first_selection_retains_source_failure common hb ha hd w n hfail hdt hct hnot
  exact ⟨g,hg,hfail',hi,selected_crossing_element common hb ha hd w n hdt hct hg hF hJ⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
