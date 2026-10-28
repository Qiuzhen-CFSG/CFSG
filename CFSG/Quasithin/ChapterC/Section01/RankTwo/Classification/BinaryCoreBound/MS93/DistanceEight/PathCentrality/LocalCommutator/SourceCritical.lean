module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.SourceCritical

/-!
# Local commutator control from the source critical-prefix branch

For an escaping orbit, the geometric construction produces an actual critical
prefix in that same orbit. Its local span is literally unchanged. The earlier
nonnatural-section contradiction therefore supplies the natural section of
the original span, and the complete natural branch proves local control there.

The only independent input is the nonnatural branch of (4.4.1), restricted
here to genuine critical prefixes. Its producer is the existing CriticalCase
development. No local-control, selected-configuration or orbit-escape theorem
is assumed in the endpoint-actor application: movement supplies escape first.
The arbitrary-pair local-control statement remains a separate public target.

Source: MS93 (4.4.1), printed pp.890--892, with its standing critical-path
notation. The endpoint-actor application feeds (4.4.4), printed p.894.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.SourceCritical
open NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R}

/-- This is exactly the independent nonnatural branch at a source prefix. -/
theorem localControl_of_critical_prefix (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a e : Vertex R} (p : CriticalPath R geometry a e)
    (hn : ¬ ⁅Z R a, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2))
    (exclude : ¬ HasNaturalSection R a (p.walk.getVert 2) → False) :
    LocalControlAt R a (p.walk.getVert 2) := by
  have hnat : HasNaturalSection R a (p.walk.getVert 2) := by
    by_contra h
    exact exclude h
  exact NaturalCase.localControl_of_naturalSection_and_critical_prefix common hb p hn hnat

/-- Rebase only the earlier natural-section premise along the unchanged span.
Both resulting commutator conclusions concern the original ordered pair. -/
theorem localControl_of_spanEscape (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (exclude : ∀ {d e : Vertex R} (p : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ HasNaturalSection R d (p.walk.getVert 2) → False)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (escape : SpanEscape geometry a c) : LocalControlAt R a c := by
  obtain ⟨s⟩ := movingSeed_nonempty hd hn
  obtain ⟨e, g, p, hcenter, _⟩ :=
    (spanEscape_iff_critical_placement ha (by omega) s).mp escape
  have hspan : localZSpan R (act R g a) c = localZSpan R a c :=
    CriticalCase.span_eq_of_local_conjugator g.property
  have hdist : (cosetGraph R).dist (act R g a) c = 2 := by
    have h := dist_act R (g : FreeAmalgam R) a c
    rw [show act R g c = c from g.property] at h
    exact h.trans hd
  have hn' : ¬ ⁅Z R (act R g a), Q R c⁆ ≤ fixedCore R c := by
    intro h
    apply hn
    apply (span_commutator_le_fixed_iff hc hd.le (by omega)).mp
    have hh := (span_commutator_le_fixed_iff hc hdist.le (by omega)).mpr h
    rwa [hspan] at hh
  have hnp : ¬ ⁅Z R (act R g a), Q R (p.walk.getVert 2)⁆ ≤
      fixedCore R (p.walk.getVert 2) := by rwa [hcenter]
  have hnatp : HasNaturalSection R (act R g a) (p.walk.getVert 2) := by
    by_contra h
    exact exclude p hnp h
  have hnat : HasNaturalSection R a c := by
    rw [hcenter] at hnatp
    simpa only [HasNaturalSection, hspan] using hnatp
  exact NaturalCase.localControl_of_naturalSection_and_spanEscape
    common hb ha hc hd hn hnat escape

/-- Movement by x in the actual endpoint Z-layer supplies all orbit and
initial-noncentrality premises of the local-control application. -/
theorem localControl_of_endpoint_movement (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (exclude : ∀ {d e : Vertex R} (p : CriticalPath R geometry d e),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ HasNaturalSection R d (p.walk.getVert 2) → False)
    {a c e : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (he : color R e = false) (hce : (cosetGraph R).dist c e + 2 = geometry.b R)
    {x : FreeAmalgam R} (hxQ : x ∈ Q R c) (hxZ : x ∈ Z R e)
    (hm : ¬ ⁅localZSpan R a c, zpowers x⁆ ≤ fixedCore R c) :
    LocalControlAt R a c := by
  have hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c := by
    intro h
    exact hm ((commutator_mono le_rfl (zpowers_le.mpr hxQ)).trans
      ((span_commutator_le_fixed_iff hc hd.le (by omega)).mpr h))
  exact localControl_of_spanEscape common hb exclude ha hc hd hn
    (spanEscape_of_endpoint_movement he hce hxZ hm)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.SourceCritical
