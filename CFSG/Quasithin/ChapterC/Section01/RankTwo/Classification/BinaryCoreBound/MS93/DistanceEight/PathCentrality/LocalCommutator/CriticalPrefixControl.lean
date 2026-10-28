module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.SourceCritical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.LocalControlTransport

/-!
# Local control on the critical prefixes actually used by MS93

The complete two-clause local-control condition transports under the literal
local conjugator. Consequently a source theorem restricted to critical prefixes
controls every escaping local orbit. For an endpoint Z-layer at distance b-2,
failure of a commutator bound itself supplies escape: Q at that endpoint
centralizes its Z-layer. This also gives the covering clause for a moving
endpoint element, without asserting control on arbitrary distance-two pairs.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), pp.890--892,
and its endpoint applications in (4.4.4)--(4.4.5), pp.894--895.
The critical-prefix theorem remains the independent earlier-source input.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator
open NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Source (4.4.1) restricted to the actual prefixes of critical paths. -/
def CriticalPrefixControl (R : Subgroup M) (geometry : Geometry R) : Prop :=
  ∀ {a e : Vertex R} (p : CriticalPath R geometry a e),
    LocalControlAt R a (p.walk.getVert 2)

/-- An already fixed initial displacement gives both local conclusions. -/
theorem localControl_of_initial_fixed (hb : 2 < geometry.b R)
    {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2)
    (h : ⁅Z R a, Q R c⁆ ≤ fixedCore R c) : LocalControlAt R a c := by
  have hs := (span_commutator_le_fixed_iff hc hd hb).mpr h
  refine ⟨(commutator_mono le_rfl inf_le_right).trans hs, ?_⟩
  intro x hx hn
  exact (hn ((commutator_mono le_rfl (zpowers_le.mpr hx)).trans hs)).elim

/-- It suffices to prove the critical-prefix statement in its moving case. -/
theorem criticalPrefixControl_of_moving (hb : 4 < geometry.b R)
    (h : ∀ {a e : Vertex R} (p : CriticalPath R geometry a e),
      ¬ ⁅Z R a, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      LocalControlAt R a (p.walk.getVert 2)) : CriticalPrefixControl R geometry := by
  intro a e p
  by_cases hn : ⁅Z R a, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2)
  · have hl : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
    exact localControl_of_initial_fixed (by omega)
      ((p.vertex_color hl).mpr (by decide)) (p.dist_start hl).le hn
  · exact h p hn

/-- An escaping local orbit is the conjugate of an actual critical prefix.
Both kernel factors in local control are transported with that conjugator. -/
theorem localControl_of_spanEscape_of_criticalPrefix
    (hb : 4 < geometry.b R) (hprefix : CriticalPrefixControl R geometry)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (escape : SpanEscape geometry a c) : LocalControlAt R a c := by
  by_cases hn : ⁅Z R a, Q R c⁆ ≤ fixedCore R c
  · exact localControl_of_initial_fixed (by omega) hc hd.le hn
  · obtain ⟨s⟩ := movingSeed_nonempty hd hn
    obtain ⟨e, g, p, hcenter, _⟩ :=
      (spanEscape_iff_critical_placement ha (by omega) s).mp escape
    have hp := hprefix p
    rw [hcenter] at hp
    exact (CriticalCase.localControlAt_local_conjugator_iff g.property).mp hp

/-- The endpoint actor supplies escape whenever the desired bound fails.
Thus no unconditional orbit-escape premise is needed for this source use. -/
theorem endpoint_commutator_le_fixed_of_criticalPrefix
    (hb : 4 < geometry.b R) (hprefix : CriticalPrefixControl R geometry)
    {a c e : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (he : color R e = false)
    (hce : (cosetGraph R).dist c e + 2 = geometry.b R)
    (hZ : Z R e ≤ Q R a ⊓ Q R c) :
    ⁅localZSpan R a c, Z R e⁆ ≤ fixedCore R c := by
  by_contra hn
  have escape : SpanEscape geometry a c := by
    refine ⟨e, hce, ?_⟩
    intro hs
    apply hn
    have hz : ⁅Q R e, Z R e⁆ = ⊥ := by
      rw [commutator_comm]
      exact geometry.centralizes e he
    exact ((commutator_mono hs le_rfl).trans_eq hz).trans bot_le
  exact hn ((commutator_mono le_rfl hZ).trans
    (localControl_of_spanEscape_of_criticalPrefix hb hprefix ha hc hd escape).1)

/-- The second local-control clause for an actual moving endpoint element. -/
theorem endpoint_covers_Z_of_criticalPrefix
    (hb : 4 < geometry.b R) (hprefix : CriticalPrefixControl R geometry)
    {a c e : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (he : color R e = false)
    (hce : (cosetGraph R).dist c e + 2 = geometry.b R)
    {x : FreeAmalgam R} (hxQ : x ∈ Q R c) (hxZ : x ∈ Z R e)
    (hm : ¬ ⁅localZSpan R a c, zpowers x⁆ ≤ fixedCore R c) :
    Z R c ≤ ⁅zpowers x, localZSpan R a c⁆ ⊔ fixedCore R c :=
  (localControl_of_spanEscape_of_criticalPrefix hb hprefix ha hc hd
    (spanEscape_of_endpoint_movement he hce hxZ hm)).2 x hxQ hm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator

