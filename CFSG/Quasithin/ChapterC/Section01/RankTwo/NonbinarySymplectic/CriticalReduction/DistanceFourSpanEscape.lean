module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanAction

/-!
# Both literal normal spans escape in the large backward-image branch

The large critical-image radius bound prevents the midpoint normal span
from lying in the midpoint kernel: such containment would make an actual
critical actor fix the span modulo its starting seed, forcing the span
into B. The path moving-index bound excludes that conclusion.

Apply this to the reverse of the supplied backward path u→e, whose literal
midpoint is a. Thus V2=<Z_a^{G_e}> escapes Q_a. If V1=<Z_e^{G_a}> lay in
Q_e, the proved crossed commutator bound would make V2 fix V1 modulo Z_a,
giving the same contradiction. Both spans remain those of the original
a,e pair. No relation between u and a prescribed orbit is assumed.

Source: the paired actors in MS93 (5.12)(2), printed pp.925--926. The
radius fixed-core hypothesis remains an explicit source branch. These
escape assertions do not by themselves assert an FF module or offender.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem midpoint_span_not_le_B
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    ¬ localZSpan d.radical (path.walk.getVert 2) a ≤
      B d.radical a (geometry.Z_normal a) := by
  intro hh
  have hu := (DistanceEight.U_le_Z d.radical (path.walk.getVert 2)).trans
    ((Z_le_localZSpan d.radical (path.walk.getVert 2) a).trans hh)
  have hi := h.replacement_path_moving_index_ge_field d path hb
  rw [relIndex_eq_one.mpr hu] at hi
  exact (not_le_of_gt (Finite.one_lt_card (α := F))) hi

private theorem actual_normal_radius_fixed
    {geometry : Geometry d.radical} (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (W T : Subgroup (FreeAmalgam d.radical))
    (hWV : W ≤ V d.radical a)
    (hSW : stabilizer d.radical a ≤ normalizer (W : Set _))
    (hTS : T ≤ stabilizer d.radical a) (hTQ : ¬ T ≤ Q d.radical a)
    (hc : ⁅W,T⁆ ≤ Z d.radical a) : W ≤ B d.radical a (geometry.Z_normal a) := by
  obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb ha
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hk : f.ker=(Q d.radical a).subgroupOf (stabilizer d.radical a) := by
    rw [←hfQ]
    exact (comap_map_eq_self_of_injective (stabilizer d.radical a).subtype_injective f.ker).symm
  exact normal_radius_le_B_of_kernel_escape geometry (by omega) ha f hf hk
    (Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) a ha)
    W T hWV hSW hTS hTQ hc

private theorem midpoint_span_escapes_of_large
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hlarge : Nat.card F^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ¬ localZSpan d.radical (path.walk.getVert 2) a ≤ Q d.radical (path.walk.getVert 2) := by
  intro htrap
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hl : path.walk.length=4 := path.length_eq_b.trans hb
  have hWV : localZSpan d.radical (path.walk.getVert 2) a ≤ V d.radical a :=
    localZSpan_le_V d.radical (by
      rw [SimpleGraph.dist_comm,path.dist_start (by omega : 2 ≤ path.walk.length)])
  have hdisp := h.replacement_large_critical_radius_commutator d path hb4 hlarge
  have hpen : path.walk.getVert (path.walk.length-2)=path.walk.getVert 2 := by rw [hl]
  rw [hpen] at hdisp
  have heQ := (critical_reverse d.radical geometry
    (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
    a path.start_color (by
      rw [geometry.distance_constant a path.start_color]
      exact lt_of_lt_of_le (by decide : 0<4) hb4)
    z path.end_color path.critical).2
  exact midpoint_span_not_le_B h d path hb4
    (actual_normal_radius_fixed h d hb4 path.start_color _ (Z d.radical z) hWV
      (localZSpan_normalized d.radical (path.walk.getVert 2) a)
      (path.endpoint_Z_le_start_stabilizer (by omega)) heQ
      ((commutator_mono (le_inf hWV htrap) le_rfl).trans hdisp))

/-- The actual large backward image makes both original midpoint spans
escape the opposite kernels. No prescribed-orbit or nonzero-actor premise
is supplied; the fixed-radius premise is the literal source branch. -/
theorem Input.replacement_distance_four_spans_escape_of_large_back
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ¬ localZSpan d.radical (path.walk.getVert 2) a ≤ Q d.radical (path.walk.getVert 2) ∧
      ¬ localZSpan d.radical a (path.walk.getVert 2) ≤ Q d.radical a := by
  let e := path.walk.getVert 2
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hsq : Nat.card F^2 ≤ (Q d.radical e).relIndex (Z d.radical u) := by
    by_contra! hs
    have hi := (h.replacement_small_critical_indices_eq_field d back (by omega) hs).1
    exact (ne_of_gt hlarge) hi
  have hrevLarge := h.replacement_large_critical_reverse_index d back (by omega) hsq
  let rev : CriticalPath d.radical geometry e u := {
    start_color := back.end_color
    walk := back.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,back.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse d.radical geometry
      (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
        (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
      u back.start_color (by
        rw [geometry.distance_constant u back.start_color]
        exact lt_of_lt_of_le (by decide : 0<4) hb4)
      e back.end_color back.critical }
  have hrmid : rev.walk.getVert 2=a := by
    change back.walk.reverse.getVert 2=a
    rw [SimpleGraph.Walk.getVert_reverse,back.length_eq_b,hb]
    exact hmid
  have hW2escape : ¬ localZSpan d.radical a e ≤ Q d.radical a := by
    have hh := midpoint_span_escapes_of_large h d rev hb hrevLarge
    rwa [hrmid] at hh
  refine ⟨?_,hW2escape⟩
  intro htrap
  have hl := path.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hWV : localZSpan d.radical e a ≤ V d.radical a :=
    localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,hd])
  have hW2S : localZSpan d.radical a e ≤ stabilizer d.radical a :=
    (localZSpan_le_Q d.radical he hd.le (by omega : 2 < geometry.b d.radical)).trans
      (Q_le_stabilizer_of_dist_two d.radical e a he (by rw [SimpleGraph.dist_comm]; exact hd))
  obtain ⟨_,_,_,_,hcross,_⟩ := h.replacement_distance_four_normal_spans_of_radius_fixed d path hb hfixed
  rw [inf_eq_left.mpr htrap] at hcross
  exact midpoint_span_not_le_B h d path hb4
    (actual_normal_radius_fixed h d hb4 path.start_color _ (localZSpan d.radical a e)
      hWV (localZSpan_normalized d.radical e a) hW2S hW2escape hcross)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
