module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightResidualTransport
import all Stellmacher.PushingUp.DistanceTwoCore

/-!
# The geometric boundary of full relative-mover comparisons

In the free holomorph amalgam, distinct component neighbors of an edge
vertex have stabilizer intersection equal to its actual edge core. In the
surviving image-eight branch, the full relative-normalizer mover escapes
that core: its quotient order is eight, whereas its intersection with the
edge core has quotient order four. It therefore cannot be contained in the
other component stabilizer. Equality of two such relative movers forces
the component vertices to coincide.

The terminal relative-mover equality assumed by EightResidualTransport is
consequently impossible on a genuine critical path above distance four.
The literal restricted original radical likewise fails to lie in any other
component stabilizer at the base edge. These are statements about the
existing graph and maps, with both covers and central attachments retained.

Source comparison: MS93 (2.1)(ii), printed p.855, identifies T_beta with
the actual edge stabilizer, here Q_beta. Its (5.5)--(5.8), printed
pp.915--920, compares movers for this same actor T_beta. Equality of the two full relative
normalizers' movers in the free amalgam is not that comparison. The earlier
conditional APIs remain valid, but their terminal equalities cannot be
discharged in this branch. A source application must prove the common-actor
transport or use the actual edge movers; this obstruction does not refute
the source theorem or prove the final distance bound.

The midpoint argument reuses the generic Bass--Serre normal-form lemma in
Stellmacher.PushingUp.DistanceTwoCore through an intentional private import.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightRelativeBoundary
open EightPairedNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The full relative-normalizer mover strictly escapes the actual edge core. -/
theorem relativeMover_not_le_edge_knownSimple (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ¬ relativeMover (d := d) a t ≤ Q d.radical t := by
  obtain ⟨J,_,hJ,_,_,hi,_,_,_⟩ :=
    SylowSmallMovers.edge_normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) hb ha hat
  obtain ⟨hE,_,_,_,hEi,_⟩ := EightSmallMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb ha hat
  intro hle
  have heq : SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4 = J := by
    rw [hE,inf_eq_right.mpr hle]
    exact hJ
  rw [heq,hi] at hEi
  contradiction

include e hz hn in
/-- Distinct component neighbors have intersection equal to the edge core.
A relative-normalizer mover therefore cannot lie in the opposite stabilizer. -/
theorem relativeMover_not_le_neighbor_knownSimple (hb : 4 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) (hne : c ≠ a) :
    ¬ relativeMover (d := d) a t ≤ stabilizer d.radical c := by
  have horbit : Stellmacher.PushingUp.InMVertexOrbit d.radical a := by
    obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical ha
    exact ⟨g,by simpa only [act_mVertex,one_mul] using hg⟩
  have hmid := Stellmacher.PushingUp.stabilizer_inf_le_midpoint d.radical a t c
    horbit hat (adjacent_symm d.radical hct) hne
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases ht : color d.radical t <;> simp_all
  intro hle
  apply relativeMover_not_le_edge_knownSimple (e := e) (hz := hz) (hn := hn) hb ha hat
  have hJa : relativeMover (d := d) a t ≤ stabilizer d.radical a :=
    (SmallMover.join_le _ _ _ _).trans inf_le_right
  rw [Q_h_eq_edge d.radical ht hat]
  exact le_inf hJa ((le_inf hJa hle).trans hmid)

include e hz hn in
/-- Equality of the full relative movers across an edge forces the two
component vertices to coincide; it is not the source's common-actor equality. -/
theorem relativeMover_eq_iff_knownSimple (hb : 4 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    relativeMover (d := d) c t = relativeMover (d := d) a t ↔ c = a := by
  constructor
  · intro heq
    by_contra hne
    apply relativeMover_not_le_neighbor_knownSimple (e := e) (hz := hz) (hn := hn)
      hb ha hat hct hne
    rw [←heq]
    exact (SmallMover.join_le _ _ _ _).trans inf_le_right
  · rintro rfl
    rfl

include e hz hn in
/-- In particular the final mover-equality premise in EightResidualTransport
cannot hold on a genuine critical path above distance four. -/
theorem terminal_relativeMovers_ne_knownSimple (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    relativeMover (d := d) z (p.walk.getVert (p.walk.length-1)) ≠
      relativeMover (d := d) (p.walk.getVert (p.walk.length-2))
        (p.walk.getVert (p.walk.length-1)) := by
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hct : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hzt : Adjacent d.radical z (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  intro heq
  have hv := (relativeMover_eq_iff_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hcol hct hzt).mp heq
  have hd := p.dist_end (p.walk.length-2)
  rw [←hv,SimpleGraph.dist_self] at hd
  omega

include e hz hn in
/-- The literal restricted original radical also escapes every other component
stabilizer at the base edge, although it normalizes the entire edge core. -/
theorem original_radical_not_le_other_neighbor_knownSimple
    (hb : 4 < replacementDistance h d)
    {c : Vertex d.radical} (hct : Adjacent d.radical c (beta d.radical))
    (hne : c ≠ alpha d.radical) :
    ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      stabilizer d.radical c := by
  intro hle
  apply relativeMover_not_le_neighbor_knownSimple (e := e) (hz := hz) (hn := hn)
    hb rfl (base_adjacent d.radical) hct hne
  apply (SmallMover.join_le _ _ _ _).trans
  exact (SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb).le.trans hle

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightRelativeBoundary
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
