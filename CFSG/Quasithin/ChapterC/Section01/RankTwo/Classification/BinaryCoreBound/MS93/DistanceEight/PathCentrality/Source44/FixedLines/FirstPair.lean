module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.FixedLines.Selections

/-!
# The residual first terminal image

For a critical pair ending at the retained predecessor, a first-edge fixed
line not normalized by the terminal Z-layer cannot have critical image four.
The proved marked pairing would identify that line with the critical
commutator, putting it in the predecessor Z-layer. Critical minimality then
makes the terminal layer centralize it, a contradiction.

The actual simultaneous first selection consequently has image two. This
records precisely the residual case; it does not assume the source's ensuing
fixed-line identification or claim the terminal exclusion has been completed.
Source: Meierfrankenfeld--Stellmacher (1993), printed p.892.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

 theorem selected_pair_index_two (common : CommonFacts R source geometry)
    (hb : 4<geometry.b R) {a c : Vertex R} (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {d t : Vertex R}
    (p : CriticalPath R geometry d w.predecessor)
    (hdt : Adjacent R d t) (hct : Adjacent R c t)
    (hnot : ¬Z R n.vertex≤normalizer (edgeFixedNatural (R:=R) d t)) :
    (Q R w.predecessor).relIndex (Z R d)=2 := by
  apply (critical_Z_index_two_or_four common p).resolve_right
  intro hi
  have hid : (Q R d).relIndex (Z R w.predecessor)=4 :=
    (critical_Z_index_reciprocity common p).symm.trans hi
  have hcv : (cosetGraph R).dist c w.predecessor=geometry.b R-2 := by
    change (cosetGraph R).dist c (w.path.walk.getVert (w.path.walk.length-2))=_
    rw [w.path.dist_start (Nat.sub_le _ _),w.path.length_eq_b]
  have hlen : (cosetGraph R).dist d w.predecessor=geometry.b R :=
    p.shortest.symm.trans p.length_eq_b
  have hdist : (cosetGraph R).dist t w.predecessor+1=
      (cosetGraph R).dist d w.predecessor := by
    have htc : (cosetGraph R).dist t c=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (adjacent_symm R hct))
    have hdt' : (cosetGraph R).dist d t=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)
    have hu := (cosetGraph_connected R).dist_triangle (u:=t) (v:=c) (w:=w.predecessor)
    have hl := (cosetGraph_connected R).dist_triangle (u:=d) (v:=t) (w:=w.predecessor)
    rw [htc,hcv] at hu
    rw [hdt',hlen] at hl
    omega
  have heq := critical_commutator_eq_edgeFixedNatural common hb p hdt hdist hid
  have hF : edgeFixedNatural (R:=R) d t≤Z R w.predecessor := by
    rw [← heq]
    exact le_normalizer_iff_commutator_le_right.mp
      ((p.reverse common).endpoint_Z_le_start_stabilizer (by omega) |>.trans (Z_normalized R _))
  have hZQ : Z R n.vertex≤Q R w.predecessor := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ n.color)
    rw [geometry.distance_constant _ n.color,SimpleGraph.dist_comm,n.distance]
    change 2<geometry.b R
    omega
  have hcomm : Z R n.vertex≤centralizer (Z R w.predecessor : Set (FreeAmalgam R)) :=
    hZQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes w.predecessor w.predecessor_color)))
  exact hnot ((hcomm.trans (centralizer_le hF)).trans (Subgroup.centralizer_le_normalizer _))

 theorem first_selection_index_two (common : CommonFacts R source geometry)
    (hb : 4<geometry.b R) {a c : Vertex R} (ha : color R a=false)
    (hd : (cosetGraph R).dist a c=2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hnot : ¬edgeFixedNatural (R:=R) w.backward t≤fixedCore R c) :
    ∃g∈stabilizer R c,
      (¬Z R n.vertex≤normalizer
        (edgeFixedNatural (R:=R) (act R g w.backward) (act R g t))) ∧
      (¬Z R n.vertex≤normalizer (Z R (act R g w.backward)⊔Z R c : Subgroup (FreeAmalgam R))) ∧
      (Q R w.predecessor).relIndex (Z R (act R g w.backward))=2 := by
  obtain ⟨g,hg,hgF,hgJ,⟨p⟩⟩ := first_selection common hb ha hd w n hdt hct hnot
  refine ⟨g,hg,hgF,hgJ,selected_pair_index_two common hb w n p ?_ ?_ hgF⟩
  · exact (adjacent_act_iff R g w.backward t).mpr hdt
  · have hgc : act R g c=c := hg
    simpa only [hgc] using (adjacent_act_iff R g c t).mpr hct

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
