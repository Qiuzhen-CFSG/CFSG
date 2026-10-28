module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.TerminalNeighbor
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.MarkedPairing
public import Theory.Representation.PSL3Two.FourGroupGeometry.SelfCentralizing
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The critical pairs forced by terminal nonnormalization

A terminal Z-layer has an elementary four-group image in the actual local
SL3(2) quotient. That image is self-centralizing. A subgroup commuting with
the opposite Z-layer consequently lies in its product with the exact local
kernel. The critical endpoint then normalizes its join with the opposite
Z-layer. Contraposition supplies the two-step noncontainment; graph distance
and critical minimality construct the actual replacement critical pair.

The final consumer applies this to the original backward witness and its
constructed terminal neighbor. It supplies the critical-pair implication
used by both terminal normalizer selections, without asserting the remaining
fixed-line choices or the final contradiction.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.4.1), printed p.892, final two paragraphs.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
open Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

 theorem critical_four_image_normalizes_join
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {c lam : Vertex R} (p : CriticalPath R geometry c lam)
    (hi : (Q R lam).relIndex (Z R c)=4)
    (A : Subgroup (FreeAmalgam R))
    (hA : A≤stabilizer R lam) (hAc : A≤stabilizer R c)
    (hcomm : A≤centralizer (Z R c : Set (FreeAmalgam R))) :
    Z R lam≤normalizer (A⊔Z R c : Subgroup (FreeAmalgam R)) := by
  let S := stabilizer R lam
  let π := localProjection source lam p.end_color
  have hZ : Z R c≤S := (p.reverse common).endpoint_Z_le_start_stabilizer (by omega)
  have hZc : Z R lam≤stabilizer R c := p.endpoint_Z_le_start_stabilizer (by omega)
  let E := ((Z R c).subgroupOf S).map π
  let := geometry.Z_elementary (by omega) c p.start_color
  let := IsElementaryAbelian.subgroupOf (p:=2) hZ
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map π
  have hcard : Nat.card E=4 := by
    rw [show Nat.card E= (Q R lam).relIndex (Z R c) from ?_,hi]
    rw [← relIndex_ker,localProjection_kernel,localKernel,subgroupOf,relIndex_comap,
      map_subgroupOf_eq_of_le hZ]
  have hmap : (A.subgroupOf S).map π ≤ E := by
    rw [← BinaryLinearThree.FourGroupGeometry.fourGroup_centralizer E hcard]
    rintro _ ⟨a,ha,rfl⟩ _ ⟨z,hz,rfl⟩
    rw [← map_mul,← map_mul]
    apply congrArg π
    exact Subtype.ext (hcomm ha z hz)
  have hbound : A≤Q R lam⊔Z R c := by
    have hle := map_le_map_iff.mp hmap
    rw [localProjection_kernel] at hle
    have hh := map_mono (f:=S.subtype) hle
    rwa [map_subgroupOf_eq_of_le hA,Subgroup.map_sup,
      map_subgroupOf_eq_of_le hZ,map_subgroupOf_eq_of_le (show Q R lam≤S from fun _ hx=>hx.1),
      sup_comm] at hh
  have hZnormal : Z R lam≤normalizer (Z R c) := hZc.trans (Z_normalized R c)
  have heq : ⁅Z R lam,Z R c⁆=⁅Z R lam,Q R lam⊔Z R c⁆ :=
    commutator_eq_of_centralizing_sup rfl
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes lam p.end_color)))
      (hZ.trans (Z_normalized R lam))
  have hAZ : ⁅A,Z R lam⁆≤Z R c := by
    rw [commutator_comm]
    exact ((commutator_mono le_rfl hbound).trans_eq heq.symm).trans
      (le_normalizer_iff_commutator_le_right.mp hZnormal)
  let Sc := stabilizer R c
  let := geometry.Z_normal c
  have hsmall : ⁅A.subgroupOf Sc,(Z R lam).subgroupOf Sc⁆≤(Z R c).subgroupOf Sc := by
    intro x hx
    have hm := mem_map_of_mem Sc.subtype hx
    rw [map_commutator,map_subgroupOf_eq_of_le hAc,map_subgroupOf_eq_of_le hZc] at hm
    exact hAZ hm
  have hn := le_normalizer_sup_of_commutator_le (A.subgroupOf Sc)
    ((Z R lam).subgroupOf Sc) (A.subgroupOf Sc) ((Z R c).subgroupOf Sc) le_rfl hsmall
  have hm := (map_mono (f:=Sc.subtype) hn).trans
    ((A.subgroupOf Sc⊔(Z R c).subgroupOf Sc).le_normalizer_map Sc.subtype)
  rwa [map_subgroupOf_eq_of_le hZc,Subgroup.map_sup,
    map_subgroupOf_eq_of_le hAc,map_subgroupOf_eq_of_le (Z_le_stabilizer R c)] at hm

 theorem terminal_noncontainment_of_join_nonnormalization
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a=false)
    (hd : (cosetGraph R).dist a c=2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {d : Vertex R}
    (hdc : (cosetGraph R).dist d c=2)
    (hn : ¬Z R n.vertex≤normalizer (Z R d⊔Z R c : Subgroup (FreeAmalgam R))) :
    ¬Z R d≤Q R w.predecessor := by
  intro h
  have hcol : color R d=false :=
    (color_eq_of_dist_even R d c (by rw [hdc]; decide)).trans w.path.start_color
  have hZQ : Z R d≤Q R c := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hcol)
    rw [geometry.distance_constant d hcol,hdc]
    change 2 < geometry.b R
    omega
  have hlam : Z R d≤stabilizer R n.vertex :=
    h.trans (Q_le_stabilizer_of_dist_two R w.predecessor n.vertex w.predecessor_color n.distance)
  exact hn (critical_four_image_normalizes_join common hb (n.criticalPath common hb ha hd)
    (n.pairing common hb ha hd).2.2.1 (Z R d) hlam (hZQ.trans (fun _hx hx=>hx.1))
    (hZQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes c w.path.start_color)))))

 theorem terminal_new_critical_pair
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a=false)
    (hd : (cosetGraph R).dist a c=2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {d : Vertex R}
    (hdc : (cosetGraph R).dist d c=2)
    (hn : ¬Z R n.vertex≤normalizer (Z R d⊔Z R c : Subgroup (FreeAmalgam R))) :
    Nonempty (CriticalPath R geometry d w.predecessor) := by
  have hcol : color R d=false :=
    (color_eq_of_dist_even R d c (by rw [hdc]; decide)).trans w.path.start_color
  have hnot := terminal_noncontainment_of_join_nonnormalization common hb ha hd w n hdc hn
  have hmin := criticalDistance_le R d (geometry.exists_critical d hcol) hnot
  rw [geometry.distance_constant d hcol] at hmin
  change geometry.b R ≤ (cosetGraph R).dist d w.predecessor at hmin
  have hmax := (cosetGraph_connected R).dist_triangle (u:=d) (v:=c) (w:=w.predecessor)
  have hcv := w.path.dist_start (Nat.sub_le w.path.walk.length 2)
  change (cosetGraph R).dist c w.predecessor=w.path.walk.length-2 at hcv
  rw [hdc,hcv,w.path.length_eq_b] at hmax
  have hdist : (cosetGraph R).dist d w.predecessor=geometry.b R := by omega
  exact ⟨CriticalPath.ofPair hcol ⟨hdist.trans (geometry.distance_constant d hcol).symm,hnot⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
