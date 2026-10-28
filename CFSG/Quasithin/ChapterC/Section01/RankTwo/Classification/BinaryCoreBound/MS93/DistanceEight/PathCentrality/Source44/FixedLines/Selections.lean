module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.FixedLines.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# The two simultaneous terminal selections in MS93 (4.4.1)

Source (2.1)(vii) moves both the natural fixed line and the Z-product with
one conjugator. The first selection retains that local conjugator. The
second retains a single transporter of the reversed ordered pair. Each
failure to normalize the product constructs the corresponding actual
critical path by the terminal order-four image calculation.

The first selection is under the source contrary assumption that the fixed
line is not contained in D. These choices do not assert the subsequent
fixed-line/critical-commutator identifications or the final contradiction.
Source: Meierfrankenfeld--Stellmacher (1993), printed p.892, last two
paragraphs of the proof of (4.4.1).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

 theorem first_selection (common : CommonFacts R source geometry)
    (hb : 4<geometry.b R) {a c : Vertex R} (ha : color R a=false)
    (hd : (cosetGraph R).dist a c=2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hnot : ¬edgeFixedNatural (R:=R) w.backward t≤fixedCore R c) :
    ∃g∈stabilizer R c,
      (¬Z R n.vertex≤normalizer
        (edgeFixedNatural (R:=R) (act R g w.backward) (act R g t))) ∧
      (¬Z R n.vertex≤normalizer (Z R (act R g w.backward)⊔Z R c : Subgroup (FreeAmalgam R))) ∧
      Nonempty (CriticalPath R geometry (act R g w.backward) w.predecessor) := by
  have hcol := w.backward_color ha
  have hcard := fixed_line_card common hb ha hd w n hcol hdt
  have hZQ : Z R w.backward≤Q R c := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hcol)
    rw [geometry.distance_constant _ hcol,w.backward_distance hd]
    change 2<geometry.b R
    omega
  have hFQ : edgeFixedNatural (R:=R) w.backward t≤Q R c :=
    inf_le_left.trans ((U_le_Z R w.backward).trans hZQ)
  have hFnot : ¬((edgeFixedNatural (R:=R) w.backward t).subgroupOf
      (stabilizer R c)).Normal := fun hn =>
    hnot (line_normal_implies_fixed hFQ hcard hn)
  obtain ⟨hFe,hFn⟩ := fixed_line_edge (by omega : 2<geometry.b R) hcol hdt
  obtain ⟨hJe,hJn⟩ := two_step_join_edge_normal (by omega : 2<geometry.b R)
    hcol w.path.start_color hdt hct
  obtain ⟨g,hg,hgF,hgJ⟩ := source_2_1_vii R c n.vertex t w.path.start_color hct
    (edgeFixedNatural (R:=R) w.backward t) (Z R w.backward⊔Z R c)
    hFe hJe hFn hJn hFnot (backward_join_nonnormal common hb ha hd w).1.2
    (critical_conjugates_sup_edge common (n.criticalPath common hb ha hd) hct)
  have hgc : act R g c=c := hg
  rw [← fixed_line_act] at hgF
  rw [Subgroup.map_sup,← Z_act,← Z_act,hgc] at hgJ
  have hdist : (cosetGraph R).dist (act R g w.backward) c=2 := by
    simpa only [hgc,w.backward_distance hd] using dist_act R g w.backward c
  exact ⟨g,hg,hgF,hgJ,terminal_new_critical_pair common hb ha hd w n hdist hgJ⟩



 theorem second_selection (common : CommonFacts R source geometry)
    (hb : 4<geometry.b R) {a c : Vertex R} (ha : color R a=false)
    (hd : (cosetGraph R).dist a c=2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t) :
    ∃g : FreeAmalgam R, act R g w.backward=c ∧
      (¬Z R n.vertex≤normalizer (edgeFixedNatural (R:=R) c (act R g t))) ∧
      (¬Z R n.vertex≤normalizer (Z R (act R g c)⊔Z R c : Subgroup (FreeAmalgam R))) ∧
      Nonempty (CriticalPath R geometry (act R g c) w.predecessor) := by
  obtain ⟨u,hu⟩ := exists_mVertex_of_color R (w.backward_color ha)
  obtain ⟨v,hv⟩ := exists_mVertex_of_color R w.path.start_color
  let h := u⁻¹*v
  have hhc : act R h w.backward=c := by rw [hu,act_mVertex,mul_inv_cancel_left,← hv]
  let d := act R h c
  let s := act R h t
  have hds : Adjacent R d s := (adjacent_act_iff R h c t).mpr hct
  have hcs : Adjacent R c s := by
    simpa only [hhc] using (adjacent_act_iff R h w.backward t).mpr hdt
  have hcol : color R d=false := (action_preserves_color R h c).trans w.path.start_color
  have hdist : (cosetGraph R).dist d c=2 := by
    simpa only [d,hhc,SimpleGraph.dist_comm] using
      (dist_act R h c w.backward).trans (by rw [SimpleGraph.dist_comm]; exact w.backward_distance hd)
  have hcard := fixed_line_card common hb ha hd w n w.path.start_color hcs
  have hnF := natural_line_not_normal common w.path.start_color
    (show edgeFixedNatural (R:=R) c s≤U R c from inf_le_left) hcard
  obtain ⟨hFe,hFn⟩ := fixed_line_edge (by omega : 2<geometry.b R) w.path.start_color hcs
  obtain ⟨hJe,hJn⟩ := two_step_join_edge_normal (by omega : 2<geometry.b R)
    hcol w.path.start_color hds hcs
  have hQG : Q R s≤stabilizer R c := fun _ hx=>hx.2 c (adjacent_symm R hcs)
  have hJnot : ¬((Z R d⊔Z R c).subgroupOf (stabilizer R c)).Normal := by
    intro hn
    have hh := (normal_subgroupOf_iff_le_normalizer (hJe.trans hQG)).mp hn
    have hj : Z R d⊔Z R c = (Z R c⊔Z R w.backward).map (MulAut.conj h⁻¹).toMonoidHom := by
      rw [Subgroup.map_sup,← Z_act,← Z_act,hhc]
    have hs : stabilizer R c = (stabilizer R w.backward).map (MulAut.conj h⁻¹).toMonoidHom := by
      rw [← stabilizer_act,hhc]
    rw [hj,hs,← Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj h⁻¹).bijective,
      Subgroup.map_le_map_iff_of_injective (MulAut.conj h⁻¹).injective] at hh
    exact (backward_join_nonnormal common hb ha hd w).2.2
      (normal_subgroupOf_of_le_normalizer hh)
  obtain ⟨k,hk,hkF,hkJ⟩ := source_2_1_vii R c n.vertex s w.path.start_color hcs
    (edgeFixedNatural (R:=R) c s) (Z R d⊔Z R c)
    hFe hJe hFn hJn hnF hJnot
    (critical_conjugates_sup_edge common (n.criticalPath common hb ha hd) hcs)
  have hkc : act R k c=c := hk
  rw [← fixed_line_act,hkc] at hkF
  rw [Subgroup.map_sup,← Z_act,← Z_act,hkc] at hkJ
  have hdist' : (cosetGraph R).dist (act R k d) c=2 := by
    simpa only [hkc,hdist] using dist_act R k d c
  refine ⟨h*k,?_,?_,?_,?_⟩
  · rw [act_mul,hhc,hkc]
  · simpa only [act_mul,s] using hkF
  · simpa only [act_mul,d] using hkJ
  · simpa only [act_mul,d] using
      terminal_new_critical_pair common hb ha hd w n hdist' hkJ

 theorem second_selection_core_transport (common : CommonFacts R source geometry)
    (hb : 4<geometry.b R) {a c : Vertex R} (ha : color R a=false)
    (hd : (cosetGraph R).dist a c=2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hcore : edgeFixedNatural (R:=R) w.backward t≤fixedCore R c) :
    ∃g : FreeAmalgam R, act R g w.backward=c ∧
      (¬Z R n.vertex≤normalizer (edgeFixedNatural (R:=R) c (act R g t))) ∧
      (¬Z R n.vertex≤normalizer (Z R (act R g c)⊔Z R c : Subgroup (FreeAmalgam R))) ∧
      Nonempty (CriticalPath R geometry (act R g c) w.predecessor) ∧
      edgeFixedNatural (R:=R) c (act R g t)≤fixedCore R (act R g c) := by
  obtain ⟨g,hg,hgF,hgJ,hp⟩ := second_selection common hb ha hd w n hdt hct
  refine ⟨g,hg,hgF,hgJ,hp,?_⟩
  have hh := map_mono (f:=(MulAut.conj g⁻¹).toMonoidHom) hcore
  rwa [← fixed_line_act,← Escape.PairingControl.FirstPairing.fixedCore_act,hg] at hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
