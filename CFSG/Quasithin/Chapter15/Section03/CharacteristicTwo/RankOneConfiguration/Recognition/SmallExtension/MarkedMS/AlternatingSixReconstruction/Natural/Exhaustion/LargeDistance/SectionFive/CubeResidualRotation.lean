module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePredecessorSlice

/-!
# Residual rotation of the trapped three-pair obstruction

Assume an original nonsylow replacement has critical distance greater than
four and a radius trapped in its second predecessor core. The uniform
small-slice theorem then identifies every reverse kernel with its predecessor
slice. Its full core commutator is central in the predecessor stabilizer.
Moving the last edge to the previous edge by that residual preserves each
nonzero backward-kernel commutator. Nonvanishing gives a genuine new critical
path with its first edge and all overlapping vertices retained. Uniform
smallness makes both of its critical images have order two, so the selected
commutator is the full endpoint displacement on both the full seed and the
moving cover, after transport by the same residual element.

The literal consumer selects an eligible neighbor and the cubic pair itself.
It transports the trapped radius through either orientation of that same
pair, excludes the unrotated backward-path alternative, and applies the
rotation to the retained noncentral line. Both end-edge seeds, both endpoint
seeds, the generating equation, neighbor transporter and cubic are preserved.
No nonzero line, slice index, radical image or residual transporter is assumed
in this application. The radius-trapping hypothesis remains explicit.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the residual rotation in (5.8), printed pp.919--920.
The remaining source comparison is alignment of this selected line with the
original critical line times the endpoint center. Without that alignment,
equality of fixed-hyperplane and whole-cover displacement is possible for
disjoint transpositions in the three-pair group. Neither this module nor its
consumer claims the final trapped-radius or large-distance contradiction.
Both covers and their full central attachments remain throughout.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

include h in
private theorem residual_neighbor_transporter
    {c t v : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t) (hcv : Adjacent d.radical c v) :
    ∃ k ∈ Ltilde d.radical c, act d.radical k t = v := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨l,hl,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hl) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  have hgen : Ltilde d.radical c ⊔ Q d.radical t = stabilizer d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
      rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
      simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
    · rw [hg.1] at hcol
      cases hcol
  have hn : Q d.radical t ≤ normalizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hxc : x⁻¹ ∈ stabilizer d.radical c :=
      (stabilizer d.radical c).inv_mem (hx.2 _ (adjacent_symm d.radical hct))
    have hh := Ltilde_act d.radical x⁻¹ c
    rw [inv_inv,show act d.radical x⁻¹ c = c from hxc] at hh
    exact hh.symm
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical c hct hcv
  have hprod : g ∈ (Q d.radical t : Set (FreeAmalgam d.radical)) *
      (Ltilde d.radical c : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hn,
      sup_comm (Q d.radical t) (Ltilde d.radical c),hgen]
    exact hg
  obtain ⟨q,hq,k,hk,rfl⟩ := hprod
  refine ⟨k,hk,?_⟩
  have hqt : act d.radical q t = t := hq.1
  simpa only [act_mul,hqt] using hgt

include e hz hn in
/-- The residual rotation of a nonzero backward kernel is a critical path
with both critical images of order two under the trapped-radius hypothesis. -/
theorem nonsylow_trapped_residual_critical_path_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a₀ a₁ : Vertex d.radical}
    (p₀ : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (htrapped : V d.radical a₀ ≤ Q d.radical (p₀.walk.getVert (p₀.walk.length-2)))
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hD : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≠ ⊥) :
    ∃ k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2)),
      act d.radical k (p.walk.getVert (p.walk.length-1)) = p.walk.getVert (p.walk.length-3) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical k a'),
        q.walk.getVert 1=t ∧
        (∀ i ≤ p.walk.length-3, q.walk.getVert (i+2)=p.walk.getVert i) ∧
        (Q d.radical (act d.radical k a')).relIndex (Z d.radical c)=2 ∧
        (Q d.radical c).relIndex (Z d.radical (act d.radical k a'))=2 ∧
        let H := ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆
        Nat.card H=2 ∧
        H ≤ centralizer (stabilizer d.radical (p.walk.getVert (p.walk.length-2)) :
          Set (FreeAmalgam d.radical)) ∧
        ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ c)⁆=H ∧
        ⁅Z d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆=H ∧
        ⁅U d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆=H := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hp := nonsylow_trapped_radius_predecessor_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns p₀ htrapped p
  have htransport (k : FreeAmalgam d.radical)
      (hk : k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2))) :
      ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ c)⁆ =
        ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ := by
    rw [Z_act,inv_inv]
    exact nonsylow_trapped_radius_residual_transport_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 hns p₀ htrapped p _ hD k hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hpred : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hprev : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-3)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-3) (by omega)
    rw [show p.walk.length-3+1=p.walk.length-2 by omega] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  obtain ⟨k,hk,hkt⟩ := residual_neighbor_transporter (h := h) hcol hpred hprev
  have hescape : ¬ Z d.radical c ≤ Q d.radical (act d.radical k a') := by
    intro hh
    have hm : Z d.radical (act d.radical k⁻¹ c) ≤ Q d.radical a' := by
      calc
        _ = (Z d.radical c).map (MulAut.conj k).toMonoidHom := by rw [Z_act,inv_inv]
        _ ≤ (Q d.radical (act d.radical k a')).map (MulAut.conj k).toMonoidHom := map_mono hh
        _ = Q d.radical (act d.radical k⁻¹ (act d.radical k a')) := by
          simpa only [inv_inv] using (Q_act d.radical k⁻¹ (act d.radical k a')).symm
        _ = Q d.radical a' := by rw [←act_mul,mul_inv_cancel,act_one]
    apply hne
    rw [←htransport k hk]
    exact le_bot_iff.mp ((commutator_mono inf_le_left hm).trans_eq
      (Z_centralizes_Q d.radical a' p.end_color))
  have hcfalse : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hlast : Adjacent d.radical (p.walk.getVert (p.walk.length-1)) a' := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hend : (cosetGraph d.radical).Adj (p.walk.getVert (p.walk.length-3)) (act d.radical k a') := by
    rw [←hkt]
    exact (cosetGraph_adj d.radical _ _).mpr
      ((adjacent_act_iff d.radical k _ _).mpr hlast)
  let w₀ : (cosetGraph d.radical).Walk c a :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  let w₁ := (p.walk.take (p.walk.length-3)).concat hend
  let w := w₀.append w₁
  have hw₀ : w₀.length = 2 := rfl
  have hw : w.length = p.walk.length := by
    simp only [w,w₁,SimpleGraph.Walk.length_append,hw₀,SimpleGraph.Walk.length_concat,
      SimpleGraph.Walk.take_length,inf_eq_left.mpr (Nat.sub_le _ _)]
    omega
  have hmin := criticalDistance_le d.radical c ((replacementGeometry h d).exists_critical c hcfalse) hescape
  rw [(replacementGeometry h d).distance_constant c hcfalse] at hmin
  have hdist : (cosetGraph d.radical).dist c (act d.radical k a') = replacementDistance h d := by
    have hh := SimpleGraph.dist_le w
    rw [hw,p.length_eq_b] at hh
    exact le_antisymm hh hmin
  let q : CriticalPath d.radical (replacementGeometry h d) c (act d.radical k a') :=
    ⟨hcfalse,w,hw.trans (p.length_eq_b.trans hdist.symm),by
      refine ⟨?_,hescape⟩
      rw [(replacementGeometry h d).distance_constant c hcfalse]
      exact hdist⟩
  have hq := nonsylow_trapped_radius_predecessor_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns p₀ htrapped q
  let qr := CriticalPath.ofPair (geometry := replacementGeometry h d) q.end_color
    (critical_reverse_pair s hc q)
  have hqrsmall : (Q d.radical c).relIndex (Z d.radical (act d.radical k a')) < 4 := by
    rw [hq.2.2.1]
    decide
  let H := ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆
  let D := ⁅Z d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆
  let E := ⁅U d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆
  have hcardD : Nat.card D=2 := by
    dsimp only [D]
    rw [←card_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom)
      (MulAut.conj k⁻¹).injective,map_commutator]
    have hZ : (Z d.radical (act d.radical k⁻¹ c)).map (MulAut.conj k⁻¹).toMonoidHom =
        Z d.radical c := by
      rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
    rw [←Z_act,hZ]
    exact small_critical_commutator_card s hc qr hqrsmall
  have hED : E=D := by
    apply (map_injective (f := (MulAut.conj k⁻¹).toMonoidHom) (MulAut.conj k⁻¹).injective)
    dsimp only [E,D]
    rw [map_commutator,map_commutator,←U_act,←Z_act,←Z_act,←act_mul,inv_mul_cancel,act_one]
    exact small_critical_moving_commutator_eq s hc qr hqrsmall
  have hHD : H ≤ D := by
    rw [show H=⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ c)⁆
      from (htransport k hk).symm]
    exact commutator_mono inf_le_left le_rfl
  let : Finite D := Nat.finite_of_card_ne_zero (by rw [hcardD]; decide)
  let : Finite H := Finite.of_injective (inclusion hHD) (inclusion_injective _)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hne
  have hHcard : Nat.card H=2 := by
    have hh := card_le_of_le hHD
    omega
  have heq : H=D := eq_of_le_of_card_ge hHD (by rw [hHcard,hcardD])
  refine ⟨k,hk,hkt,q,?_,?_,hq.2.1,hq.2.2.1,hHcard,?_,htransport k hk,heq.symm,hED.trans heq.symm⟩
  · change (w₀.append w₁).getVert 1=t
    simp only [SimpleGraph.Walk.getVert_append,hw₀,show 1<2 from by decide,ite_true,
      w₀,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]
  · intro i hi
    change (w₀.append w₁).getVert (i+2)=p.walk.getVert i
    rw [SimpleGraph.Walk.getVert_append,hw₀,if_neg (by omega),Nat.add_sub_cancel]
    change ((p.walk.take (p.walk.length-3)).concat hend).getVert i=p.walk.getVert i
    rw [SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append']
    rw [if_pos (by simpa only [SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _)] using hi),SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hi]
  · exact (commutator_mono le_rfl hD).trans hp.2.2.2.2.2

include e hz hn in
/-- On a trapped nonsylow replacement, choose the eligible seed and the
same cubic pair internally. The retained noncentral obstruction becomes the
full displacement on the residual-rotated critical path. -/
theorem nonsylow_trapped_radius_rotated_line_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (htrapped : V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    ∃ delta, Adjacent d.radical delta (p.walk.getVert 1) ∧
      (¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        ∃ g ∈ stabilizer d.radical (alpha d.radical),
          act d.radical g (p.walk.getVert 1)=t ∧
          Adjacent d.radical (act d.radical g delta) t ∧
          ∃ x ∈ Ltilde d.radical (alpha d.radical),
            x ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
            x^3 ∈ Q d.radical (alpha d.radical) ∧
            Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
              stabilizer d.radical (alpha d.radical) ∧
            ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
              ((z=a' ∧ ∀ i, q.walk.getVert i=p.walk.getVert i) ∨
                (z=act d.radical x a' ∧ ∀ i, q.walk.getVert i=act d.radical x (p.walk.getVert i))) ∧
              (¬ Z d.radical z ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
                Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) ∧
              let H := ⁅Z d.radical z ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical g delta)⁆
              Nat.card H=2 ∧
              H ≤ Z d.radical (act d.radical g delta) ⊓ Z d.radical z ∧
              H ≤ Z d.radical t ⊓ Z d.radical (q.walk.getVert (q.walk.length-1)) ∧
              H ≤ Z d.radical (alpha d.radical) ⊓ Z d.radical (q.walk.getVert (q.walk.length-2)) ∧
              H ≤ centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
              (¬ H ≤ centralizer (stabilizer d.radical (act d.radical g delta) : Set (FreeAmalgam d.radical))) ∧
              H ≤ centralizer (stabilizer d.radical (q.walk.getVert (q.walk.length-2)) : Set (FreeAmalgam d.radical)) ∧
              ∃ k ∈ Ltilde d.radical (q.walk.getVert (q.walk.length-2)),
                act d.radical k (q.walk.getVert (q.walk.length-1))=q.walk.getVert (q.walk.length-3) ∧
                ∃ r : CriticalPath d.radical (replacementGeometry h d)
                    (act d.radical g delta) (act d.radical k z),
                  r.walk.getVert 1=t ∧
                  (∀ i ≤ q.walk.length-3, r.walk.getVert (i+2)=q.walk.getVert i) ∧
                  (Q d.radical (act d.radical k z)).relIndex (Z d.radical (act d.radical g delta))=2 ∧
                  (Q d.radical (act d.radical g delta)).relIndex (Z d.radical (act d.radical k z))=2 ∧
                  ⁅Z d.radical z ⊓ Q d.radical (alpha d.radical),
                    Z d.radical (act d.radical k⁻¹ (act d.radical g delta))⁆=H ∧
                  ⁅Z d.radical z,Z d.radical (act d.radical k⁻¹ (act d.radical g delta))⁆=H ∧
                  ⁅U d.radical z,Z d.radical (act d.radical k⁻¹ (act d.radical g delta))⁆=H := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨delta,hdelta,hel⟩ := exists_eligible_neighbor_at_edge s hc hb rfl ha1
  have hp := nonsylow_trapped_radius_predecessor_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns p htrapped p
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [hp.2.1]
    decide
  obtain ⟨t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,hgen,z,q,hq,hqs,hnorm,hcases⟩ :=
    nonsylow_small_backward_line_obstruction_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 hns p hsmall hdelta hel
  have hdist : (cosetGraph d.radical).dist (act d.radical g delta) (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist (act d.radical g delta) t=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical)=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := act d.radical g delta) (v := t) (w := alpha d.radical)
  have hVq : V d.radical (alpha d.radical) ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    have hlen : q.walk.length=p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rcases hq with ⟨hz,hverts⟩ | ⟨hz,hverts⟩
    · rw [hlen,hverts]
      exact htrapped
    · rw [hlen,hverts,Q_act]
      have hV : (V d.radical (alpha d.radical)).map (MulAut.conj x⁻¹).toMonoidHom =
          V d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical _
          ((stabilizer d.radical (alpha d.radical)).inv_mem (Ltilde_le_stabilizer _ hx)))
      rw [←hV]
      exact map_mono htrapped
  have hD : Z d.radical (act d.radical g delta) ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) :=
    ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)).trans hVq
  rcases hcases with ⟨v,_,_⟩ | ⟨hbad,hcard,hseed,hedge,hmiddle,hcent,hncent⟩
  · exact False.elim (v.critical.2 hD)
  · let H := ⁅Z d.radical z ⊓ Q d.radical (alpha d.radical),Z d.radical (act d.radical g delta)⁆
    have hHcard : Nat.card H=2 := by
      dsimp only [H]
      rw [commutator_comm]
      exact hcard
    have hne : H ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hHcard
      omega
    obtain ⟨k,hk,hkt,r,hrt,hover,hi,hj,_,hpre,hK,hZ,hU⟩ :=
      nonsylow_trapped_residual_critical_path_knownSimple
        (e := e) (hz := hz) (hn := hn) hb4 hns p htrapped q hat hct hD hne
    refine ⟨delta,hdelta,hel,t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,hgen,z,q,hq,hnorm,
      hHcard,?_,?_,?_,?_,?_,hpre,k,hk,hkt,r,hrt,hover,hi,hj,hK,hZ,hU⟩
    · rw [commutator_comm (Z d.radical z ⊓ Q d.radical (alpha d.radical))]
      exact hseed
    · rw [commutator_comm (Z d.radical z ⊓ Q d.radical (alpha d.radical))]
      exact hedge
    · rw [commutator_comm (Z d.radical z ⊓ Q d.radical (alpha d.radical))]
      exact hmiddle
    · rw [commutator_comm (Z d.radical z ⊓ Q d.radical (alpha d.radical))]
      exact hcent
    · rw [commutator_comm (Z d.radical z ⊓ Q d.radical (alpha d.radical))]
      exact hncent

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
