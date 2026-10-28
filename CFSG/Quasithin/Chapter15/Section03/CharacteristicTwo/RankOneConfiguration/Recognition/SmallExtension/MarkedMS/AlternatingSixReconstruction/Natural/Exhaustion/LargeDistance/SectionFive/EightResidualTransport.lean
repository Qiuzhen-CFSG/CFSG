module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightPairedNormalizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPredecessor
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowUnequalKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignment
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePredecessorSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeResidualRotation
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

/-!
# The predecessor residual comparison for equal terminal movers

A trapped radius bounds the predecessor slice when the two relative movers
on its last edge agree. The whole reverse kernel then lies in this slice,
and its commutator with the entire predecessor core has order at most eight
and is fixed by the predecessor residual. Consequently the same residual
element preserves the commutator of every core actor while rotating the last
edge to the preceding edge.

If relative movers also agree across the preceding two-edge segment, this
literal rotation makes a new overlapping critical path whose two critical
indices are two. Its full-seed and moved-seed displacements equal the original
nonzero kernel line. The natural-module alignment bound contradicts a trapped
nonnormalizing seed. Both moving covers and all central attachments remain.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(5.7)--(5.8), printed pp.919--920. The two terminal relative-mover equalities
are explicit branch hypotheses; this does not prove unconditional radius
escape or the image-eight distance bound. The residual-fixedness input is
the general predecessor-slice theorem, without an image-sixteen assumption.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightResidualTransport
open EightPairedNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Equal last relative movers under trapping make the whole reverse-kernel
core commutator fixed by the predecessor residual, with both covers retained. -/
theorem trapped_equal_predecessor_residual_fixed_knownSimple
    (hb : 4 < replacementDistance h d)
    {a₀ z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ z)
    (htrap : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a')
    (hequal : relativeMover (d := d) a' (q.walk.getVert (q.walk.length-1)) =
      relativeMover (d := d) (q.walk.getVert (q.walk.length-2))
        (q.walk.getVert (q.walk.length-1))) :
    let c := q.walk.getVert (q.walk.length-2)
    let N := ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical c⁆
    Nat.card N ≤ 8 ∧ N ≤ fixedCore d.radical c ∧
      stabilizer d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < q.walk.length := q.length_eq_b ▸ hb2
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2)) = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hct : Adjacent d.radical (q.walk.getVert (q.walk.length-2))
      (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
    rw [show q.walk.length-2+1=q.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
    rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  exact predecessor_slice_commutator_residual_fixed s hc hb2 q
    (trapped_all_equal_slices_le_two_knownSimple (e := e) (hz := hz) (hn := hn)
      hb p htrap hcol hct het hequal)

include e hz hn in
/-- A predecessor residual element preserves the commutator while conjugating
an arbitrary core actor, using the literal full reverse kernel. -/
theorem trapped_equal_radius_residual_transport_knownSimple
    (hb : 4 < replacementDistance h d)
    {a₀ a₁ : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (hbad : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a')
    (hequal : relativeMover (d := d) a' (q.walk.getVert (q.walk.length-1)) =
      relativeMover (d := d) (q.walk.getVert (q.walk.length-2))
        (q.walk.getVert (q.walk.length-1)))
    (D : Subgroup (FreeAmalgam d.radical))
    (hD : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (k : FreeAmalgam d.radical)
    (hk : k ∈ Ltilde d.radical (q.walk.getVert (q.walk.length-2))) :
    ⁅Z d.radical a' ⊓ Q d.radical a,D.map (MulAut.conj k).toMonoidHom⁆ =
      ⁅Z d.radical a' ⊓ Q d.radical a,D⁆ := by
  have hh := trapped_equal_predecessor_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hbad q hequal
  have hn := trapped_equal_predecessor_residual_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hbad q hequal
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2)) = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hl : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  exact slice_commutator_transport_of_fixed (h := h) (by omega) hcol _
    (hh.1.ge.trans inf_le_right) (hn.2.1.trans inf_le_right) D hD k hk


include e hz hn in
/-- With equal relative movers across both terminal two-edge segments, the
actual predecessor residual rotation preserves the nonzero whole-kernel
commutator and yields an overlapping critical path with both indices two. -/
theorem trapped_equal_residual_critical_path_knownSimple
    (hb4 : 4 < replacementDistance h d)
    {a₀ a₁ : Vertex d.radical}
    (p₀ : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (htrapped : V d.radical a₀ ≤ Q d.radical (p₀.walk.getVert (p₀.walk.length-2)))
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlastEqual : relativeMover (d := d) a' (p.walk.getVert (p.walk.length-1)) =
      relativeMover (d := d) (p.walk.getVert (p.walk.length-2))
        (p.walk.getVert (p.walk.length-1)))
    (hprevEqual : relativeMover (d := d) (p.walk.getVert (p.walk.length-2))
        (p.walk.getVert (p.walk.length-3)) =
      relativeMover (d := d) (p.walk.getVert (p.walk.length-4))
        (p.walk.getVert (p.walk.length-3)))
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
        H ≤ fixedCore d.radical (p.walk.getVert (p.walk.length-2)) ∧
        ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ c)⁆=H ∧
        ⁅Z d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆=H ∧
        ⁅U d.radical a',Z d.radical (act d.radical k⁻¹ c)⁆=H := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hp := trapped_equal_predecessor_residual_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 p₀ htrapped p hlastEqual
  have htransport (k : FreeAmalgam d.radical)
      (hk : k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2))) :
      ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ c)⁆ =
        ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ := by
    rw [Z_act,inv_inv]
    exact trapped_equal_radius_residual_transport_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 p₀ htrapped p hlastEqual _ hD k hk
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
  have hover (i : ℕ) (hi : i ≤ p.walk.length-3) :
      q.walk.getVert (i+2) = p.walk.getVert i := by
    change (w₀.append w₁).getVert (i+2)=p.walk.getVert i
    rw [SimpleGraph.Walk.getVert_append,hw₀,if_neg (by omega),Nat.add_sub_cancel]
    change ((p.walk.take (p.walk.length-3)).concat hend).getVert i=p.walk.getVert i
    rw [SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append']
    rw [if_pos (by simpa only [SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _)] using hi),SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hi]
  have hqpre : q.walk.getVert (q.walk.length-2) = p.walk.getVert (p.walk.length-4) := by
    have hl4 : 4 < p.walk.length := p.length_eq_b ▸ hb4
    have hqlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rw [hqlen,show p.walk.length-2=p.walk.length-4+2 by omega]
    exact hover _ (by omega)
  have hqedge : q.walk.getVert (q.walk.length-1) = p.walk.getVert (p.walk.length-3) := by
    have hqlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rw [hqlen,show p.walk.length-1=p.walk.length-3+2 by omega]
    exact hover _ le_rfl
  have hqEqual : relativeMover (d := d) (act d.radical k a')
        (q.walk.getVert (q.walk.length-1)) =
      relativeMover (d := d) (q.walk.getVert (q.walk.length-2))
        (q.walk.getVert (q.walk.length-1)) := by
    rw [hqpre,hqedge]
    have hh := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) hlastEqual
    have hkpre : act d.radical k (p.walk.getVert (p.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := Ltilde_le_stabilizer _ hk
    rw [relativeMover_act,relativeMover_act,hkt,hkpre] at hh
    exact hh.trans hprevEqual
  have hq := trapped_equal_predecessor_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 p₀ htrapped q hqEqual
  let qr := CriticalPath.ofPair (geometry := replacementGeometry h d) q.end_color
    (critical_reverse_pair s hc q)
  have hqrsmall : (Q d.radical c).relIndex (Z d.radical (act d.radical k a')) < 4 := by
    rw [hq.2.2]
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
  refine ⟨k,hk,hkt,q,?_,?_,hq.2.1,hq.2.2,hHcard,?_,htransport k hk,heq.symm,hED.trans heq.symm⟩
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
  · exact (commutator_mono le_rfl hD).trans hp.2.1

include e hz hn in
/-- Two equal terminal relative movers contradict a trapped nonnormalizing seed.
The same predecessor residual element carries its nonzero full-kernel line. -/
theorem trapped_equal_tail_nonnormalization_false_knownSimple
    (hb4 : 4 < replacementDistance h d)
    {a₀ a₁ : Vertex d.radical}
    (p₀ : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (htrapped : V d.radical a₀ ≤ Q d.radical (p₀.walk.getVert (p₀.walk.length-2)))
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlastEqual : relativeMover (d := d) a' (p.walk.getVert (p.walk.length-1)) =
      relativeMover (d := d) (p.walk.getVert (p.walk.length-2))
        (p.walk.getVert (p.walk.length-1)))
    (hprevEqual : relativeMover (d := d) (p.walk.getVert (p.walk.length-2))
        (p.walk.getVert (p.walk.length-3)) =
      relativeMover (d := d) (p.walk.getVert (p.walk.length-4))
        (p.walk.getVert (p.walk.length-3)))
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hD : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hnorm : ¬ Z d.radical a' ≤ normalizer ((Z d.radical c ⊔ Z d.radical a :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) : False := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hp := trapped_equal_predecessor_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 p₀ htrapped p hlastEqual
  have hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4 := by
    rw [hp.2.1]
    decide
  have hline := trapped_nonnormalizing_seed_kernel_line_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 p hsmall hat hct hD hnorm
  have hne : ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≠ ⊥ := by
    intro hz
    have hh := hline.1
    rw [commutator_comm, hz, card_bot] at hh
    contradiction
  obtain ⟨k,hk,hkt,r,hrt,hover,hi,hj,hcard,hpre,hK,hZ,hU⟩ :=
    trapped_equal_residual_critical_path_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 p₀ htrapped p hlastEqual hprevEqual hat hct hD hne
  have halign : ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ ≤
      ⁅Z d.radical a,Z d.radical a'⁆ ⊔
        (stabilizer d.radical a' ⊓ centralizer (stabilizer d.radical a' :
          Set (FreeAmalgam d.radical))) := by
    rw [commutator_comm]
    exact hline.2.trans (sup_le_sup_left (inf_le_inf_right _ (Z_le_stabilizer d.radical a')) _)
  have hJ : Z d.radical (act d.radical k⁻¹ c) ≤ stabilizer d.radical a' := by
    have hh := map_mono (f := (MulAut.conj k).toMonoidHom)
      (Z_le_stabilizer_of_dist_le c _ r.critical.1.le)
    have h1 := Z_act d.radical k⁻¹ c
    have h2 := stabilizer_act d.radical k⁻¹ (act d.radical k a')
    rw [inv_inv] at h1 h2
    have hcancel : act d.radical k⁻¹ (act d.radical k a') = a' := by
      rw [←act_mul,mul_inv_cancel,act_one]
    rwa [←h1,←h2,hcancel] at hh
  have hz0 := small_critical_aligned_kernel_commutator_eq_bot s hc p hsmall
    (Z d.radical (act d.radical k⁻¹ c)) hJ (hU ▸ halign)
  rw [hK] at hz0
  exact hne hz0

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightResidualTransport
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
