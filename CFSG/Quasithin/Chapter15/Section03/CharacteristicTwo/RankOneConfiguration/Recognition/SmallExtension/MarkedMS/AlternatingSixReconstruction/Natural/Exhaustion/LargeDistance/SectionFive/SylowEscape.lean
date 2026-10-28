module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmall
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusEscape
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmall
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePredecessorSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeResidualRotation
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallSeeds
/-!
# Radius escape for elementary replacement images with Sylow originals

Above distance four, the elementary replacement image is the full three-pair
subgroup of the actual symmetric-six quotient. If a whole radius were trapped
in its critical predecessor core, SylowSmall would bound every two-edge slice
by two and centralize every reverse-kernel commutator at its predecessor.
A residual element taking the last edge to the preceding edge preserves that
commutator and produces an overlapping critical path. Its small critical image
identifies the nonzero commutator with the full endpoint displacement.

The two-kernel selection supplies an eligible backward seed and one of two
conjugate critical endpoints which does not normalize its join with the starting
seed. Both paths retain the trapped radius. On the selected path, the full-seed
alignment/control theorem forces alignment with the original critical line and
endpoint center. The residual-rotated path forces the aligned full critical
kernel to be fixed, contradicting its nonzero commutator. The cubic is used
with its literal two-kernel generation equation; normalization of the whole
edge kernel is not assumed.

The literal replacement applications give radius escape at every component
vertex, universal critical escape, and overlapping backward and forward paths
with both forward slice lower bounds. Both moving covers of orders sixteen and
thirty-two and every central attachment remain present. The original radical
is distinct from its minimum characteristic replacement. Non-elementary images,
strict forward slices, terminal exclusions and distance four remain with the
large-distance assembly; no unconditional distance-two conclusion is claimed.

The `import all` edges deliberately extend the internal SylowSmall selector,
CubePredecessorSlice transport, CubeResidualRotation neighbor action and
CubeSmallSeeds obstruction without widening their existing public boundaries.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3), (5.7)--(5.8), printed pp.866--867,919--920, and Section 7,
pp.932--933; Aschbacher--Smith C.1.31, printed p.135.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SylowEscape
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)

include e hz hn in
/-- For a trapped elementary-image radius, every predecessor residual acts
trivially on the full reverse-kernel commutator, using the same conjugator
on its arbitrary core actor. The order-four possibility is retained. -/
theorem elementary_trapped_radius_residual_transport_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a₀ a₁ : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (hbad : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a')
    (D : Subgroup (FreeAmalgam d.radical))
    (hD : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (k : FreeAmalgam d.radical)
    (hk : k ∈ Ltilde d.radical (q.walk.getVert (q.walk.length-2))) :
    ⁅Z d.radical a' ⊓ Q d.radical a,D.map (MulAut.conj k).toMonoidHom⁆ =
      ⁅Z d.radical a' ⊓ Q d.radical a,D⁆ := by
  have hh := SylowSmall.elementary_trapped_radius_predecessor_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hel p hbad q
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2))=false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hl : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  exact slice_commutator_transport_of_fixed (h := h) (by omega) hcol _
    (hh.1.ge.trans inf_le_right)
    (hh.2.2.2.2.2.trans (centralizer_le (Ltilde_le_stabilizer _))) D hD k hk

include e hz hn in
/-- The residual rotation of a nonzero backward kernel is a critical path
with both critical images of order two under the trapped-radius hypothesis. -/
theorem elementary_trapped_residual_critical_path_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
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
  have hp := SylowSmall.elementary_trapped_radius_predecessor_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hel p₀ htrapped p
  have htransport (k : FreeAmalgam d.radical)
      (hk : k ∈ Ltilde d.radical (p.walk.getVert (p.walk.length-2))) :
      ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical (act d.radical k⁻¹ c)⁆ =
        ⁅Z d.radical a' ⊓ Q d.radical a,Z d.radical c⁆ := by
    rw [Z_act,inv_inv]
    exact elementary_trapped_radius_residual_transport_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 hel p₀ htrapped p _ hD k hk
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
  have hq := SylowSmall.elementary_trapped_radius_predecessor_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hel p₀ htrapped q
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
private theorem trapped_nonnormalization_false
    (hb4 : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a₀ a₁ : Vertex d.radical}
    (p₀ : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (htrapped : V d.radical a₀ ≤ Q d.radical (p₀.walk.getVert (p₀.walk.length-2)))
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hD : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hnorm : ¬ Z d.radical a' ≤ normalizer ((Z d.radical c ⊔
      Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) : False := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hu⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple hb4 hel
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hu]
  have hp := SylowSmall.elementary_trapped_radius_predecessor_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hel p₀ htrapped p
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [hp.2.1]
    decide
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical)=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr
        (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hZG : Z d.radical c ≤ stabilizer d.radical (alpha d.radical) :=
    (((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)).trans
      ((replacementGeometry h d).V_le_Q hb _ rfl)).trans (fun _ hx => hx.1)
  have hne : ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≠ ⊥ := by
    rw [commutator_comm]
    exact (small_nonnormalized_seed_kernel s hc hb p hsmall hZG hnorm).resolve_left
      (fun hn => hn hD)
  obtain ⟨k,hk,hkt,r,hrt,hover,hi,hj,hcard,hpre,hK,hZ,hU⟩ :=
    elementary_trapped_residual_critical_path_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 hel p₀ htrapped p hat hct hD hne
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have het : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hlast : color d.radical (p.walk.getVert (p.walk.length-1))=true := by
    have hh := adjacent_color_ne d.radical het
    rw [p.end_color] at hh
    cases he : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have hpred : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hcol : color d.radical c=false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hHP : ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≤ Z d.radical c := by
    rw [commutator_comm]
    exact ((cube_backward_kernel_le_edge_seeds s hc hb u hR p hat hct hD).1.trans
      inf_le_left).trans (adjacent_Z_le d.radical hcol hct)
  have halign := cube_critical_kernel_alignment s hc hb u hR p hsmall
    (Z d.radical c) (hD.trans (Q_le_adjacent_h d.radical hlast hpred)) hHP hnorm
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

include e hz hn in
/-- A whole radius cannot be trapped at the predecessor of a critical path
in the elementary replacement-image branch. Both full seed attachments are
retained in the residual rotation and its alignment contradiction. -/
theorem elementary_radius_escape_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ¬ V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  intro htrapped
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hu⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple hb4 hel
  have hp := SylowSmall.elementary_trapped_radius_predecessor_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hel p htrapped p
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [hp.2.1]
    decide
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨delta,hdelta,hd⟩ := exists_eligible_neighbor_at_edge s hc hb rfl ha1
  obtain ⟨t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,q,hq,hqs,hgen,hnorm⟩ :=
    SylowSmall.small_common_fixer_paired_seed (e := e) (hz := hz) (hn := hn)
      hb u hu p hsmall hdelta hd
  have hdist : (cosetGraph d.radical).dist (act d.radical g delta) (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist (act d.radical g delta) t=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical)=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr
        (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := act d.radical g delta) (v := t) (w := alpha d.radical)
  have hDV : Z d.radical (act d.radical g delta) ≤ V d.radical (alpha d.radical) :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  rcases hnorm with hnp | hnq
  · exact trapped_nonnormalization_false (e := e) (hz := hz) (hn := hn)
      hb4 hel p htrapped p hat hct (hDV.trans htrapped) hnp
  · have hVq : V d.radical (alpha d.radical) ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
      have hlen : q.walk.length=p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
      rw [hlen,hq,Q_act]
      have hV : (V d.radical (alpha d.radical)).map (MulAut.conj x⁻¹).toMonoidHom =
          V d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical _
          ((stabilizer d.radical (alpha d.radical)).inv_mem (Ltilde_le_stabilizer _ hx)))
      rw [←hV]
      exact map_mono htrapped
    exact trapped_nonnormalization_false (e := e) (hz := hz) (hn := hn)
      hb4 hel p htrapped q hat hct (hDV.trans hVq) hnq
include e hz hn in
/-- Radius escape at every component vertex of the original natural graph. -/
theorem elementary_radius_escape_at_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ¬ V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := elementary_radius_escape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hel (a' := act d.radical j⁻¹ a')
  rw [←hbase] at base
  intro htrapped
  apply base (p.act j⁻¹)
  have hm := map_mono (f := (MulAut.conj j).toMonoidHom) htrapped
  simpa only [CriticalPath.act,actWalk_length,actWalk_getVert,V_act,Q_act,inv_inv] using hm

include e hz hn in
/-- Universal critical escape in the actual elementary-image replacement graph,
including every shortest predecessor of every critical pair. -/
theorem elementary_criticalEscape_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d))) :
    Factorization.CriticalEscape d.radical (replacementGeometry h d) := by
  intro a ha a' hcrit c hce hpath
  obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist a c
  obtain ⟨v,hv⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a'
  let p : CriticalPath d.radical (replacementGeometry h d) a a' :=
    ⟨ha,w.append v,by rw [SimpleGraph.Walk.length_append,hw,hv,hce,hpath],hcrit⟩
  have heq : p.walk.getVert (p.walk.length-2) = c := by
    change (w.append v).getVert ((w.append v).length-2) = c
    rw [SimpleGraph.Walk.length_append,hv,hce,Nat.add_sub_cancel]
    simp only [SimpleGraph.Walk.getVert_append,lt_self_iff_false,ite_false,
      Nat.sub_self,SimpleGraph.Walk.getVert_zero]
  simpa only [heq] using elementary_radius_escape_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hel p

include e hz hn in
/-- Both source (5.8) slice lower bounds and the actual forward shift follow
without a point-core-image or strict-slice hypothesis. -/
theorem elementary_forward_path_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) ∧
      2 ≤ (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical a) ∧
      ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z,
        (cosetGraph d.radical).dist a' z = 2 ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
        q.walk.getVert (q.walk.length-2) = a' := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hesc := elementary_criticalEscape_knownSimple (e := e) (hz := hz) (hn := hn) hb4 hel
  exact ⟨critical_forward_slice_index_two_le_of_escape s hc hb hesc p,
    critical_start_slice_index_two_le s hc hb p,
    critical_forward_extension_of_escape s hc hb hesc p⟩

include e hz hn in
/-- An actual backward critical path follows from radius escape, with every
overlapping vertex retained and no strict Baumann-slice premise. -/
theorem elementary_backward_path_of_radius_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hel : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ c t, Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1=t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2)=p.walk.getVert i) ∧
        2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hd : (cosetGraph d.radical).dist a (p.walk.getVert (p.walk.length-2)) + 2 =
      (replacementGeometry h d).b d.radical := by
    rw [p.dist_start (Nat.sub_le _ _),p.length_eq_b]
    change replacementDistance h d - 2 + 2 = replacementDistance h d
    omega
  obtain ⟨c,hcol,hca,hcrit⟩ := exists_critical_shift d.radical p.start_color hd
    (elementary_radius_escape_at_knownSimple (e := e) (hz := hz) (hn := hn) hb4 hel p)
  obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a
  have hwlen : w.length=2 := hw.trans hca
  let t := w.getVert 1
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      w.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := by
    apply adjacent_symm d.radical
    apply (cosetGraph_adj d.radical _ _).mp
    have hh := w.adj_getVert_succ (i := 1) (by omega)
    simpa only [show 1+1=w.length by omega,SimpleGraph.Walk.getVert_length] using hh
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hwlen hcrit.2
  have hqt : q.walk.getVert 1=t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hwlen,show 1<2 from by decide,ite_true,t]
  have hover (i : ℕ) (hi : i ≤ p.walk.length-2) :
      q.walk.getVert (i+2)=p.walk.getVert i := p.prepend_two_overlap _ _ _ _ _ hi
  have hqa : q.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  refine ⟨c,t,hat,hct,q,hqt,hover,?_⟩
  have hh := critical_start_slice_index_two_le s hc hb q
  rwa [hqa] at hh


end SylowEscape
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
