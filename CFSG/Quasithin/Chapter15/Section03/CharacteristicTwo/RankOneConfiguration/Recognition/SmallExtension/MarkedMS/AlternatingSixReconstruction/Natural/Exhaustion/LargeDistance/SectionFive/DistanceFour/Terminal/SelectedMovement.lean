module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.FullBackward

/-!
# Selected-span movement after the relative backward shift

The relative holomorph chooses an edge transporter which need not fix the
starting vertex. Its conjugation agrees on the entire edge kernel with an
actor in the starting stabilizer. The original midpoint seed is in that
kernel, so this agreement identifies the normal spans of the original and
backward seeds inside the same starting stabilizer. This transport works
for both moving covers and every radical image.

On the sixteen-element moving cover, the whole midpoint-core movement of
a large critical pair equals its critical commutator. Apply the full-seed
backward selection, retaining its actual generating edge and actor. The
actor fixes the backward commutator, making it invariant under the whole
midpoint stabilizer. Its order at most eight gives residual fixedness.
The span identity then transfers this result to the original selected span.
Both seeds of the backward pair lie in that span, so its derived subgroup
is exactly its whole core movement and lies in the original midpoint seed.

RadiusDerived applies this to the whole radius. The augmentation-cover
movement and the remaining terminal contradictions are still required;
no bound on the whole residual core [Q,Ltilde] is inferred here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.12)(1)--(2), printed pp.867,924--926, and the relative
holomorph of Section 7, pp.932--933. The graph is the literal natural
characteristic replacement, with the full central attachments retained.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

omit [Finite G] in
private theorem span_le_of_seed_le {a c z : Vertex d.radical}
    (hz : Z d.radical z ≤ localZSpan d.radical c a) :
    localZSpan d.radical z a ≤ localZSpan d.radical c a := by
  rw [localZSpan_eq_conjugates]
  apply iSup_le
  intro g
  exact (map_mono hz).trans_eq (mem_normalizer_iff_map_conj_eq.mp
    (localZSpan_normalized d.radical c a ((stabilizer d.radical a).inv_mem g.property)))

/-- The relative holomorph's agreement on the edge kernel preserves the
whole selected span, even though its edge transporter need not fix the base. -/
theorem controlled_backward_span_eq
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    {t c : Vertex d.radical} (hat : Adjacent d.radical (alpha d.radical) t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical (alpha d.radical))
    (k : FreeAmalgam d.radical) (hc : c = act d.radical k (act d.radical x (p.walk.getVert 2)))
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (alpha d.radical))
    (hagree : ∀ v ∈ Q d.radical t, (MulAut.conj k⁻¹) v = (MulAut.conj g) v) :
    localZSpan d.radical c (alpha d.radical) =
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) := by
  let a := alpha d.radical
  let m := p.walk.getVert 2
  let v := act d.radical g⁻¹ (act d.radical x m)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hZQ : Z d.radical m ≤ Q d.radical a := by
    have hm : color d.radical m = false := (p.vertex_color (by omega)).mpr (by decide)
    apply Z_le_Q_of_dist_lt d.radical m ((replacementGeometry h d).exists_critical m hm)
    rw [(replacementGeometry h d).distance_constant _ hm,SimpleGraph.dist_comm,p.dist_start (by omega)]
    exact show 2 < replacementDistance h d by omega
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hxmQ : Z d.radical (act d.radical x m) ≤ Q d.radical t := by
    rw [Z_act]
    exact ((map_mono hZQ).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem hx)))).trans
        (Q_le_adjacent_h d.radical ht hat)
  have hZv : Z d.radical c = Z d.radical v := by
    rw [hc,Z_act]
    change (Z d.radical (act d.radical x m)).map (MulAut.conj k⁻¹).toMonoidHom =
      Z d.radical (act d.radical g⁻¹ (act d.radical x m))
    conv_rhs => rw [Z_act,inv_inv]
    apply le_antisymm
    · rintro _ ⟨y,hy,rfl⟩
      exact ⟨y,hy,(hagree y (hxmQ hy)).symm⟩
    · rintro _ ⟨y,hy,rfl⟩
      exact ⟨y,hy,hagree y (hxmQ hy)⟩
  have hspanv : localZSpan d.radical v a = localZSpan d.radical m a := by
    have hxfix : act d.radical x a = a := hx
    have hgfix : act d.radical g⁻¹ a = a := (stabilizer d.radical a).inv_mem hg
    have hxP : (localZSpan d.radical m a).map (MulAut.conj x⁻¹).toMonoidHom =
        localZSpan d.radical m a := mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized d.radical m a ((stabilizer d.radical a).inv_mem hx))
    have hgP : (localZSpan d.radical (act d.radical x m) a).map (MulAut.conj g).toMonoidHom =
        localZSpan d.radical (act d.radical x m) a := mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized d.radical (act d.radical x m) a hg)
    dsimp only [v]
    rw [←hgfix,LocalCommutator.CriticalCase.localZSpan_act,inv_inv,hgfix,hgP,
      ←hxfix,LocalCommutator.CriticalCase.localZSpan_act,hxfix,hxP]
  apply le_antisymm
  · apply span_le_of_seed_le
    rw [hZv,←hspanv]
    exact Z_le_localZSpan d.radical v a
  · rw [←hspanv]
    apply span_le_of_seed_le
    rw [←hZv]
    exact Z_le_localZSpan d.radical c a

include s in
private theorem natural_selected_core_control
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hnat : Nat.card (replacementMoved d) = 16) {c z : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical c))
    (W : Subgroup (FreeAmalgam d.radical))
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ W = stabilizer d.radical (q.walk.getVert 2))
    (hfix : ⁅Z d.radical c,Z d.radical z⁆ ≤ centralizer (W : Set (FreeAmalgam d.radical))) :
    let D := ⁅Z d.radical c,Z d.radical z⁆
    ⁅localZSpan d.radical c (q.walk.getVert 2),Q d.radical (q.walk.getVert 2)⁆ = D ∧
      D ≤ fixedCore d.radical (q.walk.getVert 2) ∧
      D ≤ X d.radical (q.walk.getVert 2) ∧ Nat.card D ≤ 8 := by
  let a := q.walk.getVert 2
  let D := ⁅Z d.radical c,Z d.radical z⁆
  have heq := natural_large_midpoint_movement_eq s hc hb hnat q hlarge
  have hdata := large_midpoint_movement s hc hb q hlarge
  rw [heq] at hdata
  have hcard := large_midpoint_movement_card s hc hb q hlarge
  rw [heq] at hcard
  have hGN : stabilizer d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le hdata.2.2.1 ((le_centralizer_iff.mp hfix).trans (Subgroup.centralizer_le_normalizer _))
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb
  have ha : color d.radical a = false := (q.vertex_color (by omega)).mpr (by decide)
  have hfixed : D ≤ fixedCore d.radical a :=
    small_core_residual_fixed_knownSimple (h := h) (e := e) ha D
      (hdata.2.1.trans (omegaCenter_le _)) ((Ltilde_le_stabilizer _).trans hGN) hcard
  refine ⟨le_antisymm ?_ (heq.symm.le.trans
    (commutator_mono (Z_le_localZSpan d.radical _ _) le_rfl)),hfixed,hdata.2.1,hcard⟩
  have hZcG : Z d.radical c ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le
    rw [q.dist_start (by omega),(replacementGeometry h d).distance_constant _ q.start_color]
    change 2 ≤ replacementDistance h d
    omega
  rw [localZSpan_eq_conjugates]
  apply commutator_iSup_le_of_relative_normal (stabilizer d.radical a)
    (Q d.radical a) D _ hGN
  · intro g
    exact (map_mono hZcG).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      ((stabilizer d.radical a).le_normalizer ((stabilizer d.radical a).inv_mem g.property)))
  · intro g
    have hh := congrArg (Subgroup.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom) heq
    have hQ : (Q d.radical a).map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom =
        Q d.radical a := mem_normalizer_iff_map_conj_eq.mp
      (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem g.property))
    have hD : D.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = D :=
      mem_normalizer_iff_map_conj_eq.mp (hGN ((stabilizer d.radical a).inv_mem g.property))
    change (⁅Z d.radical c,Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)).map _ = D.map _ at hh
    rw [map_commutator,hQ,hD] at hh
    exact hh.le

include e hz hn in
/-- On the natural cover, the entire original selected span has small,
residual-fixed core movement, for every radical image. The full backward
selector and its relative holomorph supply the same span internally. -/
theorem natural_large_selected_span_core_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    (hnat : Nat.card (replacementMoved d) = 16) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    let H := ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),Q d.radical (alpha d.radical)⁆
    H ≤ fixedCore d.radical (alpha d.radical) ∧
      H ≤ X d.radical (alpha d.radical) ∧ Nat.card H ≤ 8 ∧
      H = ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ∧
      H ≤ Z d.radical (p.walk.getVert 2) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,hexact,t,c,hat,hct,hgen,hgenQ,
    q,hq1,hq2,hq3,hidx,hstrict,htransport,hmove,hDexact,hWN,hfix,hback⟩ :=
    full_seed_backward_large_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  obtain ⟨x,hx,hxt,k,hk,hc',g,hg,hagree⟩ := htransport
  have hspan := controlled_backward_span_eq hb p hat x hx k hc' g hg.2 hagree
  have hd := natural_selected_core_control s hc hb hnat q hback W
    (by rwa [hq1,hq2]) hfix
  rw [hq2,hspan] at hd
  dsimp only
  refine ⟨hd.1.symm ▸ hd.2.1,hd.1.symm ▸ hd.2.2.1,hd.1.symm ▸ hd.2.2.2,?_,?_⟩
  · apply le_antisymm
    · rw [hd.1]
      have hZc : Z d.radical c ≤ localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) := by
        rw [←hspan]
        exact Z_le_localZSpan d.radical _ _
      exact commutator_mono hZc (Z_le_localZSpan d.radical _ _)
    · apply commutator_mono le_rfl
      have hl : p.walk.length = 4 := p.length_eq_b.trans hb
      exact (localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
        ((replacementGeometry h d).V_le_Q (show 2 < replacementDistance h d by omega) (alpha d.radical) rfl)
  · rw [hd.1]
    exact ((critical_Z_commutator_le_moving (h := h) q).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
