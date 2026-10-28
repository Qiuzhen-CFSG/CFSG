module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SelectedMovement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ChiefFactor

/-!
# From the selected span to the whole derived radius

For either moving cover, a large critical path makes its forward seed
escape the Baumann slice. Apply the unique-noncentral-chief-factor
alternative to the normal span of this seed. The fixed alternative would
put the seed in the slice, so the span, joined with the full starting seed,
contains the entire moving radius.

The radius is the moving radius joined with its abelian incident edge
radius. The preceding containment bounds its whole derived subgroup by
the selected span's core movement. This step holds for all radical images
and both covers; it does not require a chosen Sylow or point-core image.

On the sixteen-element moving cover, SelectedMovement identifies that
movement with the selected derived subgroup. Thus the whole derived radius,
the selected derived subgroup and the selected core movement coincide.
Their order is at most eight; they lie in the same midpoint seed and are
fixed by the actual residual. This supplies a whole-radius step in the
large-image argument, while leaving the augmentation-cover movement,
large-image and chosen large-slice contradictions, and Source/Application
unfinished. In particular it is not a whole residual-core product estimate.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.2)(i), (5.12)(2), printed pp.914,925--926. The chief-factor
alternative and all maps are instantiated in the natural replacement.
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

include s in
/-- The selected forward span carries the unique noncentral factor of the
whole radius. This uses one large path, on either cover and every radical image. -/
theorem large_moving_radius_le_selected_span
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    Vcirc d.radical (alpha d.radical) ≤
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊔ Z d.radical (alpha d.radical) := by
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  let Y := P.comap (embedM d.radical)
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hPV : P ≤ V d.radical (alpha d.radical) := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    hPV.trans ((replacementGeometry h d).V_local _ rfl hb2)
  have hPN := localZSpan_normalized d.radical (p.walk.getVert 2) (alpha d.radical)
  have hYm : Y.map (embedM d.radical) = P :=
    map_comap_eq_self (hPG.trans_eq (stabilizer_m_base d.radical))
  let : Y.Normal := ⟨by
    intro y hy g
    change embedM d.radical (g*y*g⁻¹) ∈ P
    rw [map_mul,map_mul,map_inv]
    have hg : embedM d.radical g ∈ stabilizer d.radical (alpha d.radical) := by
      rw [show alpha d.radical = mVertex d.radical 1 from rfl,stabilizer_m_base]
      exact ⟨g,rfl⟩
    exact (mem_normalizer_iff.mp (hPN hg) (embedM d.radical y)).mp hy⟩
  have hLm : (replacementComponent d).map (embedM d.radical) = Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
  have hZm : (radiusSeed d).map (embedM d.radical) = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  rcases critical_radius_normal_subgroup_dichotomy s hc hb2 p hlarge Y (comap_mono hPV) with hf | hm
  · have hf' := map_mono (f := embedM d.radical) hf
    rw [map_commutator,hYm,hLm,hZm] at hf'
    have hPB : P ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
      intro v hv
      apply (mem_B_iff d.radical (alpha d.radical) _ ((replacementGeometry h d).V_local _ rfl hb2) v).mpr
      refine ⟨hPV hv,?_⟩
      intro l hl
      rw [commutator_comm] at hf'
      exact hf' (commutator_mem_commutator hl hv)
    exact (large_image_forward_eligible s hc hb p hlarge
      ((DistanceEight.U_le_Z d.radical _).trans ((Z_le_localZSpan d.radical _ _).trans hPB))).elim
  · have hm' := map_mono (f := embedM d.radical) hm
    rw [map_commutator,radius_comap_map (h := h) hb2,hLm,Subgroup.map_sup,hYm,hZm] at hm'
    exact hm'

include e hz hn in
/-- The natural-cover branch now controls the whole moving radius, not
only the selected span. Its full starting seed contributes no core movement. -/
theorem natural_large_moving_radius_core_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    (hnat : Nat.card (replacementMoved d) = 16) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ⁅Vcirc d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hm := large_moving_radius_le_selected_span s hc hb p hlarge
  have hf := (natural_large_selected_span_core_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hnat p hlarge).1
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hb2 : 2 < replacementDistance h d := by omega
  have hPG : localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤
      stabilizer d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
      ((replacementGeometry h d).V_local _ rfl hb2)
  apply (commutator_mono hm le_rfl).trans
  exact commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical)) _ _ _ _
    (fixedCore_normalized d.radical (alpha d.radical)) hPG (Z_le_stabilizer d.radical _) hf
    ((Z_centralizes_Q d.radical (alpha d.radical) rfl).le.trans bot_le)

include s in
/-- The entire derived radius lies in the core movement of the chosen
span, for both covers and every radical image. -/
theorem large_radius_derived_le_selected_core
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆ ≤
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),Q d.radical (alpha d.radical)⁆ := by
  let a := alpha d.radical
  let P := localZSpan d.radical (p.walk.getVert 2) a
  let D := ⁅P,Q d.radical a⁆
  have hb2 : 2 < replacementDistance h d := by omega
  have hVQ := (replacementGeometry h d).V_le_Q hb2 a rfl
  have hVG : V d.radical a ≤ stabilizer d.radical a := hVQ.trans (fun _ hx => hx.1)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hPPV : P ≤ V d.radical a := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hPN : stabilizer d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅P,Q d.radical a⁆).map (MulAut.conj g).toMonoidHom = ⁅P,Q d.radical a⁆
    have hmP : P.map (MulAut.conj g).toMonoidHom = P :=
      mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized d.radical _ _ hg)
    have hmQ : (Q d.radical a).map (MulAut.conj g).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hg)
    rw [map_commutator,hmP,hmQ]
  have hPG : Vcirc d.radical a ≤ stabilizer d.radical a :=
    (le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer a).trans (V_normalized a))).trans hVG
  have hEG := (edge_radius_le_radius rfl (base_adjacent d.radical)).trans hVG
  have hdecomp : V d.radical a = Vcirc d.radical a ⊔ V d.radical (beta d.radical) := by
    apply le_antisymm
    · have hm := map_mono (f := embedM d.radical)
        (radius_comap_le_edge_sup_commutator (h := h) (r := d) hb2)
      have hLm : (replacementComponent d).map (embedM d.radical) = Ltilde d.radical a := by
        rw [Ltilde_alpha,replacement_residual h d]
      rw [radius_comap_map (h := h) hb2,Subgroup.map_sup,edge_radius_comap_map (h := h) hb2,
        map_commutator,radius_comap_map (h := h) hb2,hLm] at hm
      exact hm.trans_eq (sup_comm _ _)
    · exact sup_le (le_normalizer_iff_commutator_le_left.mp
        ((Ltilde_le_stabilizer a).trans (V_normalized a)))
        (edge_radius_le_radius rfl (base_adjacent d.radical))
  have hmQ : ⁅Vcirc d.radical a,Q d.radical a⁆ ≤ D :=
    (commutator_mono (large_moving_radius_le_selected_span s hc hb p hlarge) le_rfl).trans
      (commutator_sup_le_of_relative_normal (stabilizer d.radical a) _ _ _ _ hPN
        (hPPV.trans hVG) (Z_le_stabilizer d.radical _) le_rfl
        ((Z_centralizes_Q d.radical a rfl).le.trans bot_le))
  have hPV : ⁅Vcirc d.radical a,V d.radical a⁆ ≤ D :=
    (commutator_mono le_rfl hVQ).trans hmQ
  have hPE : ⁅Vcirc d.radical a,V d.radical (beta d.radical)⁆ ≤ D :=
    (commutator_mono le_rfl (edge_radius_le_radius rfl (base_adjacent d.radical))).trans hPV
  have hEE : ⁅V d.radical (beta d.radical),V d.radical (beta d.radical)⁆ ≤ D :=
    (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr
        (edge_radius_commutative (replacementGeometry h d) hb2 a (beta d.radical) rfl (base_adjacent d.radical)))).le.trans bot_le
  have hEV : ⁅V d.radical (beta d.radical),V d.radical a⁆ ≤ D := by
    rw [commutator_comm,hdecomp]
    exact commutator_sup_le_of_relative_normal (stabilizer d.radical a) _ _ _ _ hPN hPG hEG hPE hEE
  change ⁅V d.radical a,V d.radical a⁆ ≤ D
  conv_lhs => lhs; rw [hdecomp]
  exact commutator_sup_le_of_relative_normal (stabilizer d.radical a) _ _ _ _ hPN hPG hEG hPV hEV

include e hz hn in
/-- For the natural cover, the whole derived radius, the selected derived
subgroup and the selected core movement coincide. They lie in the same
midpoint seed and are small and residual-fixed. -/
theorem natural_large_radius_derived_configuration_knownSimple
    (hb : replacementDistance h d = 4)
    (hnat : Nat.card (replacementMoved d) = 16) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    let H := ⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆
    H = ⁅P,P⁆ ∧ ⁅P,P⁆ = ⁅P,Q d.radical (alpha d.radical)⁆ ∧
      H ≤ Z d.radical (p.walk.getVert 2) ∧ H ≤ fixedCore d.radical (alpha d.radical) ∧
      H ≤ X d.radical (alpha d.radical) ∧ Nat.card H ≤ 8 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hd := natural_large_selected_span_core_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hnat p hlarge
  have hupper := large_radius_derived_le_selected_core s hc hb p hlarge
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hPV : localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤ V d.radical (alpha d.radical) :=
    localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have heq := le_antisymm (hupper.trans hd.2.2.2.1.le) (commutator_mono hPV hPV)
  dsimp only
  refine ⟨heq,hd.2.2.2.1.symm,?_,?_,?_,?_⟩
  all_goals rw [heq,←hd.2.2.2.1]
  · exact hd.2.2.2.2
  · exact hd.1
  · exact hd.2.1
  · exact hd.2.2.1

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
