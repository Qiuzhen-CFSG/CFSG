module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SelectedMovement

/-!
# The large commutator in the reciprocal selected span

The full backward selector supplies a second large critical pair whose two
seeds belong to the original selected span. Its commutator cannot have order
at most two, since that would force both critical seed images to have order
two. Thus the selected derived subgroup has order greater than two. The
same statement transports along the literal amalgam action to any starting
vertex; both central covers and every radical image are retained.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.12)(2), printed p.926.
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

include e hz hn in
/-- A large critical image forces a selected-span commutator of order greater
than two. Both seeds of the large backward critical pair lie in the selected
span, by the literal controlled backward transport. -/
theorem large_selected_derived_gt_two_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    2 < Nat.card (⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ :
        Subgroup (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,hexact,t,c,hat,hct,hgen,hgenQ,
    q,hq1,hq2,hq3,hidx,hstrict,htransport,hmove,hDexact,hWN,hfix,hback⟩ :=
    full_seed_backward_large_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  obtain ⟨x,hx,hxt,k,hk,hc',g,hg,hagree⟩ := htransport
  have hspan := controlled_backward_span_eq hb p hat x hx k hc' g hg.2 hagree
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  have hZc : Z d.radical c ≤ P := by
    change Z d.radical c ≤ localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    rw [←hspan]
    exact Z_le_localZSpan d.radical _ _
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    (localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
      (((replacementGeometry h d).V_le_Q (show 2 < replacementDistance h d by omega) (alpha d.radical) rfl).trans
        (fun _ hx => hx.1))
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  let : Finite (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (Subgroup.commutator_le_self P)) (inclusion_injective _)
  by_contra hnlarge
  have hsmall : Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by change ¬ 2 < Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) at hnlarge; omega
  have hcsmall : Nat.card (⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ :
      Subgroup (FreeAmalgam d.radical)) ≤ 2 :=
    (card_le_of_le (commutator_mono hZc (Z_le_localZSpan d.radical _ _))).trans hsmall
  have htwo := (critical_indices_two_of_commutator_card s hc q hcsmall).1
  omega

include e hz hn in
/-- The same lower bound at any starting vertex of a large critical path. -/
theorem large_selected_derived_gt_two_at_knownSimple
    (hb : replacementDistance h d = 4) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    2 < Nat.card (⁅localZSpan d.radical (p.walk.getVert 2) a,
      localZSpan d.radical (p.walk.getVert 2) a⁆ :
        Subgroup (FreeAmalgam d.radical)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_selected_derived_gt_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  have hlarge₀ : 4 ≤ (Q d.radical (act d.radical g⁻¹ z)).relIndex
      (Z d.radical (act d.radical g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  have hm := base (p.act g⁻¹) hlarge₀
  simp only [CriticalPath.act,actWalk_getVert] at hm
  rw [LocalCommutator.CriticalCase.localZSpan_act,←map_commutator,
    card_map_of_injective (MulAut.conj _).injective] at hm
  exact hm

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
