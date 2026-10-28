module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalExclusionSeed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalQuotient

/-!
# The central kernel and large derived subgroup of the moved radius

Full-radius core fixedness gives residual fixation of the derived radius.
The three-subgroups lemma then shows that the literal Baumann preimage
centralizes the moved radius. On a large critical path, the selected-span
derived subgroup equals its component-moved derived subgroup and therefore
lies in the moved-radius derived subgroup. The backward-pair lower bound
makes the latter's order greater than two, at every starting vertex.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10) and (5.12)(2), printed pp.880,926.
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


/-- Under full-radius core fixedness, the Baumann preimage centralizes the
entire moved radius. This is the three-subgroups lemma on the literal groups. -/
theorem reciprocal_B_centralizes_moving
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    B d.radical a ((replacementGeometry h d).Z_normal a) ≤
      centralizer (Vcirc d.radical a : Set (FreeAmalgam d.radical)) := by
  have hVQ := V_le_Q d.radical (geometry := replacementGeometry h d) ha hb
  have hVV : ⁅V d.radical a,V d.radical a⁆ ≤
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono le_rfl hVQ).trans hfixed).trans inf_le_right
  apply (commutator_centralizes_iff_centralizes_moved (V d.radical a)
    (Ltilde d.radical a) _ (Escape.EdgeTransfer.B_le_radius hb a ha) hVV).mp
  have hBZ : ⁅B d.radical a ((replacementGeometry h d).Z_normal a),Ltilde d.radical a⁆ ≤
      Z d.radical a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl b hb'
    exact ((mem_B_iff d.radical a _ (hVQ.trans (fun _ hx => hx.1)) b).mp hb').2 l hl
  exact hBZ.trans ((commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q d.radical a ha)).trans (centralizer_le hVQ))

include e hz hn in
/-- The large selected commutator lies in the derived moved radius. -/
theorem large_moving_derived_gt_two_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (hfixed : ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical)) :
    2 < Nat.card (⁅Vcirc d.radical (alpha d.radical),Vcirc d.radical (alpha d.radical)⁆ :
      Subgroup (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hPV : localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤
      V d.radical (alpha d.radical) := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hPQ := hPV.trans (V_le_Q d.radical (geometry := replacementGeometry h d) rfl hb2)
  have hPP := ((commutator_mono hPV hPQ).trans hfixed).trans inf_le_right
  have he := selected_span_derived_eq_moved hb2 p hPP
  have hP₀V : forwardMovedSpan d.radical (p.walk.getVert 2) ≤ Vcirc d.radical (alpha d.radical) :=
    commutator_mono hPV le_rfl
  have hmV : Vcirc d.radical (alpha d.radical) ≤ V d.radical (alpha d.radical) :=
    le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer _).trans (V_normalized _))
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite (Vcirc d.radical (alpha d.radical)) :=
    Finite.of_injective (inclusion (hmV.trans ((replacementGeometry h d).V_local _ rfl hb2)))
      (inclusion_injective _)
  let : Finite (⁅Vcirc d.radical (alpha d.radical),Vcirc d.radical (alpha d.radical)⁆ :
      Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
        (inclusion (Subgroup.commutator_le_self _)) (inclusion_injective _)
  have hbig := large_selected_derived_gt_two_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  rw [he] at hbig
  exact hbig.trans_le (card_le_of_le (commutator_mono hP₀V hP₀V))

include e hz hn in
/-- Large critical paths at any starting vertex give a derived moved-radius
subgroup of order greater than two once full-radius core fixedness holds. -/
theorem large_moving_derived_gt_two_at_knownSimple
    (hb : replacementDistance h d = 4) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    2 < Nat.card (⁅Vcirc d.radical a,Vcirc d.radical a⁆ :
      Subgroup (FreeAmalgam d.radical)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_moving_derived_gt_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  have hlarge₀ : 4 ≤ (Q d.radical (act d.radical g⁻¹ z)).relIndex
      (Z d.radical (act d.radical g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  have hfixed₀ : ⁅V d.radical (act d.radical g⁻¹ a),Q d.radical (act d.radical g⁻¹ a)⁆ ≤
      fixedCore d.radical (act d.radical g⁻¹ a) := by
    rw [V_act,Q_act,←map_commutator,fixedCore,Q_act,Ltilde_act,
      map_inf_centralizer_of_injective _ (MulAut.conj _).injective]
    exact map_mono hfixed
  have hm := base (p.act g⁻¹) hlarge₀ hfixed₀
  rw [Vcirc_act,←map_commutator,card_map_of_injective (MulAut.conj _).injective] at hm
  exact hm

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
