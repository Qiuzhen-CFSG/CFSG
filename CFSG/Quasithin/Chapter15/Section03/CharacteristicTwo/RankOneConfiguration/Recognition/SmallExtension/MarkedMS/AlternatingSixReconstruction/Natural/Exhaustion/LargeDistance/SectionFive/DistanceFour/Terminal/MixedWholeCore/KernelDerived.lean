module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedSpanDerived
public import Theory.GroupTheory.ClassTwoIndexTwoDerived

/-!
# Derived transfer for the strict mixed midpoint kernel

The mixed radius has image of order two at the midpoint. Its selected span
has derived subgroup of order two, fixed by the starting stabilizer. The
faithful symmetric-six action on the span's central quotient forces that
quotient to have order greater than four. The class-two index-two theorem
therefore identifies the common midpoint kernel's derived subgroup with
the span's entire derived subgroup.

This supplies the transfer premise of
`selected_terminal_false_of_opposite_core_bounds` without an endpoint
commutator estimate or recognition of a natural central quotient. The source
leaf applies it to the original strict mixed branch. The two estimates for
the whole residual core remain source obligations; neither the span nor its
midpoint kernel is identified with that whole core.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the class-two argument of (3.10)(i), printed pp.880--881, applied to
the mixed selected configuration in (5.12), printed pp.924--927. The faithful
action argument follows `DistanceFour.Kernel` with the mixed radius bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- The common midpoint kernel retains the selected span's entire derived line. -/
theorem selected_kernel_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (q : MixedBackwardShift (h := h) p) :
    let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
    let Y := P ⊓ Q d.radical (p.walk.getVert 2)
    ⁅Y,Y⁆ = ⁅P,P⁆ ∧ Nat.card (⁅Y,Y⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  let Y := P ⊓ Q d.radical c
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hPV : P ≤ V d.radical (alpha d.radical) := localZSpan_le_V d.radical hdist
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    hPV.trans ((V_le_Q d.radical rfl hb2).trans (fun _ hx => hx.1))
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  let : Finite (V d.radical (alpha d.radical)) := Finite.of_injective
    (inclusion ((V_le_Q d.radical rfl hb2).trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hD := mixed_selected_span_derived_data_knownSimple hb u him p q
  change ⁅P,P⁆ = _ ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
    ⁅P,P⁆ ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) at hD
  have hnon : ⁅P,P⁆ ≠ ⊥ := by
    intro he
    have hi := hD.2.1
    rw [he,card_bot] at hi
    omega
  have hm : (_root_.commutator P).map P.subtype = ⁅P,P⁆ := P.map_subtype_commutator
  have hDc : _root_.commutator P ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hD.2.2 (hm ▸ mem_map_of_mem P.subtype hx) y (hPG y.property)
  have hDcard : Nat.card (_root_.commutator P) = 2 := by
    rw [←card_map_of_injective P.subtype_injective,hm]
    exact hD.2.1
  have hlarge : 4 < (center P).index := by
    let ρ := selectedSpanSymmetricAction s hc hb2 c hdist
    have hρ := selected_span_symmetric_action_injective s hb2 p hnon ρ
      (selectedSpanSymmetricAction_projection s hc hb2 c hdist)
    have hi := Nat.card_le_card_of_injective (f := fun g => (ρ g).toEquiv)
      (MulEquiv.toEquiv_injective.comp hρ)
    change Nat.card (Equiv.Perm (Fin 6)) ≤ Nat.card (Equiv.Perm (P ⧸ center P)) at hi
    rw [Nat.card_perm,Nat.card_fin,Nat.card_perm] at hi
    rw [index_eq_card]
    by_contra hn
    have hh := Nat.factorial_le (show Nat.card (P ⧸ center P) ≤ 4 by omega)
    norm_num at hi hh
    omega
  have hq2 : q.path.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hradius := mixed_four_backward_radius_index_knownSimple hb u him p q.path hq2
  rw [hl] at hradius
  have hi : (Y.subgroupOf P).index ≤ 2 := by
    change Y.relIndex P ≤ 2
    rw [inf_relIndex_left]
    exact (relIndex_le_of_le_right hPV index_ne_zero_of_finite).trans_eq hradius
  have he := ClassTwo.commutator_eq_of_index_le_two_of_center_index_gt_four
    hDc hDcard hlarge (Y.subgroupOf P) hi
  have heq : ⁅Y,Y⁆ = ⁅P,P⁆ := by
    have hh := congrArg (Subgroup.map P.subtype) he
    rwa [map_commutator,map_subgroupOf_eq_of_le (show Y ≤ P from inf_le_left),hm] at hh
  exact ⟨heq,heq ▸ hD.2.1⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
