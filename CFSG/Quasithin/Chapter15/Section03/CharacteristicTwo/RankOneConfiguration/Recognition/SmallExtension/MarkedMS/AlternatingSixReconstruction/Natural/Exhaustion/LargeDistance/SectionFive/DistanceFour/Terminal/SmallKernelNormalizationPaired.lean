module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightCompatible
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalLines
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual

/-!
# The literal paired candidates for image-eight kernel normalization

The equal-mover selector is kept before its orientation is collapsed. Both
endpoint paths use the same selected edge, transporter, residual element and
common full-seed fixer. At least one candidate has an overlapping backward
critical path, and the selected seed retains its strict Baumann slice.
This is the geometric interface for strengthening the finite source-(5.6)
choice while preserving all data needed by source-(5.12)(1).

Source: MS93 (5.6)--(5.7), printed pp.917--919.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include e hz hn in
/-- Keep both source Delta candidates and their literal common fixer before
choosing the critical orientation. -/
theorem eight_equal_paired_backward_candidates_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hequal : EightEdgeComparison.edgeMover (d := d) delta (beta d.radical) =
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical delta)) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        let c := act d.radical g delta
        let t := act d.radical g (beta d.radical)
        let J := EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t
        Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        EightEdgeComparison.edgeMover (d := d) c t = J ∧
        2 < (B d.radical (alpha d.radical)
          ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c) ∧
        J ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) = stabilizer d.radical (alpha d.radical) ∧
        x ∈ J ⊔ J.map (MulAut.conj x).toMonoidHom ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ Z d.radical (act d.radical x z) = stabilizer d.radical (alpha d.radical) ∧
        (Z d.radical (alpha d.radical) ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
          centralizer (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical (alpha d.radical) ⊓
            centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) (act d.radical x z),
          (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
          (Q d.radical (act d.radical x z)).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
          ((∃ r : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert (p.walk.length-2)),
            r.walk.getVert 1 = t ∧ ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i) ∨
          (∃ r : CriticalPath d.radical (replacementGeometry h d) c (q.walk.getVert (q.walk.length-2)),
            r.walk.getVert 1 = t ∧ ∀ i ≤ q.walk.length-2, r.walk.getVert (i+2) = q.walk.getVert i)) := by
  obtain ⟨g,hg,x,hxL,hx3,hat,hgen,hxpair,hleft,hright,hfixed⟩ := EightCompatible.paired_generating_common_fixer_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb hmodel p hsmall
  let c := act d.radical g delta
  let t := act d.radical g (beta d.radical)
  have hx : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hxL
  have hct : Adjacent d.radical c t := (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
  have hEq : EightEdgeComparison.edgeMover (d := d) c t =
      EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t := by
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hequal
    dsimp only [EightEdgeComparison.edgeMover] at hh ⊢
    rw [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj g⁻¹).injective,←U_act,←Q_act,←Q_act,
      ←U_act,←Q_act,hga] at hh
    exact hh
  have strict (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (alpha d.radical)) :
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (act d.radical y delta)) := by
    have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj y⁻¹).toMonoidHom =
        B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        (by omega : 2 < replacementDistance h d) _ rfl ((stabilizer d.radical _).inv_mem hy))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hstrict
  have hxa : act d.radical x (alpha d.radical) = alpha d.radical := hx
  obtain ⟨q,hq⟩ : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) (act d.radical x z),
      ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x (alpha d.radical)) (act d.radical x z),
        ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hxa] at hh
  have hqs : (Q d.radical (act d.radical x z)).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    conv_lhs => rhs; rw [←hxa]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hsmall
  have hLgen : Ltilde d.radical (alpha d.radical) ≤
      EightEdgeComparison.edgeMover (d := d) c t ⊔ Z d.radical z ⊔
        Z d.radical (act d.radical x z) := by
    rw [hEq,hgen]
    exact Ltilde_le_stabilizer _
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hdelta
    have hc : color d.radical delta = false := by
      change color d.radical delta ≠ true at hh
      cases hc : color d.radical delta <;> simp_all
    change color d.radical (act d.radical g delta) = false
    rw [action_preserves_color,hc]
  have backward {v : Vertex d.radical}
      (b : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) v)
      (hbad : ¬ Z d.radical c ≤ Q d.radical (b.walk.getVert (b.walk.length-2))) :
      ∃ r : CriticalPath d.radical (replacementGeometry h d)
          c (b.walk.getVert (b.walk.length-2)),
        r.walk.getVert 1 = t ∧
        ∀ i ≤ b.walk.length-2, r.walk.getVert (i+2) = b.walk.getVert i := by
    let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length = 2 := rfl
    have hb2 : 2 ≤ (replacementGeometry h d).b d.radical := by
      change 2 ≤ replacementDistance h d
      omega
    let r := b.prepend_two hb2 hcol w hw hbad
    refine ⟨r,?_,fun i hi => b.prepend_two_overlap _ _ _ _ _ hi⟩
    change (b.prepend_two _ hcol w hw hbad).walk.getVert 1 = t
    rw [CriticalPath.prepend_two_walk]
    simp only [SimpleGraph.Walk.getVert_append,hw,show 1<2 from by decide,ite_true,
      w,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]
  refine ⟨g,hg,x,hxL,hx3,hat,hct,hEq,strict g hg,hgen,hxpair,hleft,hright,hfixed,q,hq,hqs,?_⟩
  by_cases hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · right
    apply backward q
    intro hqbad
    exact EightEqual.paired_traps_impossible_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hcard hb p hsmall hat hct hEq x hx q hq
        hqs hLgen hxpair hpbad hqbad (strict g hg)
  · exact Or.inl (backward p hpbad)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
