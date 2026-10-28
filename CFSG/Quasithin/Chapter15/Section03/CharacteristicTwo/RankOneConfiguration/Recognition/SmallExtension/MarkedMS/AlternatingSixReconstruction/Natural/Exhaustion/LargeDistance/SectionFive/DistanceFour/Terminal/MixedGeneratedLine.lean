module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedPairedKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedConjugateKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedPairedGeneration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedSmallRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedPairedKernel

/-!
# Generated critical lines and the entire mixed kernel orbit

At critical distance four the first and third edges are the two endpoint
edges. If their kernels generate the midpoint stabilizer, that stabilizer
fixes the full critical commutator. The mixed radius image has order two,
so every escaping nearby seed has the same commutator line. Conjugating
this fixed line identifies the full seed kernels, including both central
attachments. Consequently the actual backward kernel lies in every
midpoint conjugate of the predecessor core and centralizes the original
midpoint orbit span.

The private imports reuse the preceding near-seed and edge-distance proofs
inside this terminal family. No private declaration occurs in an exported
statement. Source: MS93 (5.12)(1),(3), printed pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
open MixedConjugateKernel
local notation "S" => Equiv.Perm (Fin 6)
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- At distance four the two interior edge kernels are the endpoint
edge kernels. Their generation fixes the full critical commutator. -/
theorem cube_generated_four_critical_line_central
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4) (u : S)
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2)) :
    ⁅Z d.radical a,Z d.radical z⁆ ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let r : CriticalPath d.radical (replacementGeometry h d) z a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hfirst := cube_critical_commutator_le_first_seed s hc u hR p
  have hlast := cube_critical_commutator_le_first_seed s hc u hR r
  change ⁅Z d.radical z,Z d.radical a⁆ ≤ Z d.radical (p.walk.reverse.getVert 1) at hlast
  rw [commutator_comm,SimpleGraph.Walk.getVert_reverse,hl] at hlast
  have hseed (i : ℕ) (hi : i = 1 ∨ i = 3) :
      Z d.radical (p.walk.getVert i) ≤
        centralizer (Q d.radical (p.walk.getVert i) : Set (FreeAmalgam d.radical)) := by
    have hcol : color d.radical (p.walk.getVert i) = true := by
      have hn : ¬ color d.radical (p.walk.getVert i) = false := by
        rw [p.vertex_color (by rcases hi with rfl | rfl <;> omega)]
        rcases hi with rfl | rfl <;> decide
      exact Bool.eq_true_of_not_eq_false hn
    intro y hy
    rw [Z,if_neg (by simp [hcol])] at hy
    exact (mem_omegaCenter_iff.mp hy).2.2
  apply le_centralizer_iff.mp
  rw [←hgen]
  exact sup_le (le_centralizer_iff.mp (hfirst.trans (hseed 1 (Or.inl rfl))))
    (le_centralizer_iff.mp (hlast.trans (hseed 3 (Or.inr rfl))))

include e hz hn in
theorem mixed_four_central_conjugate_kernel_knownSimple
    (hb : replacementDistance h d = 4)
    {a a' z t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2)))
    (hradius : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (V d.radical a) = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hcentral : ⁅Z d.radical z,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    Z d.radical z ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
      Q d.radical (act d.radical x (p.walk.getVert (p.walk.length-2))) := by
  let c := p.walk.getVert (p.walk.length-2)
  let w := act d.radical x⁻¹ z
  have hcancel : act d.radical x w = z := by
    dsimp only [w]
    rw [←act_mul,inv_mul_cancel,act_one]
  by_cases hout : Z d.radical w ≤ Q d.radical c
  · have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hout
    rw [←Z_act,←Q_act,hcancel] at hh
    exact inf_le_left.trans hh
  have hnear := edge_near hat hzt
  have hfix : act d.radical x⁻¹ a = a := (stabilizer d.radical a).inv_mem hx
  have hnear' : (cosetGraph d.radical).dist w a ≤ 2 := by
    rw [show w = act d.radical x⁻¹ z from rfl,←hfix,dist_act]
    exact hnear
  have hw : color d.radical w = false := (action_preserves_color d.radical _ _).trans q.start_color
  obtain ⟨r⟩ := mixed_four_near_critical hb p hw hnear' hout
  obtain ⟨r'⟩ : Nonempty (CriticalPath d.radical (replacementGeometry h d) z (act d.radical x c)) := by
    rw [←hcancel]
    exact ⟨r.act x⟩
  let H := ⁅Z d.radical z,Z d.radical c⁆
  have hHC : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := hcentral
  have hHmap : H.map (MulAut.conj x⁻¹).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ ((le_centralizer_iff.mp hHC)
        ((stabilizer d.radical a).inv_mem hx)))
  have heq : ⁅Z d.radical z,Z d.radical c⁆ = ⁅Z d.radical z,Z d.radical (act d.radical x c)⁆ := by
    have hsame := (mixed_four_near_seed_radius_commutator hb p hradius q hnear).symm.trans
      (mixed_four_near_seed_radius_commutator hb p hradius r hnear')
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hsame
    change H.map (MulAut.conj x⁻¹).toMonoidHom = _ at hh
    rw [hHmap,map_commutator,←Z_act,←Z_act,hcancel] at hh
    exact hh
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hq : (Q d.radical c).relIndex (Z d.radical z) < 4 :=
    critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q
  have hr : (Q d.radical (act d.radical x c)).relIndex (Z d.radical z) < 4 :=
    critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb r'
  exact (small_critical_equal_commutators_kernel s hc q r' hq hr heq).le.trans inf_le_right

include e hz hn in
/-- Every midpoint conjugate of the predecessor core contains the same
full backward seed kernel of the actual mixed selector. -/
theorem mixed_backward_kernel_le_every_conjugate_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a) :
    Z d.radical q.start ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
      Q d.radical (act d.radical x (p.walk.getVert (p.walk.length-2))) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (by omega)
  have hq3 : q.path.walk.getVert 3 = p.walk.getVert 1 := q.overlap 1 (by omega)
  have hgen : Q d.radical (q.path.walk.getVert 1) ⊔ Q d.radical (q.path.walk.getVert 3) =
      stabilizer d.radical (q.path.walk.getVert 2) := by
    rw [q.first,hq3,hq2]
    exact q.generation
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono plus_le_D
  have hcentral := cube_generated_four_critical_line_central s hc hb u hR q.path hgen
  rw [hq2] at hcentral
  exact mixed_four_central_conjugate_kernel_knownSimple (e := e) (hz := hz) (hn := hn) hb p q.path
    (mixed_four_backward_radius_index_knownSimple hb u him p q.path hq2)
    q.adjacent_start q.adjacent_shift x hx hcentral

include e hz hn in
/-- The entire backward seed kernel centralizes the original midpoint
orbit span, since it lies in every conjugate predecessor core. -/
theorem mixed_backward_kernel_centralizes_span_knownSimple
    (hb : replacementDistance h d = 4) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p) :
    Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤
      centralizer (localZSpan d.radical (p.walk.getVert 2) a : Set (FreeAmalgam d.radical)) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hv : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  apply le_centralizer_iff.mp
  rw [localZSpan_eq_conjugates]
  apply iSup_le
  intro x
  rw [←Z_act]
  apply (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q d.radical _ ((action_preserves_color d.radical _ _).trans hv))).trans
  apply centralizer_le
  change Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤
    Q d.radical (act d.radical (x : FreeAmalgam d.radical) (p.walk.getVert 2))
  simpa only [hl] using mixed_backward_kernel_le_every_conjugate_knownSimple
    hb u him p q x x.property

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
