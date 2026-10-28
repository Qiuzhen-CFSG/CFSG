module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedResidualLine

/-!
# Direct edge support of the mixed full-kernel failure line

The full kernel lies in the midpoint core. The quadratic edge action therefore
puts its commutator with the endpoint kernel in the last edge seed. Failure of
normalization puts the same line in the starting and midpoint seeds; a strict
slice identifies their intersection with the first edge seed. If these two
edge kernels generate the midpoint stabilizer, the line is fixed there.

The last-edge containment comes from the commutator calculation itself, not
from an inference about an arbitrary intersection of three omega centers.
Source: MS93 (5.12)(1),(3), printed pp.924--927.
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

/-- Every subgroup of the midpoint core has endpoint-kernel movement in
the full last-edge seed, including every central attachment. -/
theorem midpoint_kernel_endpoint_movement_le_edge_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (K : Subgroup (FreeAmalgam d.radical))
    (hK : K ≤ Q d.radical (p.walk.getVert 2)) :
    ⁅K,Z d.radical z ⊓ Q d.radical a⁆ ≤ Z d.radical (p.walk.getVert 3) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono plus_le_D
  have hzt : Adjacent d.radical z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical (p.walk.getVert 3) = true := by
    have hh := adjacent_color_ne d.radical hzt
    rw [p.end_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  rw [commutator_comm]
  exact (commutator_mono inf_le_left (hK.trans (Q_le_adjacent_h d.radical ht hct))).trans
    (cube_edge_seed_commutator_le s hc u hR p.end_color hzt)

/-- Interior edge generation supplies genuine opposite-midpoint fixation
for the full failed-normalization commutator, without a reciprocal-slice premise. -/
theorem backward_failure_line_midpoint_fixed_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z b : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hbcol : color d.radical b = false)
    (hnear : (cosetGraph d.radical).dist b a ≤ 2)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2))
    (hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical b ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ⁅Z d.radical b ⊓ Q d.radical (p.walk.getVert 2),Z d.radical z ⊓ Q d.radical a⁆ ≤
      centralizer (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom :=
    hf ▸ map_mono plus_le_D
  let H := ⁅Z d.radical b ⊓ Q d.radical (p.walk.getVert 2),Z d.radical z ⊓ Q d.radical a⁆
  obtain ⟨_,_,hseeds⟩ := small_backward_kernel_nonnormal_three_seed_line s hc hb p
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p) hbcol hnear hbad
  have hZV : Z d.radical b ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hnear)
  have hHa : H ≤ Z d.radical a :=
    (commutator_mono (inf_le_left.trans hZV) inf_le_right).trans
      (cube_radius_core_commutator_le_seed s hc hb2 u hR a p.start_color)
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hfirst : H ≤ Z d.radical (p.walk.getVert 1) :=
    (le_inf hHa (hseeds.trans (inf_le_left.trans inf_le_right))).trans
      (mixed_strict_seed_intersection_eq_edge s hb2 u hf p.start_color hat hct hstrict).le
  have hlast : H ≤ Z d.radical (p.walk.getVert 3) :=
    midpoint_kernel_endpoint_movement_le_edge_knownSimple hb u him p _ inf_le_right
  have hcent (i : ℕ) (hi : i=1 ∨ i=3) :
      Z d.radical (p.walk.getVert i) ≤ centralizer (Q d.radical (p.walk.getVert i) : Set (FreeAmalgam d.radical)) := by
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
  exact sup_le (le_centralizer_iff.mp (hfirst.trans (hcent 1 (Or.inl rfl))))
    (le_centralizer_iff.mp (hlast.trans (hcent 3 (Or.inr rfl))))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
