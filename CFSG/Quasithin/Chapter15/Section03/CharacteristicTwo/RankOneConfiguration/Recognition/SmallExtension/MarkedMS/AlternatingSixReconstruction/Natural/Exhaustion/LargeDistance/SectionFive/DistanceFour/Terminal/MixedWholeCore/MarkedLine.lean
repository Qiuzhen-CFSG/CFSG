module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedPairLift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.ConjugateKernel

/-!
# Fixation of the conjugate mixed source failure line

The source paired conjugator preserves the original first-edge seed. A strict
slice identifies this seed with the intersection of the starting and midpoint
seeds. Consequently the conjugate failure line lies in the same original
compatible triple as the first line, and the actual starting stabilizer fixes
it. All full seed kernels and central attachments are retained.

Fixation by the opposite midpoint stabilizer and the two estimates for the
whole residual core remain separate source obligations; this does not assert
the mixed terminal exclusion.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(3), pp.926--927.
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

/-- Preserving the original first edge makes the conjugate failed-normalization
line fixed at the original starting vertex, without identifying its full kernel
with the original backward kernel. -/
theorem conjugate_failure_line_fixed_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hmark : x ∈ normalizer (Z d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)))
    (hbad : ¬ Z d.radical (act d.radical x z) ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2))) ⊔
        Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let H := ⁅Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)),
      Z d.radical (act d.radical x z) ⊓ Q d.radical a⁆
    Nat.card H = 2 ∧ H ≤ Z d.radical q.edge ∧
      H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      H ≤ Z d.radical q.start ⊓ Z d.radical (p.walk.getVert 2) ⊓
        Z d.radical (act d.radical x z) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.path.walk.length = 4 := q.path.length_eq_b.trans hb
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hnear : (cosetGraph d.radical).dist q.start a ≤ 2 := by
    simpa only [hq2] using (q.path.dist_start (i := 2) (by omega)).le
  have hxa : act d.radical x a = a := hx
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom :=
    hf ▸ map_mono plus_le_D
  have hsmall := critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb (p.act x)
  have hnearx : (cosetGraph d.radical).dist q.start (act d.radical x a) ≤ 2 := by rwa [hxa]
  have hh := small_backward_kernel_nonnormal_three_seed_line s hc hb (p.act x) hsmall
    q.path.start_color hnearx
  simp only [CriticalPath.act,actWalk_getVert,hxa] at hh
  obtain ⟨_,hcard,hseeds⟩ := hh hbad
  let H := ⁅Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)),
    Z d.radical (act d.radical x z) ⊓ Q d.radical a⁆
  change Nat.card H = 2 at hcard
  change H ≤ Z d.radical q.start ⊓ Z d.radical (act d.radical x (p.walk.getVert 2)) ⊓
    Z d.radical (act d.radical x z) at hseeds
  have hZV : Z d.radical q.start ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hnear)
  have hHa : H ≤ Z d.radical a :=
    (commutator_mono (inf_le_left.trans hZV) inf_le_right).trans
      (cube_radius_core_commutator_le_seed s hc hb2 u hR a p.start_color)
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hvt : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hinter := mixed_strict_seed_intersection_eq_edge s hb2 u hf p.start_color hat hvt hstrict
  have hsame : Z d.radical a ⊓ Z d.radical (act d.radical x (p.walk.getVert 2)) =
      Z d.radical a ⊓ Z d.radical (p.walk.getVert 2) := by
    have he := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hinter
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,←Z_act,←Z_act,hxa] at he
    have hm : (Z d.radical (p.walk.getVert 1)).map (MulAut.conj x⁻¹).toMonoidHom =
        Z d.radical (p.walk.getVert 1) := mem_normalizer_iff_map_conj_eq.mp
          ((normalizer (Z d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical))).inv_mem hmark)
    rw [hm] at he
    exact he.trans hinter.symm
  have hHv : H ≤ Z d.radical (p.walk.getVert 2) :=
    ((le_inf hHa (hseeds.trans (inf_le_left.trans inf_le_right))).trans hsame.le).trans inf_le_right
  have hi : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical q.start) := by rwa [q.index_eq]
  have htriple := mixed_strict_compatible_triple_central s hb2 u hf p.start_color
    q.adjacent_start q.adjacent_shift hat hvt hi hstrict q.generation
  have hedge := mixed_strict_seed_intersection_eq_edge s hb2 u hf p.start_color
    q.adjacent_start q.adjacent_shift hi
  have hHback : H ≤ Z d.radical q.start := hseeds.trans (inf_le_left.trans inf_le_left)
  exact ⟨hcard,(le_inf hHa hHback).trans hedge.le,
    (le_inf (le_inf hHback hHa) hHv).trans htriple,
    le_inf (le_inf hHback hHv) (hseeds.trans inf_le_right)⟩

omit [Finite G] in
/-- A line fixed at the starting vertex belongs to a seed exactly when it
belongs to its conjugate by an element of that stabilizer. -/
theorem fixed_line_le_seed_iff_conjugate
    {a z : Vertex d.radical} (H : Subgroup (FreeAmalgam d.radical))
    (hfix : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a) :
    H ≤ Z d.radical (act d.radical x z) ↔ H ≤ Z d.radical z := by
  have hm : H.map (MulAut.conj x⁻¹).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hfix ((stabilizer d.radical a).inv_mem hx)))
  rw [Z_act]
  have he : H.map (MulAut.conj x⁻¹).toMonoidHom ≤
      (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom ↔ H ≤ Z d.radical z :=
    map_le_map_iff_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
      (MulAut.conj x⁻¹).injective
  rwa [hm] at he

/-- The actual strict mixed source configuration has an order-two failure
line fixed by the whole starting stabilizer in either endpoint orientation.
The marked paired conjugator is constructed from the original hypotheses. -/
theorem strict_selected_fixed_failure_line_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    ∃ q : MixedBackwardShift (h := h) p,
      ∃ x ∈ stabilizer d.radical (alpha d.radical),
        Q d.radical q.edge ⊔ Q d.radical (act d.radical x⁻¹ q.edge) =
          stabilizer d.radical (alpha d.radical) ∧
        Q d.radical q.edge ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
          stabilizer d.radical (alpha d.radical) ∧
        Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2) ≤
          Q d.radical (act d.radical x (p.walk.getVert 2)) ∧
        x ∈ normalizer ((Z d.radical (alpha d.radical) ⊓
          Z d.radical (p.walk.getVert 2) : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ∃ H : Subgroup (FreeAmalgam d.radical),
          (H = ⁅Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2),
              Z d.radical z ⊓ Q d.radical (alpha d.radical)⁆ ∨
            H = ⁅Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2)),
              Z d.radical (act d.radical x z) ⊓ Q d.radical (alpha d.radical)⁆) ∧
          Nat.card H = 2 ∧ H ≤ Z d.radical q.edge ∧
          H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
          H ≤ Z d.radical q.start ⊓ Z d.radical (p.walk.getVert 2) ⊓
            Z d.radical z ⊓ Z d.radical (act d.radical x z) := by
  obtain ⟨q,x,hx,hpair,hend,hkernel,hmark⟩ :=
    strict_selected_marked_pair_knownSimple hb u him p hstrict
  refine ⟨q,x,hx,hpair,hend,hkernel,hmark,?_⟩
  by_cases hbad : ¬ Z d.radical z ≤ normalizer
      (((Z d.radical q.start ⊓ Q d.radical (p.walk.getVert 2)) ⊔
        Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _)
  · obtain ⟨hcard,hedge,hfix,hseeds⟩ :=
      mixed_backward_failure_line_knownSimple hb u him p q hstrict hbad
    refine ⟨_,Or.inl rfl,hcard,hedge,hfix,le_inf hseeds ?_⟩
    exact (fixed_line_le_seed_iff_conjugate _ hfix x hx).mpr (hseeds.trans inf_le_right)
  · have hnorm := Classical.not_not.mp hbad
    have hbadx : ¬ Z d.radical (act d.radical x z) ≤ normalizer
        (((Z d.radical q.start ⊓ Q d.radical (act d.radical x (p.walk.getVert 2))) ⊔
          Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      intro hh
      exact paired_normalization_false_knownSimple hb u him p q hstrict x hend hnorm
        (backward_kernel_normalization_transfer_knownSimple hb u him p q _ _
          (le_inf inf_le_left hkernel) inf_le_left (le_sup_right.trans_eq hend) hh)
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb
    have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using
        p.walk.adj_getVert_succ (i := 0) (by omega)
    have hvt : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
      adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
        (p.walk.adj_getVert_succ (i := 1) (by omega)))
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    have hf : d.radical.map s.projection = plus.map (MulAut.conj u).toMonoidHom := by
      rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    have hinter := mixed_strict_seed_intersection_eq_edge s (by omega) u hf
      p.start_color hat hvt hstrict
    rw [hinter] at hmark
    obtain ⟨hcard,hedge,hfix,hseeds⟩ :=
      conjugate_failure_line_fixed_knownSimple hb u him p q hstrict x hx hmark hbadx
    refine ⟨_,Or.inr rfl,hcard,hedge,hfix,?_⟩
    exact le_inf (le_inf (hseeds.trans inf_le_left)
      ((fixed_line_le_seed_iff_conjugate _ hfix x hx).mp (hseeds.trans inf_le_right)))
      (hseeds.trans inf_le_right)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
