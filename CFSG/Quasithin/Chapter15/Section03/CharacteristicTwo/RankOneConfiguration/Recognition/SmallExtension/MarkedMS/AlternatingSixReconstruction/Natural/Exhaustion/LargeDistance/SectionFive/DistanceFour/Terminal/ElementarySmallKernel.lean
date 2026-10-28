module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.CubeSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ResidualSmallSection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EdgeKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.CubeSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.NonnormalSelection

/-!
# The full backward kernel with two elementary-image actors

An elementary radical image makes the first edge kernel normalize the full
kernel of every small critical path. If that edge and an actor generate the
midpoint residual, and the actor normalizes the full kernel joined with the
midpoint seed, that join lies in the Baumann subgroup. Its quotient over the
midpoint seed has order at most eight. The critical index-two formula then
bounds the original moving-seed slice by two, with the central attachment
retained on both moving covers.

The literal three-pair application uses the simultaneous cubic selector.
It keeps both endpoint actors, their generating equality, the same cubic
and the transported strict slice. On its selected backward path a large
critical image or failure of joint full-kernel normalization is unavoidable.
The second actor is never replaced by one-actor generation. Discharging
joint normalization through the compatible source choices remains the
small-image terminal obligation; this module does not assert that exclusion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.12)(1),(3), printed pp.924--927, with the paired selection of
(5.6) and the small-section argument of (5.2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- Residual invariance of the full small critical kernel join bounds the
actual moving-seed Baumann slice, for every elementary radical image. -/
theorem elementary_small_normalized_slice_le_two
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hel : IsElementaryAbelian 2 (d.radical.map s.projection))
    {c z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (W : Subgroup (FreeAmalgam d.radical))
    (hgen : Ltilde d.radical (p.walk.getVert 2) ≤ Q d.radical (p.walk.getVert 1) ⊔ W)
    (hWN : W ≤ normalizer (((Z d.radical c ⊓ Q d.radical z) ⊔
      Z d.radical (p.walk.getVert 2) : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) ≤ 2 := by
  let a := p.walk.getVert 2
  let t := p.walk.getVert 1
  let K := Z d.radical c ⊓ Q d.radical z
  let J := K ⊔ Z d.radical a
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha : color d.radical a = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hTGa : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr hel.toIsMulCommutative)
  have hTK := (small_critical_end_kernels_normalized_of_abelian_image s hc hab p hsmall).1
  have hTJ : Q d.radical t ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    (le_inf hTK (hTGa.trans (Z_normalized d.radical a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJN : Ltilde d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    hgen.trans (sup_le hTJ hWN)
  have hZV : Z d.radical c ≤ V d.radical a :=
    le_iSup_of_le c (le_iSup_of_le (by rw [p.dist_start (by omega)]) le_rfl)
  have hJV : J ≤ V d.radical a := sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical _ 2)
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (sup_le
      (hZV.trans ((V_le_Q d.radical ha hb2).trans (fun _ hx => hx.1)))
      (Z_le_stabilizer d.radical a))) (inclusion_injective _)
  have hJindex : (Z d.radical a).relIndex J ≤ 8 :=
    (relIndex_le_of_le_right (show J ≤ Z d.radical c ⊔ Z d.radical a from
      sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
        (DistanceFour.adjacent_seed_span_index_le_eight
          (e := e) (hz := hz) (hn := hn) hb2 ha hat hct)
  have hJB := residual_small_radius_le_slice_knownSimple (e := e) hb2 ha J hJV hJN hJindex
  let := finite_Z d.radical c
  have hi := relIndex_le_of_le_left (le_sup_left.trans hJB : K ≤ B d.radical a _)
    (index_ne_zero_of_finite (H := K.subgroupOf (Z d.radical c)))
  change (B d.radical a _).relIndex (Z d.radical c) ≤
    (Z d.radical c ⊓ Q d.radical z).relIndex (Z d.radical c) at hi
  rw [inf_relIndex_left,(small_critical_indices s hc p hsmall).1] at hi
  exact (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c)
    index_ne_zero_of_finite).trans hi

include e hz hn in
/-- The original three-pair selector retains both actors and the same
conjugator in its full-kernel normalization obstruction. -/
theorem cube_strict_backward_paired_kernel_obstruction_knownSimple
    (hb : replacementDistance h d = 4)
    (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          Q d.radical t ⊔ (Q d.radical t).map (MulAut.conj x).toMonoidHom =
            stabilizer d.radical (alpha d.radical) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          Q d.radical t ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
            stabilizer d.radical (alpha d.radical) ∧
          ∃ w, (w = p.walk.getVert 2 ∨ w = act d.radical x (p.walk.getVert 2)) ∧
            ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta) w,
              q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
              (4 ≤ (Q d.radical w).relIndex (Z d.radical (act d.radical g delta)) ∨
                ¬ Z d.radical z ⊔ Z d.radical (act d.radical x z) ≤
                  normalizer (((Z d.radical (act d.radical g delta) ⊓ Q d.radical w) ⊔
                    Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hel : IsElementaryAbelian 2 (d.radical.map s.projection) := by
    let : IsElementaryAbelian 2 (D 6) := elementary_disjointTranspositions (3 : Fin 4)
    rw [hfull]
    exact IsElementaryAbelian.map _
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨t,hat,g,hg,hgt,hct,hi,x,hx,hpair,hx3,r,hr,hrs,hgen,halt⟩ :=
    cube_strict_small_backward_pair s hc hb2 u hfull p hsmall hdelta hstrict
  refine ⟨t,hat,g,hg,hgt,hct,hi,x,hx,hpair,hx3,hgen,?_⟩
  have bound {w : Vertex d.radical}
      (q : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta) w)
      (hqt : q.walk.getVert 1 = t) (hqa : q.walk.getVert 2 = alpha d.radical) :
      4 ≤ (Q d.radical w).relIndex (Z d.radical (act d.radical g delta)) ∨
        ¬ Z d.radical z ⊔ Z d.radical (act d.radical x z) ≤
          normalizer (((Z d.radical (act d.radical g delta) ⊓ Q d.radical w) ⊔
            Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    by_cases hlarge : 4 ≤ (Q d.radical w).relIndex (Z d.radical (act d.radical g delta))
    · exact Or.inl hlarge
    refine Or.inr fun hn => (not_le_of_gt hi) ?_
    have hres : Ltilde d.radical (q.walk.getVert 2) ≤ Q d.radical (q.walk.getVert 1) ⊔
        (Z d.radical z ⊔ Z d.radical (act d.radical x z)) := by
      rw [hqt,hqa,←sup_assoc,hgen]
      exact Ltilde_le_stabilizer _
    simpa only [hqa] using elementary_small_normalized_slice_le_two s hc hb hel q
      (by omega) _ hres (by simpa only [hqa] using hn)
  rcases halt with ⟨q,hqt,hover⟩ | ⟨q,hqt,hover⟩
  · have hqa : q.walk.getVert 2 = alpha d.radical := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
    refine ⟨p.walk.getVert (p.walk.length-2),Or.inl ?_,q,hqt,hqa,bound q hqt hqa⟩
    rw [hl]
  · have hrl : r.walk.length = 4 := r.length_eq_b.trans hb
    have hqa : q.walk.getVert 2 = alpha d.radical := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
    refine ⟨r.walk.getVert (r.walk.length-2),Or.inr ?_,q,hqt,hqa,bound q hqt hqa⟩
    rw [hrl,hr]

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
