module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.LargeImageCases
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.FourImageSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Extension
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Sharpening

/-!
# Full predecessor images in the source replacement argument

Regular turns transfer the predecessor's image order to the forward pair.
Equal predecessor and edge images give the literal product of the two even
kernels. This product identifies the opposite edge with its two-step
displacement. The proved (4.4.1) B-bound and (4.2)(i) neighboring extension
then put that opposite edge in the forward edge times the fixed core.

The induction's fixed-core premise also makes the forward edge invariant
under the next vertex stabilizer. Consequently it is the displacement of
that entire local orbit span under its kernel. `source_stage` applies all
these conclusions to the original failed-span commutator, deriving its
order four from the terminal seed.

The final source switching theorem uses the two-turn argument from
FourImageSource: the backward edge lies in the natural group four positions
earlier, so the escaping radius centralizes both order-four planes and
identifies them. That argument requires no image-size hypothesis. The
preceding reductions and their public statements are preserved.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.2)(i), (4.4.1), and the regular turns in (4.4.4), pp.882, 890--894.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.EightImageSource
open PathCentrality.RegularPaths PathCentrality.RegularPaths.CommutatorPropagation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
/-- A regular turn preserves the literal kernel image order. -/
theorem forward_relIndex_eq_predecessor
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hp : HasTurnConjugators R p) {j : ℕ}
    (heven : Even j) (hj : 2 ≤ j) (hlen : j + 2 ≤ p.walk.length) :
    (Q R (p.walk.getVert j)).relIndex (Q R (p.walk.getVert (j + 2))) =
      (Q R (p.walk.getVert j)).relIndex (Q R (p.walk.getVert (j - 2))) := by
  obtain ⟨k, hk, hturn⟩ := hp j heven hj hlen
  have hkc : act R k (p.walk.getVert j) = p.walk.getVert j := hk
  have hi := relIndex_map_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom)
    (Q R (p.walk.getVert j)) (Q R (p.walk.getVert (j + 2)))
    (MulAut.conj k⁻¹).injective
  rw [← Q_act, ← Q_act, hkc, hturn] at hi
  exact hi.symm

/-- The fixed-core induction premise makes the forward plane normal at the
next even vertex. It does not imply pointwise fixation by its kernel. -/
theorem fixed_edge_normalized_at_neighbor (source : LocalSource L R)
    {c d t : Vertex R} (hc : color R c = false) (hd : color R d = false)
    (hct : Adjacent R c t) (hdt : Adjacent R d t)
    (hfixed : edgeCommutator R c t ≤ fixedCore R d) :
    stabilizer R d ≤ normalizer (edgeCommutator R c t : Set (FreeAmalgam R)) := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hct
    cases ht : color R t <;> simp_all
  rw [← source.local_generation d hd]
  apply sup_le
  · exact (le_centralizer_iff.mp (hfixed.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  · exact (Q_le_adjacent_h R ht hdt).trans (normalizer_commutator_ge_right _ _)

/-- Apply both transfers to the same regular path and the same subgroup. -/
theorem forward_configuration (source : LocalSource L R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hp : HasTurnConjugators R p) {j : ℕ}
    (heven : Even j) (hj : 2 ≤ j) (hlen : j + 2 ≤ p.walk.length)
    (height : (Q R (p.walk.getVert j)).relIndex
      (Q R (p.walk.getVert (j - 2))) = 8)
    {K : Subgroup (FreeAmalgam R)}
    (hforward : K = edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j + 1)))
    (hfixed : K ≤ fixedCore R (p.walk.getVert (j + 2))) :
    (Q R (p.walk.getVert j)).relIndex (Q R (p.walk.getVert (j + 2))) = 8 ∧
      stabilizer R (p.walk.getVert (j + 2)) ≤ normalizer (K : Set (FreeAmalgam R)) := by
  refine ⟨(forward_relIndex_eq_predecessor p hp heven hj hlen).trans height, ?_⟩
  rw [hforward] at hfixed ⊢
  apply fixed_edge_normalized_at_neighbor source
    ((p.vertex_color (by omega)).mpr heven)
    ((p.vertex_color hlen).mpr (by rw [Nat.even_iff] at heven ⊢; omega))
    ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := j) (by omega)))
    _ hfixed
  apply adjacent_symm R
  have ht := (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := j + 1) (by omega))
  simpa only [show j + 1 + 1 = j + 2 by omega] using ht

/-- All incident odd kernels have the same literal quotient image order. -/
theorem edge_relIndex_eq {c s t : Vertex R}
    (hs : Adjacent R c s) (ht : Adjacent R c t) :
    (Q R c).relIndex (Q R s) = (Q R c).relIndex (Q R t) := by
  obtain ⟨g, hg, hst⟩ := stabilizer_transitive_neighbors R c hs ht
  have hgc : act R g c = c := hg
  have hi := relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (Q R c) (Q R s) (MulAut.conj g⁻¹).injective
  rw [← Q_act, ← Q_act, hgc, hst] at hi
  exact hi.symm

/-- The full predecessor product identifies the opposite edge displacement. -/
theorem opposite_edge_eq_displacement_of_full_predecessor
    (geometry : Geometry R)
    {c d t : Vertex R} (hc : color R c = false) (hd : color R d = false)
    (hct : Adjacent R c t) (hdt : Adjacent R d t)
    (hi : (Q R c).relIndex (Q R d) = (Q R c).relIndex (Q R t)) :
    edgeCommutator R d t = ⁅Z R d, Q R c⁆ := by
  exact (commutator_eq_of_centralizing_sup
    (PredecessorControl.predecessor_sup_kernel_eq_edge hc hct hdt hi)
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes d hd)))
    ((Escape.EdgeTransfer.neighbor_kernel_le_stabilizer d t c hd hdt hct).trans
      (Z_normalized R d))).symm

/-- Source local control and neighboring sharpening bound the opposite edge. -/
theorem opposite_edge_le_edge_sup_fixed_of_full_predecessor
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {c d t : Vertex R} (hc : color R c = false) (hd : color R d = false)
    (hct : Adjacent R c t) (hdt : Adjacent R d t)
    (hdist : (cosetGraph R).dist c d = 2)
    (hi : (Q R c).relIndex (Q R d) = (Q R c).relIndex (Q R t))
    (height : (Q R c).relIndex (Q R d) = 8)
    (hcard : Nat.card (edgeCommutator R c t) = 4) :
    edgeCommutator R d t ≤ edgeCommutator R c t ⊔ fixedCore R c := by
  have hne : Q R c ≠ Q R d := by
    intro h
    rw [← h, relIndex_self] at height
    omega
  have hB : edgeCommutator R d t ≤ B R c (geometry.Z_normal c) := by
    rw [opposite_edge_eq_displacement_of_full_predecessor geometry hc hd hct hdt hi]
    exact displacement_le_B common hb hd hc (by rw [SimpleGraph.dist_comm]; exact hdist)
  exact Escape.EdgeTransfer.Sharpening.neighbor_sharpening_of_card_four
    common.large_distance (moduleFacts common) c t d hc hct hdt hne hcard
    (Escape.EdgeTransfer.Extension.neighbor_le_natural_sup_fixedCore
      common.large_distance (moduleFacts common) c t d hc hct hdt hne hB)

/-- The entire local span has the same displacement as the fixed forward edge. -/
theorem span_displacement_eq_fixed_edge
    (common : CommonFacts R source geometry)
    {c d t : Vertex R} (hc : color R c = false) (hd : color R d = false)
    (hct : Adjacent R c t) (hdt : Adjacent R d t)
    (hdist : (cosetGraph R).dist c d = 2)
    (hi : (Q R c).relIndex (Q R d) = (Q R c).relIndex (Q R t))
    (hfixed : edgeCommutator R c t ≤ fixedCore R d) :
    ⁅localZSpan R c d, Q R d⁆ = edgeCommutator R c t := by
  have hgen := PredecessorControl.predecessor_sup_kernel_eq_edge hc hct hdt hi
  have heq : ⁅Z R c, Q R d⁆ = edgeCommutator R c t :=
    commutator_eq_of_centralizing_sup (sup_comm _ _ |>.trans hgen)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes c hc)))
      ((Escape.EdgeTransfer.neighbor_kernel_le_stabilizer c t d hc hct hdt).trans
        (Z_normalized R c))
  have hnorm := fixed_edge_normalized_at_neighbor source hc hd hct hdt hfixed
  apply le_antisymm
  · rw [LocalCommutator.span_commutator_eq_conjugates hd hdist.le common.large_distance, heq]
    apply iSup_le
    intro g
    exact (mem_normalizer_iff_map_conj_eq.mp
      (hnorm ((stabilizer R d).inv_mem g.property))).le
  · rw [← heq]
    exact commutator_mono (Z_le_localZSpan R c d) le_rfl

/-- The actual failed-span stage supplies the full forward kernel product,
its span displacement, and the opposite-edge bound. The extra fixed-core
factor is retained; this is not the requested backward switching equality. -/
theorem source_stage
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a a'} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {t} (ht : Adjacent R a t)
    (hne : ¬ Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R)))
    {g} (hg : g ∈ stabilizer R a)
    (hge : (edgeCommutator R a (p.walk.getVert 1)).map (MulAut.conj g⁻¹).toMonoidHom =
      edgeCommutator R a t)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (n : ℕ) (hn : 0 < n) (hlen : 4 * n + 4 ≤ p.walk.length)
    (hforward : failedSpanCommutator p g = edgeCommutator R
      (p.walk.getVert (p.walk.length - 4 * n)) (p.walk.getVert (p.walk.length - 4 * n + 1)))
    (hfixed : failedSpanCommutator p g ≤ fixedCore R
      (p.walk.getVert (p.walk.length - 4 * n + 2)))
    (hedge : (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
      (Q R (p.walk.getVert (p.walk.length - 4 * n - 1))) = 8)
    (hprev : (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
      (Q R (p.walk.getVert (p.walk.length - 4 * n - 2))) = 8) :
    let c := p.walk.getVert (p.walk.length - 4 * n)
    let d := p.walk.getVert (p.walk.length - 4 * n + 2)
    let s := p.walk.getVert (p.walk.length - 4 * n + 1)
    (Q R c).relIndex (Q R d) = 8 ∧
      stabilizer R d ≤ normalizer (failedSpanCommutator p g) ∧
      Q R d ⊔ Q R c = Q R s ∧
      ⁅localZSpan R c d, Q R d⁆ = failedSpanCommutator p g ∧
      edgeCommutator R d s ≤ failedSpanCommutator p g ⊔ fixedCore R c := by
  let j := p.walk.length - 4 * n
  have hj : 4 ≤ j := by dsimp only [j]; omega
  have hjlen : j + 2 ≤ p.walk.length := by dsimp only [j]; omega
  have heven : Even j := by
    have he : Even p.walk.length := by
      rw [p.length_eq_b]
      exact geometry.even (alpha R) rfl
    dsimp only [j]
    rw [Nat.even_iff] at he ⊢
    omega
  have hc := (p.vertex_color (by omega : j ≤ p.walk.length)).mpr heven
  have hd := (p.vertex_color hjlen).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hct : Adjacent R (p.walk.getVert j) (p.walk.getVert (j + 1)) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by omega))
  have hdt : Adjacent R (p.walk.getVert (j + 2)) (p.walk.getVert (j + 1)) := by
    apply adjacent_symm R
    have hh := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := j + 1) (by omega))
    simpa only [show j + 1 + 1 = j + 2 by omega] using hh
  have hcs : Adjacent R (p.walk.getVert j) (p.walk.getVert (j - 1)) := by
    apply adjacent_symm R
    have hh := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := j - 1) (by omega))
    rwa [show j - 1 + 1 = j by omega] at hh
  have hdist : (cosetGraph R).dist (p.walk.getVert j) (p.walk.getVert (j + 2)) = 2 := by
    rw [Iteration.path_distance p (by omega) hjlen]
    omega
  obtain ⟨hi, hnorm⟩ := forward_configuration source p hp heven (by omega) hjlen
    hprev hforward hfixed
  have hfull : (Q R (p.walk.getVert j)).relIndex (Q R (p.walk.getVert (j + 2))) =
      (Q R (p.walk.getVert j)).relIndex (Q R (p.walk.getVert (j + 1))) :=
    hi.trans (hedge.symm.trans (edge_relIndex_eq hcs hct))
  have hcard := Iteration.EdgeSwitching.seed_card_four common p
    (RegularSource.terminal_seed common hb p hp ht hne hg hge hfail)
  rw [hforward] at hcard hfixed
  exact ⟨hi, hnorm, PredecessorControl.predecessor_sup_kernel_eq_edge hc hct hdt hfull,
    (span_displacement_eq_fixed_edge common hc hd hct hdt hdist hfull hfixed).trans
      hforward.symm,
    (opposite_edge_le_edge_sup_fixed_of_full_predecessor common hb hc hd hct hdt
      hdist hfull hi hcard).trans_eq (congrArg (fun A => A ⊔ fixedCore R _) hforward.symm)⟩

/-- The literal predecessor-image-eight contract, including the j>4 branch,
with no additional premise. The terminal seed supplies the order-four
failed-span plane; regular turns and radius escape give the backward edge. -/
theorem failedSpanLargeImageSwitching_eight
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    FailedSpanLargeImageSwitching R geometry 8 := by
  intro a a' p hp t ht hne g hg hge hfail n hn hlen hforward hfixed
    _htwo _hedge _height _hnorm _hj
  have heven : Even (p.walk.length - 4 * n) := by
    have hh : Even p.walk.length := by
      rw [p.length_eq_b]
      exact geometry.even (alpha R) rfl
    rw [Nat.even_iff] at hh ⊢
    omega
  exact FourImageSource.switching_at_regular_turns common p hp hg heven
    (by omega) (by omega) hforward hfixed
    (Iteration.EdgeSwitching.seed_card_four common p
      (RegularSource.terminal_seed common hb p hp ht hne hg hge hfail))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.EightImageSource
