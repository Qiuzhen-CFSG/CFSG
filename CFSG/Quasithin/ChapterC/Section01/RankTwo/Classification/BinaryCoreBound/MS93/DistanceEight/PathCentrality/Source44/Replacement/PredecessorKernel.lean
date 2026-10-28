module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.SourceCritical

/-!
# Predecessor kernels in the original backward switching argument

At the actual stage `j = b - 4n`, the radius subgroup lies in `Q_(j-2)`.
If that predecessor kernel has image of order two modulo `Q_j`, the escaping
radius generates its image, and `Q_(j-1)` normalizes the required join.
More generally, normalization failure with radius image of order two forces
an image of order eight on the backward edge and a predecessor-kernel image
of order four or eight. The final theorem retains all original failed-span
inputs and locates precisely such a stage.

This closes the predecessor image-two case; it does not assert the remaining
normalization needed for prescribed replacement.

Source: Meierfrankenfeld--Stellmacher (1993), the backward switching in the
proof of (4.4.4), printed p.894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.PredecessorKernel
open PathCentrality.RegularPaths PathCentrality.RegularPaths.CommutatorPropagation
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem index_two_generation {G : Type*} [Group G]
    (H B A : Subgroup G) (hAH : A ≤ H)
    (hi : B.relIndex H = 2) (hnot : ¬ A ≤ B) : H ≤ A ⊔ B := by
  obtain ⟨u, _, _, hcosets⟩ := relIndex_eq_two_iff_exists_notMem_and.mp hi
  obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp hnot
  have hxu : x * u ∈ B := (hcosets x (hAH hx)).resolve_right hxn
  have hu : u ∈ A ⊔ B := by
    have hh := (A ⊔ B).mul_mem ((A ⊔ B).inv_mem (mem_sup_left hx)) (mem_sup_right hxu)
    simpa only [inv_mul_cancel_left] using hh
  intro y hy
  rcases hcosets y hy with hyu | hyb
  · have hh := (A ⊔ B).mul_mem (mem_sup_right hyu) ((A ⊔ B).inv_mem hu)
    simpa only [mul_inv_cancel_right] using hh
  · exact mem_sup_right hyb

omit [Finite M] in
theorem backward_radius_le_predecessor_kernel
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (n : ℕ) (hn : 0 < n) (hlen : 4 * n + 4 ≤ p.walk.length) :
    VBall R a (4 * n) ≤ Q R (p.walk.getVert (p.walk.length - 4 * n - 2)) := by
  apply Iteration.ball_le_Q_of_dist_add_lt p.start_color
  rw [p.dist_start (by omega), ← p.length_eq_b]
  omega

omit [Finite M] in
theorem backward_radius_normalized_of_predecessor_index_two
    (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (n : ℕ) (hn : 0 < n) (hlen : 4 * n + 4 ≤ p.walk.length)
    (hindex : (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
      (Q R (p.walk.getVert (p.walk.length - 4 * n - 2))) = 2) :
    Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
      normalizer (VBall R a (4 * n) ⊔ Q R (p.walk.getVert (p.walk.length - 4 * n)) :
        Subgroup (FreeAmalgam R)) := by
  let j := p.walk.length - 4 * n
  have hj : 4 ≤ j := by dsimp only [j]; omega
  have hjlen : j ≤ p.walk.length := Nat.sub_le _ _
  have heven : Even j := by
    have hh : Even p.walk.length := by
      rw [p.length_eq_b]
      exact geometry.even (alpha R) rfl
    dsimp only [j]
    rw [Nat.even_iff] at hh ⊢
    omega
  obtain ⟨_,hescape,_⟩ := Iteration.switching_ball_facts common p hg heven hj hjlen
  have hind : p.walk.length - j = 4 * n := by dsimp only [j]; omega
  rw [hind] at hescape
  have hA := backward_radius_le_predecessor_kernel p n hn hlen
  change VBall R a (4 * n) ≤ Q R (p.walk.getVert (j - 2)) at hA
  have hgen : VBall R a (4 * n) ⊔ Q R (p.walk.getVert j) =
      Q R (p.walk.getVert (j - 2)) ⊔ Q R (p.walk.getVert j) := by
    apply le_antisymm
    · exact sup_le_sup_right hA _
    · exact sup_le (index_two_generation _ _ _ hA hindex hescape) le_sup_right
  have hback : Adjacent R (p.walk.getVert (j - 1)) (p.walk.getVert j) := by
    have h := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := j - 1) (by omega))
    rwa [show j - 1 + 1 = j by omega] at h
  have hprev : Adjacent R (p.walk.getVert (j - 1)) (p.walk.getVert (j - 2)) := by
    have h := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := j - 2) (by omega))
    rw [show j - 2 + 1 = j - 1 by omega] at h
    exact adjacent_symm R h
  have hnQ (c : Vertex R) (hc : Adjacent R (p.walk.getVert (j - 1)) c) :
      Q R (p.walk.getVert (j - 1)) ≤ normalizer (Q R c : Set (FreeAmalgam R)) :=
    (show Q R (p.walk.getVert (j - 1)) ≤ stabilizer R c from
      fun _ hx => hx.2 c hc).trans (Q_normalized R c)
  change Q R (p.walk.getVert (j - 1)) ≤ normalizer
    (VBall R a (4 * n) ⊔ Q R (p.walk.getVert j) : Subgroup (FreeAmalgam R))
  rw [hgen]
  exact (le_inf (hnQ _ hprev) (hnQ _ hback)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

private theorem two_normalized_in_small (A P : Subgroup SL) (hAP : A ≤ P)
    (hA : Nat.card A = 2) (hP : Nat.card P ≤ 4) : P ≤ normalizer A := by
  have hm := (A.subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv, hA] at hm
  have hi : (A.subgroupOf P).index = 1 ∨ (A.subgroupOf P).index = 2 := by
    have hn := (A.subgroupOf P).index_ne_zero_of_finite
    omega
  rcases hi with hi | hi
  · have he : A = P := eq_of_le_of_card_ge hAP (by omega)
    rw [he]
    exact P.le_normalizer
  · exact (normal_subgroupOf_iff_le_normalizer hAP).mp (normal_of_index_eq_two hi)

private theorem two_image_card_dvd_eight (P : Subgroup SL) (hP : IsPGroup 2 P) :
    Nat.card P ∣ 8 := by
  obtain ⟨S,hS⟩ := hP.exists_le_sylow
  have hc : Nat.card (S : Subgroup SL) = 8 := by
    rw [S.card_eq_multiplicity, Matrix.PSL3Two.card_SL]
    decide +kernel
  exact hc ▸ card_dvd_of_le hS

/-- On the actual backward path, normalization can fail only with a full
Sylow image on the backward edge and a larger predecessor-kernel image. -/
theorem backward_normalization_failure_large_images
    (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (n : ℕ) (hn : 0 < n) (hlen : 4 * n + 4 ≤ p.walk.length)
    (htwo : (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
      (VBall R a (4 * n)) = 2)
    (hfailure : ¬ Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
      normalizer (VBall R a (4 * n) ⊔ Q R (p.walk.getVert (p.walk.length - 4 * n)) :
        Subgroup (FreeAmalgam R))) :
    (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
        (Q R (p.walk.getVert (p.walk.length - 4 * n - 1))) = 8 ∧
      ((Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
        (Q R (p.walk.getVert (p.walk.length - 4 * n - 2))) = 4 ∨
       (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
        (Q R (p.walk.getVert (p.walk.length - 4 * n - 2))) = 8) := by
  let j := p.walk.length - 4 * n
  have hj : 4 ≤ j := by dsimp only [j]; omega
  have hjlen : j ≤ p.walk.length := Nat.sub_le _ _
  have heven : Even j := by
    have hh : Even p.walk.length := by
      rw [p.length_eq_b]
      exact geometry.even (alpha R) rfl
    dsimp only [j]
    rw [Nat.even_iff] at hh ⊢
    omega
  have hc := (p.vertex_color hjlen).mpr heven
  have hs : Adjacent R (p.walk.getVert j) (p.walk.getVert (j - 1)) := by
    apply adjacent_symm R
    have h := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := j - 1) (by omega))
    rwa [show j - 1 + 1 = j by omega] at h
  have hd : color R (p.walk.getVert (j - 2)) = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hcd : (cosetGraph R).dist (p.walk.getVert (j - 2)) (p.walk.getVert j) = 2 := by
    rw [Iteration.path_distance p (by omega) hjlen]
    omega
  have hS : Q R (p.walk.getVert (j - 1)) ≤ stabilizer R (p.walk.getVert j) :=
    fun _ hx => hx.2 _ (adjacent_symm R hs)
  have hN : Q R (p.walk.getVert (j - 2)) ≤ stabilizer R (p.walk.getVert j) :=
    Q_le_stabilizer_of_dist_two R _ _ hd hcd
  have hscol : color R (p.walk.getVert (j - 1)) = true := by
    have hne := adjacent_color_ne R hs
    cases hh : color R (p.walk.getVert (j - 1)) <;> simp_all
  have hds : Adjacent R (p.walk.getVert (j - 2)) (p.walk.getVert (j - 1)) := by
    have h := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := j - 2) (by omega))
    rwa [show j - 2 + 1 = j - 1 by omega] at h
  have hNS : Q R (p.walk.getVert (j - 2)) ≤ Q R (p.walk.getVert (j - 1)) :=
    Q_le_adjacent_h R hscol hds
  obtain ⟨_,hescape,hA⟩ := Iteration.switching_ball_facts common p hg heven hj hjlen
  have hind : p.walk.length - j = 4 * n := by dsimp only [j]; omega
  rw [hind] at hescape hA
  have hAN := backward_radius_le_predecessor_kernel p n hn hlen
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) _ hc
  have hP : IsPGroup 2 (model.actorImage (Q R (p.walk.getVert (j - 1)))) :=
    (Escape.EdgeTransfer.edge_kernel_two source _ _ hc hs).comap_subtype.map model.projection
  have hNI : IsPGroup 2 (model.actorImage (Q R (p.walk.getVert (j - 2)))) :=
    ((Escape.EdgeTransfer.edge_kernel_two source _ _ hc hs).to_le hNS).comap_subtype.map
      model.projection
  have hPdiv := two_image_card_dvd_eight _ hP
  have hNdiv := two_image_card_dvd_eight _ hNI
  rw [model.actorImage_card _ hS] at hPdiv
  rw [model.actorImage_card _ hN] at hNdiv
  have hPnot : ¬ (Q R (p.walk.getVert j)).relIndex
      (Q R (p.walk.getVert (j - 1))) ≤ 4 := by
    intro hsmall
    apply hfailure
    apply (Iteration.EdgeSwitching.radius_normalized_iff_actorImage_normalized
      model (hA.trans hS) hS).mpr
    apply two_normalized_in_small _ _ (map_mono (comap_mono hA))
    · exact (model.actorImage_card _ (hA.trans hS)).trans htwo
    · change Nat.card (model.actorImage (Q R (p.walk.getVert (j - 1)))) ≤ 4
      rwa [model.actorImage_card _ hS]
  have hNnot1 : (Q R (p.walk.getVert j)).relIndex
      (Q R (p.walk.getVert (j - 2))) ≠ 1 :=
    fun h => hescape (hAN.trans (relIndex_eq_one.mp h))
  have hNnot2 : (Q R (p.walk.getVert j)).relIndex
      (Q R (p.walk.getVert (j - 2))) ≠ 2 :=
    fun h => hfailure (backward_radius_normalized_of_predecessor_index_two
      common p hg n hn hlen h)
  have hPD := Nat.mem_divisors.mpr ⟨hPdiv,(by decide : 8 ≠ 0)⟩
  have hND := Nat.mem_divisors.mpr ⟨hNdiv,(by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1,2,4,8} : Finset ℕ) by decide] at hPD hND
  simp only [Finset.mem_insert,Finset.mem_singleton] at hPD hND
  dsimp only [j] at hPD hND hPnot hNnot1 hNnot2
  omega

/-- The original failed-span inputs retain only the full-Sylow backward edge
and larger predecessor-kernel image as a possible normalization obstruction. -/
theorem failed_span_two_image_failure
    (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (_hp : HasTurnConjugators R p)
    {t : Vertex R} (_ht : Adjacent R a t)
    (_hne : ¬ Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (_hge : (edgeCommutator R a (p.walk.getVert 1)).map
      (MulAut.conj g⁻¹).toMonoidHom = edgeCommutator R a t)
    (_hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hnorm : ¬ BackwardTwoImageNormalization p (failedSpanCommutator p g)) :
    ∃ n : ℕ, 0 < n ∧ 4 * n + 4 ≤ p.walk.length ∧
      failedSpanCommutator p g = edgeCommutator R
        (p.walk.getVert (p.walk.length - 4 * n))
        (p.walk.getVert (p.walk.length - 4 * n + 1)) ∧
      failedSpanCommutator p g ≤ fixedCore R
        (p.walk.getVert (p.walk.length - 4 * n + 2)) ∧
      (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
        (VBall R a (4 * n)) = 2 ∧
      (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
        (Q R (p.walk.getVert (p.walk.length - 4 * n - 1))) = 8 ∧
      ((Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
        (Q R (p.walk.getVert (p.walk.length - 4 * n - 2))) = 4 ∨
       (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
        (Q R (p.walk.getVert (p.walk.length - 4 * n - 2))) = 8) ∧
      ¬ Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
        normalizer (VBall R a (4 * n) ⊔ Q R
          (p.walk.getVert (p.walk.length - 4 * n)) : Subgroup (FreeAmalgam R)) := by
  classical
  change ¬ ∀ n : ℕ, 0 < n → 4 * n + 4 ≤ p.walk.length →
    failedSpanCommutator p g = edgeCommutator R
      (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n + 1)) →
    failedSpanCommutator p g ≤ fixedCore R
      (p.walk.getVert (p.walk.length - 4 * n + 2)) →
    (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
      (VBall R a (4 * n)) = 2 →
    Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
      normalizer (VBall R a (4 * n) ⊔ Q R
        (p.walk.getVert (p.walk.length - 4 * n)) : Subgroup (FreeAmalgam R)) at hnorm
  push Not at hnorm
  obtain ⟨n,hn,hlen,hforward,hfixed,htwo,hfailure⟩ := hnorm
  obtain ⟨hedge,hprev⟩ := backward_normalization_failure_large_images common p hg n hn hlen
    htwo hfailure
  exact ⟨n,hn,hlen,hforward,hfixed,htwo,hedge,hprev,hfailure⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.PredecessorKernel
