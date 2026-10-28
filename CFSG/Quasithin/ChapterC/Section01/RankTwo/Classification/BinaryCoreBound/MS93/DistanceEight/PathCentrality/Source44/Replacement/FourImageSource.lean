module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.LargeImageCases
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The predecessor-image-four branch of MS93 backward switching

At a regular turn at j, conjugating the forward edge and its fixed-core
bound puts the backward edge in D_(j-2). A residual turn at j-2 then fixes
that backward edge pointwise and carries it to the edge at j-4. Thus the
backward edge lies in U_(j-4), and the radius ball centered at the original
a centralizes it by distance. The same escaping ball centralizes the
failed-span plane. Both planes have order four in the natural eight-group,
so faithfulness identifies them.

This proves the literal image-four switching contract. The geometric
calculation also works without image-size assumptions; it never asserts
normality of an involution image in a Sylow group or identifies D with Z.
The earlier predecessor-normalization and moved-line reductions are retained.
Final prescribed-replacement assembly belongs to its separate source owner.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the radius and regular-turn argument in (4.4.4), printed p.894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.FourImageSource
open PathCentrality.RegularPaths PathCentrality.RegularPaths.CommutatorPropagation
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem two_normalized_in_four (A N : Subgroup SL) (hAN : A ≤ N)
    (hA : Nat.card A = 2) (hN : Nat.card N = 4) : N ≤ normalizer A := by
  have hm := (A.subgroupOf N).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv, hA, hN] at hm
  exact (normal_subgroupOf_iff_le_normalizer hAN).mp
    (normal_of_index_eq_two (by omega))

/-- An index-two radius image is invariant under the predecessor image.
This does not claim invariance under the larger backward edge image. -/
theorem radius_normalized_by_predecessor
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (n : ℕ) (hn : 0 < n) (hlen : 4 * n + 4 ≤ p.walk.length)
    (model : LocalModel (p.walk.getVert (p.walk.length - 4 * n)))
    (htwo : (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
      (VBall R a (4 * n)) = 2)
    (hfour : (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
      (Q R (p.walk.getVert (p.walk.length - 4 * n - 2))) = 4) :
    Q R (p.walk.getVert (p.walk.length - 4 * n - 2)) ≤
      normalizer (VBall R a (4 * n) ⊔ Q R (p.walk.getVert (p.walk.length - 4 * n)) :
        Subgroup (FreeAmalgam R)) := by
  have heven : Even (p.walk.length - 4 * n - 2) := by
    have hh : Even p.walk.length := by
      rw [p.length_eq_b]
      exact geometry.even (alpha R) rfl
    rw [Nat.even_iff] at hh ⊢
    omega
  have hd := (p.vertex_color (by omega)).mpr heven
  have hN : Q R (p.walk.getVert (p.walk.length - 4 * n - 2)) ≤
      stabilizer R (p.walk.getVert (p.walk.length - 4 * n)) := by
    apply Q_le_stabilizer_of_dist_two R _ _ hd
    rw [Iteration.path_distance p (by omega) (by omega)]
    omega
  have hAN := PredecessorKernel.backward_radius_le_predecessor_kernel p n hn hlen
  apply (Iteration.EdgeSwitching.radius_normalized_iff_actorImage_normalized
    model (hAN.trans hN) hN).mpr
  apply two_normalized_in_four _ _ (map_mono (comap_mono hAN))
  · exact (model.actorImage_card _ (hAN.trans hN)).trans htwo
  · exact (model.actorImage_card _ hN).trans hfour

private theorem fixed_plane_normalized (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false)
    {K A N : Subgroup (FreeAmalgam R)} (hK : K ≤ U R c) (hcard : Nat.card K = 4)
    (hA : A ≤ stabilizer R c) (hN : N ≤ stabilizer R c)
    (hescape : ¬ A ≤ Q R c) (hcomm : ⁅K,A⁆ = ⊥)
    (hnorm : N ≤ normalizer (A ⊔ Q R c : Subgroup (FreeAmalgam R))) :
    N ≤ normalizer K := by
  have hKQ : K ≤ centralizer (Q R c : Set (FreeAmalgam R)) :=
    (hK.trans (U_le_Z R c)).trans
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes c hc))
  have hKJ : ⁅K,A ⊔ Q R c⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
      (le_centralizer_iff.mp hKQ)
  rw [Iteration.EdgeSwitching.plane_eq_natural_centralizer common hc hK hcard
    (sup_le hA (show Q R c ≤ stabilizer R c from fun _ hx => hx.1))
    (fun h => hescape (le_sup_left.trans h)) hKJ]
  exact (le_inf (hN.trans (U_normalized c))
    (hnorm.trans (normalizer_le_normalizer_centralizer (A ⊔ Q R c)))).trans
      inf_normalizer_le_normalizer_inf

omit [Finite M] in
private theorem moved_plane_card_two
    (T K N : Subgroup (FreeAmalgam R)) [Finite T] (hT : IsPGroup 2 T)
    (hKT : K ≤ T) (hNT : N ≤ T) (hnorm : N ≤ normalizer K)
    (hcard : Nat.card K = 4) (hne : ⁅K,N⁆ ≠ ⊥) : Nat.card (⁅K,N⁆ : Subgroup _) = 2 := by
  let : Finite K := Finite.of_injective (inclusion hKT) (inclusion_injective _)
  have hDK : ⁅K,N⁆ ≤ K := le_normalizer_iff_commutator_le_left.mp hnorm
  let : Finite (⁅K,N⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hDK) (inclusion_injective _)
  have hproper : ⁅K,N⁆ ≠ K := by
    intro he
    have hz : K ≤ ⊥ := le_of_le_sup_commutator_of_isNilpotent T K ⊥ N
      hT.isNilpotent hKT bot_le hNT
      (by rw [(⊥ : Subgroup (FreeAmalgam R)).normalizer_eq_top]; exact le_top)
      (by rw [he, bot_sup_eq])
    have hk : K = ⊥ := le_bot_iff.mp hz
    rw [hk, card_bot] at hcard
    omega
  have hdiv := card_dvd_of_le hDK
  rw [hcard] at hdiv
  have hd := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1,2,4} : Finset ℕ) by decide] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  have hpos := (one_lt_card_iff_ne_bot _).mpr hne
  have hn4 : Nat.card (⁅K,N⁆ : Subgroup _) ≠ 4 := by
    intro hh
    exact hproper (eq_of_le_of_card_ge hDK (by omega))
  omega

/-- At the literal source stage, the predecessor preserves K. Either switching
holds, or its action on K moves an order-two subgroup inside the forward fixed
core. The final switching theorem below closes the source case directly through
regular turns, without excluding this row by quotient data alone. -/
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
    (htwo : (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
      (VBall R a (4 * n)) = 2)
    (hfour : (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
      (Q R (p.walk.getVert (p.walk.length - 4 * n - 2))) = 4) :
    Q R (p.walk.getVert (p.walk.length - 4 * n - 2)) ≤
        normalizer (failedSpanCommutator p g) ∧
      (failedSpanCommutator p g = edgeCommutator R
        (p.walk.getVert (p.walk.length - 4 * n))
        (p.walk.getVert (p.walk.length - 4 * n - 1)) ∨
      (Nat.card (⁅failedSpanCommutator p g,
        Q R (p.walk.getVert (p.walk.length - 4 * n - 2))⁆ : Subgroup _) = 2 ∧
        ⁅failedSpanCommutator p g, Q R (p.walk.getVert (p.walk.length - 4 * n - 2))⁆ ≤
          failedSpanCommutator p g ⊓ fixedCore R
            (p.walk.getVert (p.walk.length - 4 * n + 2)) ∧
        Q R (p.walk.getVert (p.walk.length - 4 * n - 2)) ≤
          centralizer ((⁅failedSpanCommutator p g,
            Q R (p.walk.getVert (p.walk.length - 4 * n - 2))⁆ :
              Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)))) := by
  let j := p.walk.length - 4 * n
  have hj : 4 ≤ j := by dsimp only [j]; omega
  have hjlen : j + 2 ≤ p.walk.length := by dsimp only [j]; omega
  have heven : Even j := by
    have hh : Even p.walk.length := by
      rw [p.length_eq_b]
      exact geometry.even (alpha R) rfl
    dsimp only [j]
    rw [Nat.even_iff] at hh ⊢
    omega
  have hc := (p.vertex_color (by omega : j ≤ p.walk.length)).mpr heven
  have hs : Adjacent R (p.walk.getVert j) (p.walk.getVert (j - 1)) := by
    have hh := p.walk.adj_getVert_succ (i := j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at hh
    exact adjacent_symm R ((cosetGraph_adj R _ _).mp hh)
  have ht' : Adjacent R (p.walk.getVert j) (p.walk.getVert (j + 1)) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by omega))
  have hds : Adjacent R (p.walk.getVert (j - 2)) (p.walk.getVert (j - 1)) := by
    have hh := p.walk.adj_getVert_succ (i := j - 2) (by omega)
    rw [show j - 2 + 1 = j - 1 by omega] at hh
    exact (cosetGraph_adj R _ _).mp hh
  have hscol : color R (p.walk.getVert (j - 1)) = true := by
    have hh := adjacent_color_ne R hs
    cases hscol : color R (p.walk.getVert (j - 1)) <;> simp_all
  have hNS : Q R (p.walk.getVert (j - 2)) ≤ Q R (p.walk.getVert (j - 1)) :=
    Q_le_adjacent_h R hscol hds
  have hS : Q R (p.walk.getVert (j - 1)) ≤ stabilizer R (p.walk.getVert j) :=
    fun _ hx => hx.2 _ (adjacent_symm R hs)
  have hKU : failedSpanCommutator p g ≤ U R (p.walk.getVert j) := by
    rw [hforward]
    exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) _ _ hc ht'
  have hcard := Iteration.EdgeSwitching.seed_card_four common p
    (RegularSource.terminal_seed common hb p hp ht hne hg hge hfail)
  obtain ⟨hcomm,hescape,hA⟩ := Iteration.switching_ball_facts common p hg heven hj (by omega)
  have hind : p.walk.length - j = 4 * n := by dsimp only [j]; omega
  rw [hind] at hcomm hescape hA
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) _ hc
  have hnorm := fixed_plane_normalized common hc hKU hcard (hA.trans hS) (hNS.trans hS)
    hescape hcomm (radius_normalized_by_predecessor p n hn hlen model htwo hfour)
  refine ⟨hnorm, ?_⟩
  by_cases hcentral : ⁅failedSpanCommutator p g, Q R (p.walk.getVert (j - 2))⁆ = ⊥
  · left
    apply edge_switch_of_image_four common model hc hs ht' hforward hcard hNS _ hcentral hfour
    intro h
    have hh := relIndex_eq_one.mpr h
    change (Q R (p.walk.getVert j)).relIndex (Q R (p.walk.getVert (j - 2))) = 4 at hfour
    omega
  · right
    have hDK := le_normalizer_iff_commutator_le_left.mp hnorm
    let := finite_stabilizer R (p.walk.getVert (j - 1))
    let : Finite (Q R (p.walk.getVert (j - 1))) := Finite.of_injective
      (inclusion (show Q R (p.walk.getVert (j - 1)) ≤ stabilizer R (p.walk.getVert (j - 1))
        from fun _ hx => hx.1)) (inclusion_injective _)
    have hline := moved_plane_card_two (Q R (p.walk.getVert (j - 1))) _ _
      (Escape.EdgeTransfer.edge_kernel_two source _ _ hc hs)
      (hKU.trans ((U_le_Z R _).trans
        (Escape.EdgeTransfer.edge_Z_le_Q common.large_distance _ _ hc hs)))
      hNS hnorm hcard hcentral
    exact ⟨hline, le_inf hDK (hDK.trans hfixed),
      (normalizer_commutator_ge_right _ _).trans
        (normalizer_le_centralizer_of_card_two _ hline)⟩

/-- Conjugate the forward fixed-core bound by the turn at j, then use a
residual turn at j-2 to place the backward edge in the natural group at j-4.
No equality between the two edges at j is used. -/
theorem backward_edge_le_preceding_natural
    (common : CommonFacts R source geometry)
    {a a'} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {j : ℕ} (heven : Even j) (hj : 4 ≤ j) (hlen : j + 2 ≤ p.walk.length)
    (hfixed : edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j + 1)) ≤
      fixedCore R (p.walk.getVert (j + 2))) :
    edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j - 1)) ≤
      U R (p.walk.getVert (j - 4)) := by
  have hadj (i : ℕ) (hi : i < p.walk.length) :
      Adjacent R (p.walk.getVert i) (p.walk.getVert (i + 1)) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ hi)
  have hd : color R (p.walk.getVert (j - 2)) = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have he : color R (p.walk.getVert (j - 4)) = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hcs : Adjacent R (p.walk.getVert j) (p.walk.getVert (j - 1)) :=
    adjacent_symm R (by simpa only [show j - 1 + 1 = j by omega] using hadj (j - 1) (by omega))
  have hsd : Adjacent R (p.walk.getVert (j - 1)) (p.walk.getVert (j - 2)) :=
    adjacent_symm R (by simpa only [show j - 2 + 1 = j - 1 by omega] using hadj (j - 2) (by omega))
  obtain ⟨g, hg, hturn⟩ := hp j heven (by omega) hlen
  have hgc : act R g (p.walk.getVert j) = p.walk.getVert j := hg
  have hmiddle : act R g (p.walk.getVert (j + 1)) = p.walk.getVert (j - 1) := by
    apply Iteration.turn_middle (geometry := geometry) _ (hadj j (by omega))
      (by simpa only [show j + 1 + 1 = j + 2 by omega] using hadj (j + 1) (by omega))
      hcs hsd hg hturn
    rw [SimpleGraph.dist_comm, Iteration.path_distance p (by omega) (by omega)]
    omega
  have hEfixed : edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j - 1)) ≤
      fixedCore R (p.walk.getVert (j - 2)) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hfixed
    rwa [← edgeCommutator_act, hgc, hmiddle, ← Escape.EdgeTransfer.fixedCore_act, hturn] at hh
  obtain ⟨l, hl, hturn'⟩ := hp (j - 2)
    (by rw [Nat.even_iff] at heven ⊢; omega) (by omega) (by omega)
  have hturn'' : act R l (p.walk.getVert j) = p.walk.getVert (j - 4) := by
    simpa only [show j - 2 + 2 = j by omega, show j - 2 - 2 = j - 4 by omega] using hturn'
  have hEeq : edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j - 1)) =
      edgeCommutator R (p.walk.getVert (j - 4)) (p.walk.getVert (j - 3)) := by
    apply Iteration.transport_edge_of_fixed (geometry := geometry) source hd _
      (adjacent_symm R hsd) (adjacent_symm R hcs)
      (adjacent_symm R (by simpa only [show j - 3 + 1 = j - 2 by omega] using hadj (j - 3) (by omega)))
      (adjacent_symm R (by simpa only [show j - 4 + 1 = j - 3 by omega] using hadj (j - 4) (by omega)))
      hl hturn'' rfl hEfixed
    rw [SimpleGraph.dist_comm, Iteration.path_distance p (by omega) (by omega)]
    omega
  rw [hEeq]
  exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (moduleFacts common) _ _ he
      (by simpa only [show j - 4 + 1 = j - 3 by omega] using hadj (j - 4) (by omega))


/-- The backward edge centralizes the source radius because that radius
lies in the kernel four positions earlier. -/
theorem backward_edge_centralizes_ball
    (common : CommonFacts R source geometry)
    {a a'} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {j : ℕ} (heven : Even j) (hj : 4 ≤ j) (hlen : j + 2 ≤ p.walk.length)
    (hfixed : edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j + 1)) ≤
      fixedCore R (p.walk.getVert (j + 2))) :
    edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j - 1)) ≤
      centralizer (VBall R a (p.walk.length - j) : Set (FreeAmalgam R)) := by
  have he : color R (p.walk.getVert (j - 4)) = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hA : VBall R a (p.walk.length - j) ≤ Q R (p.walk.getVert (j - 4)) := by
    apply Iteration.ball_le_Q_of_dist_add_lt p.start_color
    rw [p.dist_start (by omega), ← p.length_eq_b]
    omega
  exact (backward_edge_le_preceding_natural common p hp heven hj hlen hfixed).trans
    ((U_le_Z R _).trans ((commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes _ he)).trans (centralizer_le hA)))

/-- Two regular turns and radius escape identify the actual failed-span
plane with the backward edge. Image-size assumptions are unnecessary. -/
theorem switching_at_regular_turns
    (common : CommonFacts R source geometry)
    {a a'} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    {j : ℕ} (heven : Even j) (hj : 4 ≤ j) (hlen : j + 2 ≤ p.walk.length)
    (hforward : failedSpanCommutator p g =
      edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j + 1)))
    (hfixed : failedSpanCommutator p g ≤ fixedCore R (p.walk.getVert (j + 2)))
    (hcard : Nat.card (failedSpanCommutator p g) = 4) :
    failedSpanCommutator p g =
      edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j - 1)) := by
  have hc := (p.vertex_color (by omega : j ≤ p.walk.length)).mpr heven
  have ht : Adjacent R (p.walk.getVert j) (p.walk.getVert (j + 1)) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by omega))
  have hs : Adjacent R (p.walk.getVert j) (p.walk.getVert (j - 1)) := by
    have hh := p.walk.adj_getVert_succ (i := j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at hh
    exact adjacent_symm R ((cosetGraph_adj R _ _).mp hh)
  have hKU : failedSpanCommutator p g ≤ U R (p.walk.getVert j) := by
    rw [hforward]
    exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) _ _ hc ht
  have hEU := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (moduleFacts common) _ _ hc hs
  obtain ⟨u, _, hu⟩ := exists_edge_conjugator ht hs
  have hEcard : Nat.card (edgeCommutator R (p.walk.getVert j) (p.walk.getVert (j - 1))) = 4 := by
    rw [← hu, Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective, ← hforward]
    exact hcard
  obtain ⟨hcomm, hescape, hA⟩ := Iteration.switching_ball_facts common p hg heven hj (by omega)
  exact Iteration.EdgeSwitching.planes_eq_of_fixed common hc hKU hEU hcard hEcard
    (hA.trans (fun _ hx => hx.2 _ (adjacent_symm R hs))) hescape
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
    (backward_edge_centralizes_ball common p hp heven hj hlen (hforward ▸ hfixed))


/-- The literal predecessor-image-four contract, with no extra source premise.
The terminal seed supplies the order-four plane used by the geometric proof. -/
theorem failedSpanLargeImageSwitching_four
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    FailedSpanLargeImageSwitching R geometry 4 := by
  intro a a' p hp t ht hne g hg hge hfail n hn hlen hforward hfixed _htwo _hedge _hfour _hnorm _hlast
  have heven : Even (p.walk.length - 4 * n) := by
    have hh : Even p.walk.length := by
      rw [p.length_eq_b]
      exact geometry.even (alpha R) rfl
    rw [Nat.even_iff] at hh ⊢
    omega
  exact switching_at_regular_turns common p hp hg heven (by omega) (by omega) hforward hfixed
    (Iteration.EdgeSwitching.seed_card_four common p
      (RegularSource.terminal_seed common hb p hp ht hne hg hge hfail))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.FourImageSource
