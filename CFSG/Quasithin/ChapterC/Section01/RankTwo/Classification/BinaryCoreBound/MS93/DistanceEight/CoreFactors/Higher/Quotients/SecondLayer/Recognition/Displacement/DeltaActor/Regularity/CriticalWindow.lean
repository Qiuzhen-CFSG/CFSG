module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.DeltaActor.Nondegeneracy
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.DeltaActor.Regularity.SeedExtension
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Layer.WindowSelection

/-!
# A critical window through the actual delta

Write a=p[4], t=p[5], c=p[6], d=p[8]. The literal (4.5.1)(iv)
product puts hat W_a outside Q_d. The given three-seed generation equation
writes hat W_a as the join of the d and delta orbit factors. The preceding
(4.5.4)(ii) at d puts the first factor in Q_d, so some G_a-conjugate of
Z_delta escapes Q_d. Inverse conjugation selects h in G_a such that
(delta,d^h) is critical. This uses delta's given generation, without
replacing delta or assuming its actor product.

The walk delta,t^g,c,t,a,t^h,c^h,p[7]^h,d^h, where g is delta's given
transporter, has eight edges. Critical-distance minimality makes it shortest.
Its three turns are g, h inverse, and the transported original turn at c.
Thus the proved earlier `window_hatW_product` applies directly and supplies
the exact product hat W(delta,c,a) Q_a = Q_t. The last theorem feeds it to
the parent's original delta displacement consumer.

This is a weaker geometric witness than the requested fourteen-edge
SourcePath. Its middle Z-separation Z_t != Z_(t^h) is not proved; regularity
in `HasTurnConjugators` does not include that condition. The existing product
proof requires only this regular critical window, so no such inequality is
assumed in these results. The earlier complete path constructors remain
available separately.

The additional orbit-containment premise is precisely (4.5.4)(ii) on the
original supplied SourcePath, with endpoint d. Its existing producer is
qt-c01-ms93-higher-orbit-geometry, via qt-c01-ms93-higher-critical-replacement.
That source obligation remains undischarged here; this is not an unconditional
proof of (4.5.4)(iii). The final consumer also retains the delta orbit bound
and original commutator (4.5.3)(iii) already required by its parent.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.5.1)(iv), p.896, and (4.5.4)(ii)--(iii), pp.898--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.Regularity
open PathCentrality PathCentrality.RegularPaths NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The literal (4.5.1)(iv) product under the supplied Higher.SourcePath
conditions, obtained from its actual critical window at indices four to twelve. -/
theorem sourcePath_hatW_product
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : Higher.SourcePath a) :
    (hatW R a (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)) := by
  obtain ⟨e, w, hw, _, hc, hd, ht⟩ :=
    (sourcePath_iff_regular_critical_seed common earlier a
      (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 7)).mp ⟨p, rfl, rfl, rfl⟩
  simpa only [hc, hd, ht] using Early.First.Layer.window_hatW_product common earlier w hw

/-- Generation and the original endpoint's preceding orbit containment
select an endpoint for a critical pair with the fixed delta. The element
fixes a; neither delta nor the original middle vertices are reselected. -/
theorem delta_exists_critical_endpoint
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hfirst : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8)) :
    ∃ h ∈ stabilizer R (alpha R),
      ¬ Z R δ.vertex ≤ Q R (act R h (p.walk.getVert 8)) := by
  have hA := first_factor_le_Q earlier p hfirst
  have hnot : ¬ localZSpan R δ.vertex (alpha R) ≤ Q R (p.walk.getVert 8) := by
    rw [LocalCommutator.span_eq_conjugates]
    intro h
    apply second_not_le_Q earlier p (sourcePath_hatW_product common earlier p)
    rw [← δ.factors_generate]
    exact sup_le hA (sup_le h ((show hatV R (alpha R) (p.walk.getVert 6) ≤
      orbitFactor p (p.walk.getVert 8) from le_sup_right).trans hA))
  obtain ⟨g, hg, hn⟩ := exists_conjugate_not_le hnot
  refine ⟨g⁻¹, (stabilizer R _).inv_mem hg, ?_⟩
  intro h
  have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
  rw [← Z_act, ← Q_act, ← act_mul, inv_mul_cancel, act_one] at hm
  exact hn hm

/-- A regular critical eight-window through the actual delta,c,a segment.
The sole extra source premise is the original instance of (4.5.4)(ii).
No separation of the two Z-layers incident with a is claimed. -/
theorem delta_regular_critical_window
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hfirst : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8)) :
    ∃ e, ∃ w : CriticalPath R geometry δ.vertex e,
      HasTurnConjugators R w ∧ w.walk.getVert 2 = p.walk.getVert 6 ∧
      w.walk.getVert 4 = alpha R ∧ w.walk.getVert 3 = p.walk.getVert 5 := by
  obtain ⟨h, hh, hn⟩ := delta_exists_critical_endpoint common earlier δ hfirst
  have ha : act R h (alpha R) = alpha R := hh
  have hat : (cosetGraph R).Adj (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using p.walk.adj_getVert_succ (i := 4)
      (by rw [p.length_eq]; decide)
  have htc : (cosetGraph R).Adj (p.walk.getVert 5) (p.walk.getVert 6) :=
    p.walk.adj_getVert_succ (i := 5) (by rw [p.length_eq]; decide)
  have hcs : (cosetGraph R).Adj (p.walk.getVert 6) (p.walk.getVert 7) :=
    p.walk.adj_getVert_succ (i := 6) (by rw [p.length_eq]; decide)
  have hsd : (cosetGraph R).Adj (p.walk.getVert 7) (p.walk.getVert 8) :=
    p.walk.adj_getVert_succ (i := 7) (by rw [p.length_eq]; decide)
  have adj (k : FreeAmalgam R) {u v : Vertex R} (huv : (cosetGraph R).Adj u v) :
      (cosetGraph R).Adj (act R k u) (act R k v) :=
    (cosetGraph_adj R _ _).mpr ((adjacent_act_iff R k _ _).mpr
      ((cosetGraph_adj R _ _).mp huv))
  have hδt : (cosetGraph R).Adj δ.vertex (act R δ.transporter (p.walk.getVert 5)) := by
    rw [δ.vertex_eq]
    exact adj δ.transporter hat
  have hδc : (cosetGraph R).Adj (act R δ.transporter (p.walk.getVert 5)) (p.walk.getVert 6) := by
    have he := adj δ.transporter htc
    rwa [show act R δ.transporter (p.walk.getVert 6) = p.walk.getVert 6 from
      δ.transporter.property] at he
  have hah : (cosetGraph R).Adj (alpha R) (act R h (p.walk.getVert 5)) := by
    simpa only [ha] using adj h hat
  let v := SimpleGraph.Walk.cons hδt (.cons hδc (.cons htc.symm (.cons hat.symm
    (.cons hah (.cons (adj h htc) (.cons (adj h hcs) (.cons (adj h hsd) .nil)))))))
  have hv : v.length = 8 := rfl
  have hdist : (cosetGraph R).dist δ.vertex (act R h (p.walk.getVert 8)) = 8 := by
    have hmin := criticalDistance_le R δ.vertex (geometry.exists_critical _ (delta_color δ)) hn
    rw [(geometry.distance_constant _ (delta_color δ)).trans earlier.distance] at hmin
    exact le_antisymm ((SimpleGraph.dist_le v).trans_eq hv) hmin
  let w : CriticalPath R geometry δ.vertex (act R h (p.walk.getVert 8)) := {
    start_color := delta_color δ
    walk := v
    shortest := hv.trans hdist.symm
    critical := ⟨hdist.trans (earlier.distance.symm.trans
      (geometry.distance_constant _ (delta_color δ)).symm), hn⟩ }
  refine ⟨_, w, ?_, rfl, rfl, rfl⟩
  intro i hi hi2 hiend
  change i + 2 ≤ v.length at hiend
  rw [hv] at hiend
  have hic : i = 2 ∨ i = 4 ∨ i = 6 := by rw [Nat.even_iff] at hi; omega
  rcases hic with rfl | rfl | rfl
  · exact ⟨δ.transporter, δ.transporter.property, δ.vertex_eq.symm⟩
  · refine ⟨h⁻¹, (stabilizer R _).inv_mem hh, ?_⟩
    change act R h⁻¹ (act R h (p.walk.getVert 6)) = p.walk.getVert 6
    rw [← act_mul, mul_inv_cancel, act_one]
  · obtain ⟨k, hk, hturn⟩ := p.turns 6 (by decide) (by decide) (by decide)
    refine ⟨h⁻¹ * k * h, ?_, ?_⟩
    · change h⁻¹ * k * h ∈ stabilizer R (act R h (p.walk.getVert 6))
      rw [stabilizer_act]
      simpa only [MulAut.conj_apply, inv_inv, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe] using mem_map_of_mem (MulAut.conj h⁻¹).toMonoidHom hk
    · change act R (h⁻¹ * k * h) (act R h (p.walk.getVert 8)) = alpha R
      rw [← act_mul]
      simp only [← mul_assoc, mul_inv_cancel, one_mul, act_mul, hturn, p.center_eq, ha]

/-- The weaker eight-window is enough for the literal earlier product.
The first orbit bound is (4.5.4)(ii) at d, not the desired delta actor product. -/
theorem delta_product_of_first_orbit
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hfirst : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8)) :
    (hatW R δ.vertex (p.walk.getVert 6) (alpha R) : Set (FreeAmalgam R)) *
      (Q R (alpha R) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)) := by
  obtain ⟨e, w, hw, hc, ha, ht⟩ := delta_regular_critical_window common earlier δ hfirst
  simpa only [hc, ha, ht] using Early.First.Layer.window_hatW_product common earlier w hw

/-- Apply the constructed window and proved product to the original delta
orbit module. Only the two preceding orbit containments and the original
(4.5.3)(iii) commutator remain explicit; no path or actor-product witness does. -/
theorem delta_small_and_separated_of_first_orbit
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (s : OrbitModule source p δ.vertex)
    (hfirst : conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R (alpha R)) ≤
      Q R (p.walk.getVert 8))
    (horbit : conjugatesIn (Z R δ.vertex) (stabilizer R (alpha R)) ≤ Q R δ.vertex)
    (hcomm : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (alpha R)⁆ ≤ Z R (alpha R)) : letI := s.normal
    Escape.Initial.Natural.Splitting.HasSmallInvolution s.action ∧
      DisplacementSeparation s.action common.natural.marking := by
  exact delta_small_and_separated_of_candidate_product source common earlier δ s
    (delta_product_of_first_orbit common earlier δ hfirst) horbit hcomm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement.Regularity
