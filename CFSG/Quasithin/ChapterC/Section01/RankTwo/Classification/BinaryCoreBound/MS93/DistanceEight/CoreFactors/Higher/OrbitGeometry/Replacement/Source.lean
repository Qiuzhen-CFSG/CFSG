module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Unequal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.PathExtension
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.SourceApplications
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.CriticalOrbit
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Equal

/-!
# The source orbit-containment contradiction on the original path

Write a=p[4], c=p[6], d=p[8]. The replacement vertex r lies on the
critical window c,a,c^g,d^g,r. When the beta edge layers differ, all three
interior turns are separated. Extending this very window supplies the
literal first quotient-centralizer calculation. Together with the preceding
critical pair (d,d^g), source generation forces N_(G_c)(Q_(p[7])) and Z_r
to generate G_c. The previously proved actor bound places Z_r inside that
proper relative normalizer, a contradiction. Equal beta layers instead
identify Z_c with Z_(c^g), contradicting the replacement's criticality.

The final theorem proves (4.5.4)(ii) for the supplied source path from
CommonFacts and genuine Earlier alone. The original conjugator, replacement
endpoint and all four interior even vertices are preserved.

Source: Meierfrankenfeld--Stellmacher (1993), pp.896--899,
especially (4.5.1)(iii), (4.5.2)(i--ii), and (4.5.4)(ii).
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Source
open PathCentrality PathCentrality.RegularPaths Early.Orbit.Source
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The actual replacement window, including every required separation. -/
theorem backward_window (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    (g : stabilizer R a)
    (hd : (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8)
    (hn : ¬ Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 8))
    (w : Witness p g)
    (hne : Z R (p.walk.getVert 5) ≠ Z R (act R g (p.walk.getVert 5))) :
    ∃ v : CriticalPath R geometry (p.walk.getVert 6) w.endpoint,
      HasTurnConjugators R v ∧
      (∀ i, Even i → 2 ≤ i → i + 2 ≤ v.walk.length →
        Z R (v.walk.getVert (i-1)) ≠ Z R (v.walk.getVert (i+1))) ∧
      v.walk.getVert 2 = a ∧ v.walk.getVert 4 = act R g (p.walk.getVert 6) ∧
      v.walk.getVert 6 = act R g (p.walk.getVert 8) ∧
      v.walk.getVert 3 = act R g (p.walk.getVert 5) := by
  have adj (i : ℕ) (hi : i < 14) :
      (cosetGraph R).Adj (p.walk.getVert i) (p.walk.getVert (i+1)) :=
    p.walk.adj_getVert_succ (by rw [p.length_eq]; exact hi)
  have adjg (x y : Vertex R) (hxy : (cosetGraph R).Adj x y) :
      (cosetGraph R).Adj (act R g x) (act R g y) :=
    (cosetGraph_adj R _ _).mpr ((adjacent_act_iff R g _ _).mpr
      ((cosetGraph_adj R _ _).mp hxy))
  have ha5 : (cosetGraph R).Adj a (p.walk.getVert 5) := by
    simpa only [p.center_eq] using adj 4 (by decide)
  have hag5 : (cosetGraph R).Adj a (act R g (p.walk.getVert 5)) := by
    simpa only [show act R g a = a from g.property] using adjg _ _ ha5
  let u : (cosetGraph R).Walk (p.walk.getVert 6) w.endpoint :=
    .cons (adj 5 (by decide)).symm (.cons ha5.symm (.cons hag5
      (.cons (adjg _ _ (adj 5 (by decide))) (.cons (adjg _ _ (adj 6 (by decide)))
      (.cons (adjg _ _ (adj 7 (by decide)))
      (.cons ((cosetGraph_adj R _ _).mpr w.first_adjacent)
      (.cons ((cosetGraph_adj R _ _).mpr w.second_adjacent).symm .nil)))))))
  have hu : u.length = 8 := rfl
  have hc : color R (p.walk.getVert 6) = false :=
    (walk_vertex_color p.start_color p.walk (by rw [p.length_eq]; decide)).mpr (by decide)
  have hrc : CriticalPair R w.endpoint (p.walk.getVert 6)
      (geometry.exists_critical _ w.endpoint_color) :=
    ⟨w.critical_distance.trans (earlier.distance.symm.trans
      (geometry.distance_constant _ w.endpoint_color).symm), w.critical_noncontainment⟩
  let v : CriticalPath R geometry (p.walk.getVert 6) w.endpoint := {
    start_color := hc
    walk := u
    shortest := by rw [hu, SimpleGraph.dist_comm]; exact w.critical_distance.symm
    critical := common.critical_reverse _ w.endpoint_color _ hc hrc }
  refine ⟨v, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro i hi hi2 hiend
    change i + 2 ≤ 8 at hiend
    have hic : i = 2 ∨ i = 4 ∨ i = 6 := by rw [Nat.even_iff] at hi; omega
    rcases hic with rfl | rfl | rfl
    · refine ⟨(g : FreeAmalgam R)⁻¹, (stabilizer R a).inv_mem g.property, ?_⟩
      change act R (g : FreeAmalgam R)⁻¹ (act R g (p.walk.getVert 6)) = p.walk.getVert 6
      rw [← act_mul, mul_inv_cancel, act_one]
    · obtain ⟨k,hk,ht⟩ := p.turns 6 (by decide) (by decide) (by decide)
      have hfix : act R k (p.walk.getVert 6) = p.walk.getVert 6 := hk
      refine ⟨(g : FreeAmalgam R)⁻¹ * k * g, ?_, ?_⟩
      · change act R ((g : FreeAmalgam R)⁻¹ * k * g) (act R g (p.walk.getVert 6)) =
          act R g (p.walk.getVert 6)
        rw [act_mul, act_mul, ← act_mul R (g : FreeAmalgam R), mul_inv_cancel, act_one, hfix]
      · change act R ((g : FreeAmalgam R)⁻¹ * k * g) (act R g (p.walk.getVert 8)) = a
        rw [act_mul, act_mul, ← act_mul R (g : FreeAmalgam R), mul_inv_cancel, act_one, ht,
          p.center_eq]
        exact g.property
    · refine ⟨w.conjugator⁻¹, (stabilizer R _).inv_mem w.conjugator_local, ?_⟩
      change act R w.conjugator⁻¹ (act R w.conjugator (act R g (p.walk.getVert 6))) =
        act R g (p.walk.getVert 6)
      rw [← act_mul, mul_inv_cancel, act_one]
  · intro i hi hi2 hiend
    change i + 2 ≤ 8 at hiend
    have hic : i = 2 ∨ i = 4 ∨ i = 6 := by rw [Nat.even_iff] at hi; omega
    rcases hic with rfl | rfl | rfl
    · exact hne
    · change Z R (act R g (p.walk.getVert 5)) ≠ Z R (act R g (p.walk.getVert 7))
      intro he
      have hm := congrArg (fun N : Subgroup (FreeAmalgam R) =>
        N.map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom) he
      have hmap (x : Vertex R) : (Z R (act R g x)).map
          (MulAut.conj (g : FreeAmalgam R)).toMonoidHom = Z R x := by
        have h := Z_act R (g : FreeAmalgam R)⁻¹ (act R g x)
        simpa only [inv_inv, ← act_mul, mul_inv_cancel, act_one] using h.symm
      rw [hmap, hmap] at hm
      exact p.distinct_Z 6 (by decide) (by decide) (by decide) hm
    · exact (Unequal.neighbor_Z_ne common earlier p g hd hn w).symm

/-- The first source calculations on the original replacement vertices. -/
theorem backward_first_facts (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    (g : stabilizer R a)
    (hd : (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8)
    (hn : ¬ Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 8))
    (w : Witness p g)
    (hne : Z R (p.walk.getVert 5) ≠ Z R (act R g (p.walk.getVert 5))) :
    Early.FirstFacts R geometry (p.walk.getVert 6) a (act R g (p.walk.getVert 6))
      (act R g (p.walk.getVert 8)) w.endpoint (act R g (p.walk.getVert 5)) := by
  obtain ⟨v,hv,hs,ha,hc,hdg,ht⟩ := backward_window common earlier p g hd hn w hne
  obtain ⟨b,⟨q,hq⟩⟩ := Early.PathExtension.sourcePath_preserving_window common earlier v hv hs
  have h0 : q.walk.getVert 2 = p.walk.getVert 6 :=
    (hq 0 (by decide)).trans v.walk.getVert_zero
  have h2 : q.walk.getVert 4 = a := (hq 2 (by decide)).trans ha
  have h4 : q.walk.getVert 6 = act R g (p.walk.getVert 6) := (hq 4 (by decide)).trans hc
  have h6 : q.walk.getVert 8 = act R g (p.walk.getVert 8) := (hq 6 (by decide)).trans hdg
  have h8 : q.walk.getVert 10 = w.endpoint := by
    have hl : v.walk.length = 8 := v.length_eq_b.trans earlier.distance
    exact (hq 8 (by decide)).trans (by rw [← hl, SimpleGraph.Walk.getVert_length])
  have h3 : q.walk.getVert 5 = act R g (p.walk.getVert 5) := (hq 3 (by decide)).trans ht
  simpa only [Nat.reduceAdd,h0,h2,h4,h6,h8,h3] using
    (Early.firstFactsOnPath source common earlier q).forward 2 (by decide) (by decide) (by decide)

/-- The unequal-beta branch contradicts the source local generation. -/
theorem unequal_contradiction (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Early.SourcePath R a)
    (g : stabilizer R a)
    (hd : (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8)
    (hn : ¬ Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 8))
    (w : Witness (Early.Orbit.SourceApplications.higherPath geometry p) g)
    (hne : Z R (p.walk.getVert 5) ≠ Z R (act R g (p.walk.getVert 5))) : False := by
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  let c := p.walk.getVert 6
  let d := p.walk.getVert 8
  let t := p.walk.getVert 7
  have hc : color R c = false := p.even_color (i := 6) (by decide) (by decide)
  have hdc : color R d = false := p.even_color (i := 8) (by decide) (by decide)
  have hct : Adjacent R c t := p.adjacent (i := 6) (by decide)
  have hdt : Adjacent R d t := adjacent_symm R (p.adjacent (i := 7) (by decide))
  have hcomm : ⁅V R a, V R d⁆ = H R a ⊓ H R d := by
    simpa only [Nat.reduceAdd,p.center_eq] using
      ((Early.firstFactsOnPath source common earlier p).forward 4
        (by decide) (by decide) (by decide)).commutator_eq
  have hr : Z R w.endpoint ≤ relativeNormalizer R c t :=
    Unequal.endpoint_le_relativeNormalizer common earlier q w hcomm
  have hm := (p.moving_neighbors source common earlier (i := 6)
    (by decide) (by decide) (by decide)).2
  let v := orbitCriticalPath q earlier g hd hn
  have hdist : (cosetGraph R).dist (act R g d) c = 6 :=
    v.dist_start (i := 6) (by change 6 ≤ 8; decide)
  have hcQ : Z R c ≤ Q R (act R g d) := by
    apply Z_le_Q_of_dist_lt R c (geometry.exists_critical c hc)
    rw [SimpleGraph.dist_comm,hdist,geometry.distance_constant _ hc]
    change 6 < geometry.b R
    rw [earlier.distance]
    decide
  have hdV : Z R d ≤ V R c := le_iSup_of_le d (le_iSup_of_le
    q.two_step_distances.2.1.le le_rfl)
  have hnrev : ¬ Z R d ≤ Q R (act R g d) :=
    (common.critical_reverse _ v.start_color _ hdc v.critical).2
  have hgen := generation_of_first_window common earlier hc hdc hct hdt hm hcQ hdV
    (hr.trans inf_le_left) hnrev (backward_first_facts common earlier q g hd hn w hne)
  have heq : relativeNormalizer R c t = stabilizer R c := by
    simpa only [sup_eq_left.mpr hr] using hgen
  apply (relativeNormalizer_isCoatom common earlier hc hct).1
  rw [heq]
  exact subgroupOf_self _

/-- MS93 (4.5.4)(ii) on the original source path, with both cases discharged. -/
theorem source_orbit_le_Q (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Early.SourcePath R a) :
    NormalizerTransfer.conjugatesIn (Z R (p.walk.getVert 8)) (stabilizer R a) ≤
      Q R (p.walk.getVert 8) := by
  by_contra hnot
  have hc : color R (p.walk.getVert 8) = false := p.even_color (i := 8) (by decide) (by decide)
  have hdist : (cosetGraph R).dist (p.walk.getVert 8) a ≤ 4 := by
    rw [SimpleGraph.dist_comm]
    simpa only [p.center_eq] using (p.distance (geometry := geometry)
      (i := 4) (j := 8) (by decide) (by decide)).le
  obtain ⟨g,hcrit⟩ := exists_critical_of_orbit_not_le_Q earlier hc hdist hnot
  have hd : (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8 :=
    hcrit.1.trans ((geometry.distance_constant _
      ((action_preserves_color R g _).trans hc)).trans earlier.distance)
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  obtain ⟨w⟩ := exists_witness common q earlier g hd hcrit.2
  by_cases he : Z R (p.walk.getVert 5) = Z R (act R g (p.walk.getVert 5))
  · apply w.opposite_not_le_seed_join common earlier
    exact (Equal.seed_Z_eq_of_edge_Z_eq common earlier p g he).le.trans le_sup_right
  · exact unequal_contradiction common earlier p g hd hcrit.2 w he

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Source
