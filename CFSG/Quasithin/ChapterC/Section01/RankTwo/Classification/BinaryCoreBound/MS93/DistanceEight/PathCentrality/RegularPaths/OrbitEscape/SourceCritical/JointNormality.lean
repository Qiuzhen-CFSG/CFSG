module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.SourceCritical.Controls
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.Source

/-!
# Joint normality using only source critical-prefix control

The terminal critical exclusion uses the reversed critical path, and each
edge seed uses the actual conjugate path under an element fixing the start.
Both local-control calls therefore follow from the earlier nonnatural
exclusion restricted to critical prefixes. The contained seed, separating
edge conjugates and relative-normality assembly retain their proved inputs.

Source: MS93 (4.4.2), printed p.893, first subgroup argument.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.SourceCritical
open NormalizerTransfer LocalCommutator
open LocalBounds
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a a' : Vertex R}
/-- The final application of (4.4.1) excludes the printed containment
R ≤ U_(a′−2), using the full radius subgroup in (4.3). -/
theorem critical_not_le_terminal_natural [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry) (p : CriticalPath R geometry a a') :
    ¬ ⁅Z R a, Z R a'⁆ ≤ U R (p.walk.getVert (p.walk.length - 2)) := by
  let e := p.walk.getVert (p.walk.length - 2)
  have hl := p.length_eq_b
  have heven : Even p.walk.length := by
    rw [p.shortest, p.critical.1]
    exact geometry.even a p.start_color
  have he : color R e = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hea' : (cosetGraph R).dist e a' = 2 := by
    dsimp [e]
    rw [p.dist_end]
    omega
  have hae : (cosetGraph R).dist a e = geometry.b R - 2 := by
    dsimp [e]
    rw [p.dist_start (by omega), hl]
  have hZaQe : Z R a ≤ Q R e := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a p.start_color)
    rw [geometry.distance_constant a p.start_color, hae]
    change geometry.b R - 2 < geometry.b R
    omega
  have hVaGe : V R a ≤ stabilizer R e := by
    apply (V_le_iff R p.start_color _).mpr
    intro d hd hda
    apply Z_le_stabilizer_of_dist_le d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    change (cosetGraph R).dist d e ≤ geometry.b R
    have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := e)
    rw [hae] at ht
    omega
  have hVeGa : V R e ≤ stabilizer R a := by
    apply (V_le_iff R he _).mpr
    intro d hd hde
    apply Z_le_stabilizer_of_dist_le d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    change (cosetGraph R).dist d a ≤ geometry.b R
    have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := e) (w := a)
    rw [SimpleGraph.dist_comm (u := e), hae] at ht
    omega
  intro hR
  have hnotD : ¬ ⁅Z R a', Z R a⁆ ≤ fixedCore R e := by
    intro hD
    apply common.critical_noncommutation a p.start_color a' p.critical
    apply le_bot_iff.mp
    rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) e he]
    exact le_inf hR ((commutator_comm (Z R a) (Z R a') ▸ hD).trans inf_le_right)
  have hinit : ¬ ⁅Z R a', Q R e⁆ ≤ fixedCore R e :=
    fun h => hnotD ((commutator_mono le_rfl hZaQe).trans h)
  have hex : ∃ x ∈ Z R a, ¬ ⁅localZSpan R a' e, zpowers x⁆ ≤ fixedCore R e := by
    by_contra! h
    apply hnotD
    apply commutator_le.mpr
    intro z hz x hx
    exact h x hx (commutator_mem_commutator (Z_le_localZSpan R a' e hz) (mem_zpowers x))
  obtain ⟨x, hx, hmove⟩ := hex
  have hcover := (OrbitEscape.SourceCritical.reverse_prefix_control common hb exclude p hinit).2
    x (hZaQe hx) hmove
  let W := localZSpan R a' e
  have hWGa : W ≤ stabilizer R a :=
    (localZSpan_le_V R (by rw [SimpleGraph.dist_comm, hea'])).trans hVeGa
  have hKZa : ⁅zpowers x, W⁆ ≤ Z R a :=
    (commutator_mono (zpowers_le.mpr hx) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hWGa.trans (Z_normalized R a)))
  let := V_abelian_of_four_lt R p.start_color hb
  have hVV : V R a ≤ centralizer (V R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hKzero : ⁅⁅zpowers x, W⁆, V R a⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hKZa.trans ((Z_le_VBall R a 2).trans hVV))
  have hDnorm : Q R e ≤ normalizer (fixedCore R e : Set (FreeAmalgam R)) :=
    (show Q R e ≤ stabilizer R e from fun _ hx => hx.1).trans (fixedCore_normalized R e)
  have hDVa : ⁅fixedCore R e, V R a⁆ ≤ fixedCore R e :=
    le_normalizer_iff_commutator_le_left.mp (hVaGe.trans (fixedCore_normalized R e))
  have hpre : Z R e ≤ commutatorPreimage (Q R e) (V R a) (fixedCore R e) :=
    hcover.trans (sup_le
      (le_commutatorPreimage (hKZa.trans hZaQe) (hKzero.le.trans bot_le))
      (le_commutatorPreimage inf_le_left hDVa))
  have hcommD : ⁅Z R e, V R a⁆ ≤ fixedCore R e :=
    (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hDnorm)
  have hcommU : ⁅Z R e, V R a⁆ ≤ U R e :=
    (commutator_mono le_rfl hVaGe).trans_eq
      (Escape.Initial.Z_commutator_stabilizer source e he)
  have hzero : ⁅Z R e, V R a⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) e he]
    exact le_inf hcommU (hcommD.trans inf_le_right)
  apply common.escape a p.start_color a' p.critical e hea'
    (by rw [hae, p.critical.1, geometry.distance_constant a p.start_color]; change _ + 2 = geometry.b R; omega)
  rw [← common.natural.centralizer e he]
  exact le_inf hVaGe
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
      (centralizer_le (MS93.U_le_Z e)))

private theorem fixed_span_commutator_le {G : Type*} [Group G]
    (S F Q L D E A : Subgroup G)
    (hgen : L ⊔ Q = F) (hQF : Q ≤ F) (hSQ : S ≤ Q)
    (hFQ : F ≤ normalizer Q) (hFD : F ≤ normalizer D)
    (hDL : D ≤ centralizer (L : Set G)) (hQE : Q ≤ normalizer E)
    (hSE : ⁅S, Q⁆ ≤ E) (hAQ : A ≤ Q)
    (hfixed : ⁅conjugatesIn S F, A⁆ ≤ D) :
    ⁅conjugatesIn S F, A⁆ ≤ E := by
  have hFED : F ≤ normalizer (E ⊓ D : Subgroup G) := by
    rw [← hgen]
    exact sup_le
      ((le_centralizer_iff.mpr (inf_le_right.trans hDL)).trans
        (Subgroup.centralizer_le_normalizer _))
      ((le_inf hQE (hQF.trans hFD)).trans inf_normalizer_le_normalizer_inf)
  have hpre : conjugatesIn S F ≤ commutatorPreimage Q A E := by
    apply iSup_le
    intro g
    have hQ : rightConjugate Q g = Q :=
      mem_normalizer_iff_map_conj_eq.mp (hFQ (F.inv_mem g.property))
    have hD : rightConjugate D g = D :=
      mem_normalizer_iff_map_conj_eq.mp (hFD (F.inv_mem g.property))
    have hED : rightConjugate (E ⊓ D) g = E ⊓ D :=
      mem_normalizer_iff_map_conj_eq.mp (hFED (F.inv_mem g.property))
    have hbound : ⁅rightConjugate S g, A⁆ ≤ rightConjugate E g := by
      apply (commutator_mono le_rfl hAQ).trans
      rw [← hQ, rightConjugate, rightConjugate, ← map_commutator]
      exact map_mono hSE
    have hfix : ⁅rightConjugate S g, A⁆ ≤ D :=
      (commutator_mono (le_iSup (fun h : F => rightConjugate S h) g) le_rfl).trans hfixed
    have hcut : rightConjugate E g ⊓ D = E ⊓ D := by
      calc
        rightConjugate E g ⊓ D = rightConjugate E g ⊓ rightConjugate D g := by rw [hD]
        _ = rightConjugate (E ⊓ D) g :=
          (Subgroup.map_inf _ _ _ (MulAut.conj (g : G)⁻¹).injective).symm
        _ = E ⊓ D := hED
    exact le_commutatorPreimage ((map_mono hSQ).trans hQ.le)
      ((le_inf hbound hfix).trans (hcut.le.trans inf_le_left))
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le Q A E hQE)

variable [Finite M]

omit [Finite M] in
private theorem span_intersection_le_fixed (hb : 2 < geometry.b R)
    {a c : Vertex R}
    (hcontrol : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c → LocalControlAt R a c)
    (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) :
    ⁅localZSpan R a c, Q R a ⊓ Q R c⁆ ≤ fixedCore R c := by
  by_cases h : ⁅Z R a, Q R c⁆ ≤ fixedCore R c
  · exact (commutator_mono le_rfl inf_le_right).trans
      ((LocalCommutator.span_commutator_le_fixed_iff hc hd.le hb).mpr h)
  · exact (hcontrol h).1

private theorem span_commutator_le_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R)
    {a c t : Vertex R}
    (hcontrol : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c → LocalControlAt R a c) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    {A : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R a ⊓ Q R c) :
    ⁅localZSpan R a c, A⁆ ≤ edgeCommutator R a t := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    rw [ha] at hn
    cases hcol : color R t <;> simp_all
  have hQcQt : Q R c ≤ Q R t := Q_le_adjacent_h R ht hct
  have hQcGa : Q R c ≤ stabilizer R a :=
    Q_le_stabilizer_of_dist_two R c a hc (by rwa [SimpleGraph.dist_comm])
  have hQE : Q R c ≤ normalizer (edgeCommutator R a t) := by
    intro g hg
    apply (mem_normalizer_iff_map_conj_eq).mpr
    change (⁅Z R a, Q R t⁆).map (MulAut.conj g).toMonoidHom = _
    have hZ : (Z R a).map (MulAut.conj g).toMonoidHom = Z R a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a (hQcGa hg))
    have hQ : (Q R t).map (MulAut.conj g).toMonoidHom = Q R t :=
      mem_normalizer_iff_map_conj_eq.mp ((Q R t).le_normalizer (hQcQt hg))
    rw [map_commutator, hZ, hQ]
    rfl
  have hZQ : Z R a ≤ Q R c :=
    (Z_le_localZSpan R a c).trans (localZSpan_le_Q R hc hd.le hb)
  have hfixed : ⁅localZSpan R a c, A⁆ ≤ fixedCore R c :=
    (commutator_mono le_rfl hA).trans (span_intersection_le_fixed hb hcontrol hc hd)
  rw [LocalCommutator.span_eq_conjugates] at hfixed ⊢
  exact fixed_span_commutator_le (Z R a) (stabilizer R c) (Q R c) (Ltilde R c)
    (fixedCore R c) (edgeCommutator R a t) A (source.local_generation c hc)
    (fun _ hx => hx.1) hZQ (Q_normalized R c) (fixedCore_normalized R c)
    inf_le_right hQE (commutator_mono le_rfl hQcQt) (hA.trans inf_le_right) hfixed

/-- Source (4.4.1)(i) localizes the reverse seed displacement to the actual
conjugated edge commutator. The fixed initial case is included. -/
theorem edgeSeedBound (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (p : CriticalPath R geometry a a')
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2))) : EdgeSeedBound p := by
  intro g hg _hgen
  let c := p.walk.getVert 2
  let e := p.walk.getVert (p.walk.length - 2)
  let t := p.walk.getVert 1
  have hl := p.length_eq_b
  have hc : color R c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hac : (cosetGraph R).dist a c = 2 := p.dist_start (by omega)
  have heven : Even p.walk.length := by
    rw [p.shortest, p.critical.1]
    exact geometry.even a p.start_color
  have he : color R e = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hat : Adjacent R a t := by
    simpa only [SimpleGraph.Walk.getVert_zero, Nat.zero_add] using
      (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hct : Adjacent R c t :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hga : act R g a = a := hg
  have hacg : (cosetGraph R).dist a (act R g c) = 2 := by
    rw [← hga, dist_act, hac]
  have hcg : color R (act R g c) = false := (action_preserves_color R g c).trans hc
  have hatg : Adjacent R a (act R g t) := by
    simpa only [hga] using (adjacent_act_iff R g a t).mpr hat
  have hctg : Adjacent R (act R g c) (act R g t) :=
    (adjacent_act_iff R g c t).mpr hct
  have ht : color R (act R g t) = true := by
    have hn := adjacent_color_ne R hatg
    rw [p.start_color] at hn
    cases hcol : color R (act R g t) <;> simp_all
  have hZeQa : Z R e ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R e (geometry.exists_critical e he)
    rw [geometry.distance_constant e he, SimpleGraph.dist_comm, p.dist_start (by omega)]
    change p.walk.length - 2 < geometry.b R
    omega
  have hZcgV : Z R (act R g c) ≤ localZSpan R c a :=
    le_iSup (fun h : stabilizer R a => Z R (act R h c)) ⟨g, hg⟩
  have hZeC : Z R e ≤ centralizer (Z R (act R g c) : Set (FreeAmalgam R)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes e he)).trans
      (centralizer_le (hZcgV.trans hforward))
  have hZeQcg : Z R e ≤ Q R (act R g c) := by
    rw [← common.centralizer _ _ hcg hctg]
    exact le_inf (hZeQa.trans (Q_le_adjacent_h R ht hatg)) hZeC
  have hbound := span_commutator_le_edge source common.large_distance
    (OrbitEscape.SourceCritical.conjugate_prefix_control common hb exclude p hg)
    p.start_color hcg hacg hatg hctg (le_inf hZeQa hZeQcg)
  have hE : edgeCommutator R a (act R g t) = rightConjugate (edgeCommutator R a t) g := by
    simpa only [hga, rightConjugate] using edgeCommutator_act g a t
  exact (commutator_mono (conjugate_reverseSpan_le p hg) le_rfl).trans (hbound.trans hE.le)


/-- Joint normality from the earlier nonnatural branch only on critical prefixes.
Separating edge conjugates, contained displacement and the two actual local-control
applications are all discharged. -/
theorem jointSpan_normalized_of_failed_escape
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (exclude : OrbitEscape.SourceCritical.CriticalPrefixExclusion R geometry)
    (p : CriticalPath R geometry a a')
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hreverse : ∀ g ∈ stabilizer R a,
      localZSpan R a (act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4))) :
    stabilizer R a ≤ normalizer (jointSpan p) := by
  exact jointSpan_normalized_of_source_steps common p hb hreverse
    (separatingConjugates common p)
    (containedDisplacementBound_of_seed p hb (Seed.containedSeedBound common hb p hforward))
    (edgeDisplacementBound_of_seed source p hb (edgeSeedBound common hb exclude p hforward))
    (critical_not_le_terminal_natural common hb exclude p)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.SourceCritical
