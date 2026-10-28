module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.LocalBounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo.Noncontainment

/-!
# The single-seed bounds in MS93 (4.4.2)

For the contained branch, the commutator of the forward span with the critical
endpoint is larger than the critical line: otherwise the preceding local
nonnormality result fails. Both commutators lie in the terminal edge subgroup,
whose order is at most four. Thus the forward commutator fills that edge,
which bounds the displacement of every seed contained in the terminal kernel.
The hypothesis on containment remains on the full P-orbit span.

For the edge branch, the forward containment makes the terminal Z-layer
centralize the forward span. The local centralizer identity therefore puts
this actor in both kernels of each conjugated two-step pair. Source (4.4.1)(i),
including its fixed initial case, puts the reverse-span displacement in the
fixed core. Intersecting the edge subgroup with that core gives a subgroup
normalized by the entire local stabilizer: its residual centralizes the core,
and its kernel normalizes the edge. Conjugating the individual generators
back then bounds the whole local span's displacement by the prescribed edge.

The two constructors below feed LocalBounds.local_bounds_of_seed. Reverse
escape is retained by the parent for the subsequent orbit and joint-normality
arguments. All conjugations use the actual inverse-conjugation convention.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1)--(4.4.2), printed pp.890 and 893, first subgroup argument.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.LocalBounds.Seed
open NormalizerTransfer

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


variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {a a' : Vertex R}

/-- The full contained orbit span has its endpoint commutator in the forward
span. This inhabits the exact single-seed contract used by LocalBounds. -/
theorem containedSeedBound (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (p : CriticalPath R geometry a a')
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2))) : ContainedSeedBound p := by
  let c := p.walk.getVert 2
  let e := p.walk.getVert (p.walk.length - 2)
  let t := p.walk.getVert (p.walk.length - 1)
  let V₀ := localZSpan R c a
  let K := ⁅V₀, Z R a'⁆
  let E := edgeCommutator R a' t
  have hl := p.length_eq_b
  have hca : (cosetGraph R).dist c a = 2 := by
    rw [SimpleGraph.dist_comm]
    exact p.dist_start (by omega)
  have het : Adjacent R e t := by
    have h := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := p.walk.length - 2) (by omega))
    simpa only [show p.walk.length - 2 + 1 = p.walk.length - 1 by omega] using h
  have ha't : Adjacent R a' t := by
    have h := adjacent_symm R ((cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := p.walk.length - 1) (by omega)))
    simpa only [show p.walk.length - 1 + 1 = p.walk.length by omega,
      SimpleGraph.Walk.getVert_length] using h
  have ht : color R t = true := by
    have hn := adjacent_color_ne R ha't
    rw [p.end_color] at hn
    cases hcol : color R t <;> simp_all
  have hQeQt : Q R e ≤ Q R t := Q_le_adjacent_h R ht het
  have hKE : K ≤ E := by
    change ⁅V₀, Z R a'⁆ ≤ ⁅Z R a', Q R t⁆
    rw [commutator_comm V₀]
    exact commutator_mono le_rfl (hforward.trans hQeQt)
  have hEU : E ≤ U R a' := Escape.Initial.edge_le_natural source _ _ p.end_color ha't
  let : Finite (U R a') := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at a' p.end_color]; decide)
  let : Finite E := Finite.of_injective (inclusion hEU) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKE) (inclusion_injective _)
  have hKnot : ¬ K ≤ Z R a := by
    apply CommutatorContradiction.localSpan_commutator_not_le_center common p.start_color
      p.critical hca
    dsimp [c]
    rw [p.dist_end, p.critical.1, geometry.distance_constant a p.start_color]
    change p.walk.length - 2 + 2 = geometry.b R
    omega
  have hRK : ⁅Z R a, Z R a'⁆ ≤ K :=
    commutator_mono (LocalCommutator.center_Z_le_span p.start_color hca) le_rfl
  have hRZa : ⁅Z R a, Z R a'⁆ ≤ Z R a :=
    (critical_le_natural_centralizer common p).trans
      (inf_le_left.trans (MS93.U_le_Z a))
  let : Finite (⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hRK) (inclusion_injective _)
  have hRcard : 2 ≤ Nat.card (⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) :=
    (one_lt_card_iff_ne_bot _).mpr
      (common.critical_noncommutation a p.start_color a' p.critical)
  have hlarge : 2 < Nat.card K := by
    by_contra! h
    have heq : ⁅Z R a, Z R a'⁆ = K :=
      eq_of_le_of_card_ge hRK (h.trans hRcard)
    exact hKnot (heq ▸ hRZa)
  have hdvd := card_dvd_of_le (hKE.trans hEU)
  rw [common.natural.card_at a' p.end_color] at hdvd
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hEcard : Nat.card E ≤ 4 :=
    Escape.Initial.edge_card_le_four source common.large_distance (moduleFacts common)
      a' t p.end_color ha't
  have hEK : E = K := (eq_of_le_of_card_ge hKE (by omega)).symm
  have hKV : K ≤ V₀ := le_normalizer_iff_commutator_le_left.mp
    ((source.critical_Z_le_stabilizer geometry a p.start_color a' p.critical).2.trans
      (localZSpan_normalized R c a))
  intro g _hg _hgen hcontained
  have hseedQ : rightConjugate (localZSpan R a c) g ≤ Q R e :=
    (map_mono (reverseSpan_le_reversePSpan p)).trans hcontained
  exact (show ⁅rightConjugate (localZSpan R a c) g, Z R a'⁆ ≤ E by
    rw [commutator_comm]
    exact commutator_mono le_rfl (hseedQ.trans hQeQt)).trans (hEK.le.trans hKV)


omit [Finite M] in
private theorem span_intersection_le_fixed (hb : 2 < geometry.b R)
    (hlocal : LocalCommutatorControl R) {a c : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) :
    ⁅localZSpan R a c, Q R a ⊓ Q R c⁆ ≤ fixedCore R c := by
  by_cases h : ⁅Z R a, Q R c⁆ ≤ fixedCore R c
  · exact (commutator_mono le_rfl inf_le_right).trans
      ((LocalCommutator.span_commutator_le_fixed_iff hc hd.le hb).mpr h)
  · exact (hlocal a c ha hc hd h).1

private theorem span_commutator_le_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (hlocal : LocalCommutatorControl R)
    {a c t : Vertex R} (ha : color R a = false) (hc : color R c = false)
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
    (commutator_mono le_rfl hA).trans (span_intersection_le_fixed hb hlocal ha hc hd)
  rw [LocalCommutator.span_eq_conjugates] at hfixed ⊢
  exact fixed_span_commutator_le (Z R a) (stabilizer R c) (Q R c) (Ltilde R c)
    (fixedCore R c) (edgeCommutator R a t) A (source.local_generation c hc)
    (fun _ hx => hx.1) hZQ (Q_normalized R c) (fixedCore_normalized R c)
    inf_le_right hQE (commutator_mono le_rfl hQcQt) (hA.trans inf_le_right) hfixed

/-- Source (4.4.1)(i) localizes the reverse seed displacement to the actual
conjugated edge commutator. The fixed initial case is included. -/
theorem edgeSeedBound (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (hlocal : LocalCommutatorControl R)
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
  have hbound := span_commutator_le_edge source common.large_distance hlocal
    p.start_color hcg hacg hatg hctg (le_inf hZeQa hZeQcg)
  have hE : edgeCommutator R a (act R g t) = rightConjugate (edgeCommutator R a t) g := by
    simpa only [hga, rightConjugate] using edgeCommutator_act g a t
  exact (commutator_mono (conjugate_reverseSpan_le p hg) le_rfl).trans (hbound.trans hE.le)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.LocalBounds.Seed
