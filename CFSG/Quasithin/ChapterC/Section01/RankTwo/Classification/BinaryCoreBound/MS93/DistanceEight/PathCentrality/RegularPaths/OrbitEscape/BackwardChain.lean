module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.Spans

/-!
# The backward critical chain in MS93 (4.4.2)

Iterate CriticalPath.exists_shift, preserving the whole overlapping subwalk
and the critical pair at every earlier even offset. At (b-2)/2 shifts the
resulting critical path ends at the original a+2 and passes through a.
Neighbor transitivity chooses g in G_a carrying the original β to δ₁.
Distance bounds place V_a and V_(a+2)^g in Q_(δ_(b-4)); when V V₁ is normal
in G_a, this also places V₁ there.

This constructs the geometric input to the R₁/R₂ calculation. It does not
prove joint normality or the orbit-escape disjunction. It uses CommonFacts.escape
as the supplied (4.3) input and assumes no regularity, b > 6 or b = 8.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, second paragraph of the proof.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- After n backward shifts, retain all critical pairs and every original vertex
in the overlap. The endpoint equation avoids casting dependent walks. -/
structure BackwardChain {a a' : Vertex R} (p : CriticalPath R geometry a a') (n : ℕ) where
  first : Vertex R
  last : Vertex R
  path : CriticalPath R geometry first last
  endpoint_eq : last = p.walk.getVert (p.walk.length - 2 * n)
  overlap : ∀ i, i ≤ p.walk.length - 2 * n →
    path.walk.getVert (i + 2 * n) = p.walk.getVert i
  critical : ∀ k, k ≤ n →
    ∃ hk : color R (path.walk.getVert (2 * (n - k))) = false,
      CriticalPair R (path.walk.getVert (2 * (n - k)))
        (p.walk.getVert (p.walk.length - 2 * k)) (geometry.exists_critical _ hk)

/-- Repeated applications of the supplied (4.3) escape theorem construct the
whole backward chain, without any regular-turn hypothesis. -/
theorem exists_backwardChain {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (n : ℕ) (hn : 2 * n ≤ p.walk.length) :
    Nonempty (BackwardChain p n) := by
  induction n with
  | zero =>
    refine ⟨⟨a, a', p, by simp, ?_, ?_⟩⟩
    · intro i hi
      simp
    · intro k hk
      have he : k = 0 := by omega
      subst k
      simpa only [Nat.sub_zero, Nat.mul_zero, SimpleGraph.Walk.getVert_zero,
        SimpleGraph.Walk.getVert_length] using ⟨p.start_color, p.critical⟩
  | succ n ih =>
    obtain ⟨c⟩ := ih (by omega)
    obtain ⟨d, q, s, hq, hs⟩ := c.path.exists_shift common
    have hlen : c.path.walk.length = p.walk.length :=
      c.path.length_eq_b.trans p.length_eq_b.symm
    have ho (i : ℕ) (hi : i ≤ c.path.walk.length - 2) :
        s.walk.getVert (i + 2) = c.path.walk.getVert i := by
      rw [hs, SimpleGraph.Walk.getVert_append, hq, if_neg (by omega),
        Nat.add_sub_cancel, SimpleGraph.Walk.take_getVert, inf_eq_right.mpr hi]
    have he : c.path.walk.getVert (c.path.walk.length - 2) =
        p.walk.getVert (p.walk.length - 2 * (n + 1)) := by
      have hh := c.overlap (p.walk.length - 2 * (n + 1)) (by omega)
      convert hh using 2; omega
    refine ⟨⟨d, _, s, he, ?_, ?_⟩⟩
    · intro i hi
      have hidx : i + 2 * (n + 1) = (i + 2 * n) + 2 := by omega
      rw [hidx, ho _ (by omega), c.overlap i (by omega)]
    · intro k hk
      by_cases hkn : k ≤ n
      · have hidx : 2 * (n + 1 - k) = 2 * (n - k) + 2 := by omega
        rw [hidx, ho _ (by omega)]
        exact c.critical k hkn
      · have hke : k = n + 1 := by omega
        subst k
        simp only [Nat.sub_self, Nat.mul_zero, SimpleGraph.Walk.getVert_zero]
        exact ⟨s.start_color, by simpa only [he] using s.critical⟩

private theorem path_distance {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.walk.length) :
    (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert j) = j - i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk p.shortest (p.walk.isSubwalk_drop i))
    ((p.walk.drop i).isSubwalk_take (j - i))
  have hmin : j - i ≤ p.walk.length - i := Nat.sub_le_sub_right hj i
  simpa only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hmin, SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij] using hh.symm

/-- Even critical distance identifies the number of shifts ending at a+2. -/
theorem terminal_length {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hb : 2 ≤ geometry.b R) : 2 * ((p.walk.length - 2) / 2) = p.walk.length - 2 := by
  have he : Even p.walk.length := by
    rw [p.length_eq_b]
    exact geometry.even (alpha R) rfl
  rw [Nat.even_iff] at he
  have hl := p.length_eq_b
  omega

/-- The original start is still the vertex at offset 2n. -/
theorem BackwardChain.start_vertex {a a' : Vertex R} {p : CriticalPath R geometry a a'}
    {n : ℕ} (c : BackwardChain p n) : c.path.walk.getVert (2 * n) = a := by
  simpa only [Nat.zero_add, SimpleGraph.Walk.getVert_zero] using c.overlap 0 (Nat.zero_le _)

/-- The printed choice is β^g = δ₁, with g in G_a. -/
theorem BackwardChain.exists_neighbor_conjugator [Finite M]
    {a a' : Vertex R} {p : CriticalPath R geometry a a'} (hb : 4 < geometry.b R)
    (c : BackwardChain p ((p.walk.length - 2) / 2)) :
    ∃ g ∈ stabilizer R a, act R g (p.walk.getVert 1) =
      c.path.walk.getVert (p.walk.length - 3) := by
  have hl : c.path.walk.length = p.walk.length :=
    c.path.length_eq_b.trans p.length_eq_b.symm
  have hp := p.length_eq_b
  have hc := c.start_vertex
  rw [terminal_length p (by omega)] at hc
  have hleft : Adjacent R a (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    apply p.walk.adj_snd
    intro h
    have hz := h.length_eq_zero
    omega
  have hdist : (cosetGraph R).dist
      (c.path.walk.getVert (p.walk.length - 3)) a = 1 := by
    have h := path_distance c.path (i := p.walk.length - 3)
      (j := p.walk.length - 2) (by omega) (by omega)
    rw [hc] at h
    omega
  have hright : Adjacent R a (c.path.walk.getVert (p.walk.length - 3)) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp hdist))
  exact stabilizer_transitive_neighbors R a hleft hright

/-- Both radius groups in the printed bound lie in Q at δ_(b-4). -/
theorem BackwardChain.radius_bound {a a' : Vertex R} {p : CriticalPath R geometry a a'}
    (hb : 4 < geometry.b R) (c : BackwardChain p ((p.walk.length - 2) / 2))
    {g : FreeAmalgam R}
    (hturn : act R g (p.walk.getVert 1) = c.path.walk.getVert (p.walk.length - 3)) :
    V R a ⊔ V R (act R g (p.walk.getVert 2)) ≤ Q R (c.path.walk.getVert 2) := by
  have hl : c.path.walk.length = p.walk.length :=
    c.path.length_eq_b.trans p.length_eq_b.symm
  have hp := p.length_eq_b
  have hc := c.start_vertex
  rw [terminal_length p (by omega)] at hc
  have he : Even p.walk.length := by
    rw [hp]
    exact geometry.even (alpha R) rfl
  have h6 : 6 ≤ p.walk.length := by rw [Nat.even_iff] at he; omega
  apply sup_le
  · apply V_le_Q_of_dist_add_two_lt R (geometry := geometry) p.start_color
    have h := path_distance c.path (i := 2)
      (j := p.walk.length - 2) (by omega) (by omega)
    rw [hc, SimpleGraph.dist_comm] at h
    omega
  · apply V_le_Q_of_dist_add_two_lt R (geometry := geometry)
      ((action_preserves_color R g _).trans ((p.vertex_color (by omega)).mpr (by decide)))
    have h1 : (cosetGraph R).dist (act R g (p.walk.getVert 2))
        (c.path.walk.getVert (p.walk.length - 3)) = 1 := by
      rw [← hturn, dist_act, SimpleGraph.dist_comm, path_distance p (by decide) (by omega)]
    have h2 : (cosetGraph R).dist (c.path.walk.getVert (p.walk.length - 3))
        (c.path.walk.getVert 2) = p.walk.length - 5 := by
      rw [SimpleGraph.dist_comm, path_distance c.path (by omega) (by omega)]
      omega
    have ht : (cosetGraph R).dist (act R g (p.walk.getVert 2)) (c.path.walk.getVert 2) ≤
        (cosetGraph R).dist (act R g (p.walk.getVert 2))
          (c.path.walk.getVert (p.walk.length - 3)) +
        (cosetGraph R).dist (c.path.walk.getVert (p.walk.length - 3))
          (c.path.walk.getVert 2) := (cosetGraph_connected R).dist_triangle
    omega

/-- Joint normality gives V₁ ≤ V V₁ = (V V₁)^g ≤ V_a V_(a+2)^g,
and hence the exact backward-kernel containment used before defining R₁. -/
theorem BackwardChain.reverseSpan_le_kernel {a a' : Vertex R}
    {p : CriticalPath R geometry a a'} (hb : 4 < geometry.b R)
    (c : BackwardChain p ((p.walk.length - 2) / 2))
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hturn : act R g (p.walk.getVert 1) = c.path.walk.getVert (p.walk.length - 3)) :
    localZSpan R a (p.walk.getVert 2) ≤ Q R (c.path.walk.getVert 2) := by
  let J := localZSpan R (p.walk.getVert 2) a ⊔ localZSpan R a (p.walk.getVert 2)
  have heq : J.map (MulAut.conj g⁻¹).toMonoidHom = J := by
    exact mem_normalizer_iff_map_conj_eq.mp (hnorm ((stabilizer R a).inv_mem hg))
  have hd : (cosetGraph R).dist a (p.walk.getVert 2) = 2 :=
    p.dist_start (by have hh := p.length_eq_b; omega)
  have hfirst : localZSpan R (p.walk.getVert 2) a ≤ V R a :=
    localZSpan_le_V R (by rw [SimpleGraph.dist_comm, hd])
  have hlast : localZSpan R a (p.walk.getVert 2) ≤ V R (p.walk.getVert 2) :=
    localZSpan_le_V R hd.le
  have hga : act R g a = a := hg
  have hmap : J.map (MulAut.conj g⁻¹).toMonoidHom ≤
      V R a ⊔ V R (act R g (p.walk.getVert 2)) := by
    change (localZSpan R (p.walk.getVert 2) a ⊔
      localZSpan R a (p.walk.getVert 2)).map _ ≤ _
    rw [Subgroup.map_sup]
    apply sup_le_sup
    · have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hfirst
      rwa [← V_act, hga] at h
    · have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hlast
      rwa [← V_act] at h
  have hJ : J ≤ Q R (c.path.walk.getVert 2) := by
    rw [← heq]
    exact hmap.trans (c.radius_bound hb hturn)
  exact le_sup_right.trans hJ


/-- Assemble the backward path, actual neighbor conjugator and reverse-span
containment. Joint normality remains explicit for the source argument. -/
theorem exists_backward_configuration [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 4 < geometry.b R)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    ∃ c : BackwardChain p ((p.walk.length - 2) / 2),
      ∃ g ∈ stabilizer R a,
        act R g (p.walk.getVert 1) = c.path.walk.getVert (p.walk.length - 3) ∧
        localZSpan R a (p.walk.getVert 2) ≤ Q R (c.path.walk.getVert 2) := by
  obtain ⟨c⟩ := exists_backwardChain common p ((p.walk.length - 2) / 2)
    (by have hh := terminal_length p (by omega); omega)
  obtain ⟨g, hg, ht⟩ := c.exists_neighbor_conjugator hb
  exact ⟨c, g, hg, ht, c.reverseSpan_le_kernel hb hnorm hg ht⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape
