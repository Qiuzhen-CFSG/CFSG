module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Forward

/-!
# Backward extension of critical paths

The endpoint-minus-two escape clause lets us move a critical pair two edges
backwards.  The radius-two definition of `V` supplies a layer missed by the
new endpoint; critical minimality forces that layer to be an M-vertex at
exactly distance two.  The tree metric then keeps the iterated endpoints on
the unique critical path.  Reversing the final pair and applying the forward
nonnormality theorem gives MS93 2.2(v).

Source: Meierfrankenfeld--Stellmacher (1993), pp.856--857.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93

variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

private lemma tree_path_dist {α : Type*} {G : SimpleGraph α} (_hG : G.IsTree)
    {u v : α} {p : G.Walk u v} (_hp : p.IsPath) (hs : p.length = G.dist u v)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i ≤ j) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hsub : ((p.drop i).take (j - i)).IsSubwalk p :=
    (p.drop i).isSubwalk_take _ |>.trans (p.isSubwalk_drop i)
  have hdist : G.dist (p.getVert i) ((p.drop i).getVert (j-i)) = j-i := by
    calc
      _ = ((p.drop i).take (j-i)).length :=
        (SimpleGraph.length_eq_dist_of_subwalk hs hsub).symm
      _ = j-i := by simp [hi, hj]
  have heq : (p.drop i).getVert (j-i) = p.getVert j := by
    rw [SimpleGraph.Walk.drop_getVert]
    have hh : i + (j - i) = j := by omega
    rw [hh]
  simpa [heq] using hdist

private lemma tree_mem_geodesic {α : Type*} {G : SimpleGraph α} (hG : G.IsTree)
    {x y z : α} {p : G.Walk x y} (hp : p.IsPath) (_hs : p.length = G.dist x y)
    (hxy : G.dist x y = G.dist x z + G.dist z y) : z ∈ p.support := by
  obtain ⟨q, hq⟩ := hG.connected.exists_walk_length_eq_dist x z
  obtain ⟨r, hr⟩ := hG.connected.exists_walk_length_eq_dist z y
  let s := q.append r
  have hslen : s.length = G.dist x y := by
    simp only [s, SimpleGraph.Walk.length_append, hq, hr, hxy]
  have hspath : s.IsPath := s.isPath_of_length_eq_dist hslen
  have heq : s = p := congrArg Subtype.val
    (hG.isAcyclic.subsingleton_path x y |>.elim ⟨s, hspath⟩ ⟨p, hp⟩)
  rw [← heq]
  exact (by simp [s])

private lemma tree_index_geodesic {α : Type*} {G : SimpleGraph α} (hG : G.IsTree)
    {x y z : α} {p : G.Walk x y} (_hp : p.IsPath) (hs : p.length = G.dist x y)
    {i : ℕ} (hi : i ≤ p.length) (hz : p.getVert i = z) :
    i = G.dist x z := by
  have htake : (p.take i).length = i := by simp [hi]
  have hle : G.dist x z ≤ i := by
    have hh := SimpleGraph.dist_le (p.take i)
    simpa [hz, htake] using hh
  have hdrop : (p.drop i).length = p.length - i := by simp
  have hle' : G.dist z y ≤ p.length - i := by
    have hh := SimpleGraph.dist_le (p.drop i)
    simpa [hz, hdrop] using hh
  have htri := hG.connected.dist_triangle (u := x) (v := z) (w := y)
  omega

private lemma tree_geodesic_dist {α : Type*} {G : SimpleGraph α} (hG : G.IsTree)
    {x y z w : α} {p : G.Walk x y} (hp : p.IsPath) (hs : p.length = G.dist x y)
    (hz : G.dist x y = G.dist x z + G.dist z y)
    (hw : G.dist x y = G.dist x w + G.dist w y) :
    (G.dist z w = G.dist x w - G.dist x z ∨
      G.dist z w = G.dist x z - G.dist x w) := by
  have hz' := tree_mem_geodesic hG hp hs hz
  obtain ⟨i, hzi, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz'
  have hiz := tree_index_geodesic hG hp hs hi hzi
  have hw' := tree_mem_geodesic hG hp hs hw
  obtain ⟨j, hwj, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw'
  have hjw := tree_index_geodesic hG hp hs hj hwj
  by_cases h : i ≤ j
  · left
    rw [← hiz, ← hjw]
    simpa [hzi, hwj] using tree_path_dist hG hp hs hi hj h
  · right
    have h' : j ≤ i := by omega
    rw [← hiz, ← hjw]
    have hh := tree_path_dist hG hp hs hj hi h'
    simpa [hzi, hwj, SimpleGraph.dist_comm] using hh

omit [Finite M] in
private lemma Z_adjacent_le {u d : Vertex R} (hu : color R u = false)
    (hadj : Adjacent R u d) (hd : color R d = true) : Z R d ≤ Z R u := by
  have hdne : color R d ≠ false := by rw [hd]; decide
  rw [Z, if_neg hdne, Z, if_pos hu]
  exact le_iSup_of_le d (le_iSup_of_le hadj le_rfl)

omit [Finite M] in
private lemma extend_critical_step (g : Geometry R)
    (u : Vertex R) (hu : color R u = false)
    (v : Vertex R) (_hv : color R v = false)
    (hc : CriticalPair R u v (g.exists_critical u hu))
    (e : Vertex R) (_hve : (cosetGraph R).dist e v = 2)
    (hue : (cosetGraph R).dist u e + 2 = (cosetGraph R).dist u v)
    (hnot : ¬ V R u ≤ Q R e) :
    ∃ (d : Vertex R) (hd : color R d = false),
      (cosetGraph R).dist d u = 2 ∧
      CriticalPair R d e (g.exists_critical d hd) := by
  classical
  have hex : ∃ d, (cosetGraph R).dist d u ≤ 2 ∧ ¬ Z R d ≤ Q R e := by
    by_contra hn
    push Not at hn
    apply hnot
    rw [V, VBall]
    apply iSup_le
    intro d
    apply iSup_le
    intro hd
    exact hn d hd
  obtain ⟨d, hdu, hZd⟩ := hex
  have hdistue : (cosetGraph R).dist u e < criticalDistance R u (g.exists_critical u hu) := by
    rw [hc.1] at hue
    omega
  have hZu : Z R u ≤ Q R e := Z_le_Q_of_dist_lt R u (g.exists_critical u hu) hdistue
  have hdu2 : (cosetGraph R).dist d u = 2 := by
    by_contra hn2
    have hcases : (cosetGraph R).dist d u = 0 ∨ (cosetGraph R).dist d u = 1 := by omega
    rcases hcases with hzero | hone
    · have hdeq : d = u := (cosetGraph_connected R).dist_eq_zero_iff.mp hzero
      subst d
      exact hZd hZu
    · have hadj : Adjacent R u d := by
        apply (cosetGraph_adj R u d).mp
        apply SimpleGraph.dist_eq_one_iff_adj.mp
        rwa [SimpleGraph.dist_comm]
      have hdcol : color R d = true := by
        have hne := adjacent_color_ne R hadj
        cases hh : color R d <;> simp_all
      exact hZd ((Z_adjacent_le R hu hadj hdcol).trans hZu)
  have hdcol : color R d = false := by
    have hcol := color_eq_of_dist_even R u d (by rw [SimpleGraph.dist_comm, hdu2]; decide)
    exact hcol.symm.trans hu
  have he_d := g.exists_critical d hdcol
  have hdistde_le : (cosetGraph R).dist d e ≤ criticalDistance R u (g.exists_critical u hu) := by
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := u) (w := e)
    rw [hdu2] at htri
    rw [hc.1] at hue
    omega
  have hconst : criticalDistance R d he_d = criticalDistance R u (g.exists_critical u hu) := by
    rw [g.distance_constant d hdcol, g.distance_constant u hu]
  have hdistde_ge : criticalDistance R u (g.exists_critical u hu) ≤
      (cosetGraph R).dist d e := by
    rw [← hconst]
    exact criticalDistance_le R d he_d hZd
  have hdistde : (cosetGraph R).dist d e = criticalDistance R d he_d := by omega
  refine ⟨d, hdcol, hdu2, ?_⟩
  exact ⟨hdistde, hZd⟩

private lemma tree_chain {α : Type*} (G : SimpleGraph α) (hG : G.IsTree)
    {x z w y : α} (hzpos : 0 < G.dist z w)
    (h1 : G.dist x w = G.dist x z + G.dist z w)
    (h2 : G.dist z y = G.dist z w + G.dist w y) :
    G.dist x y = G.dist x z + G.dist z w + G.dist w y := by
  induction hl : G.dist w y using Nat.strong_induction_on generalizing x z w with
  | h n ih =>
    by_cases hn : n = 0
    · have hwy : w = y := hG.connected.dist_eq_zero_iff.mp (by omega)
      subst y
      omega
    · obtain ⟨p, hp⟩ := hG.connected.exists_walk_length_eq_dist w y
      cases p with
      | nil => simp at hl; omega
      | @cons w t y hwt p =>
        have hwt' : G.Adj w t := hwt
        have hty : G.dist t y + 1 = G.dist w y := by
          have hle := SimpleGraph.dist_le p
          have htri := hG.connected.dist_triangle (u := w) (v := t) (w := y)
          have hone : G.dist w t = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwt
          simp only [SimpleGraph.Walk.length_cons] at hp
          omega
        have hzt_cases := hG.dist_eq_dist_add_one_of_adj z hwt'
        have hzt : G.dist z t = G.dist z w + 1 := by
          rcases hzt_cases with hback | hfwd
          · have htri := hG.connected.dist_triangle (u := z) (v := t) (w := y)
            omega
          · exact hfwd
        have hxt_cases := hG.dist_eq_dist_add_one_of_adj x hwt'
        have hxt : G.dist x t = G.dist x w + 1 := by
          rcases hxt_cases with hback | hfwd
          · obtain ⟨q, hq⟩ := hG.connected.exists_walk_length_eq_dist x w
            have hqpath := q.isPath_of_length_eq_dist hq
            have htw : G.dist t w = 1 := by
              exact SimpleGraph.dist_eq_one_iff_adj.mpr hwt.symm
            have h1t : G.dist x w = G.dist x t + G.dist t w := by omega
            have hdist := tree_geodesic_dist hG hqpath hq h1 h1t
            omega
          · exact hfwd
        have h1' : G.dist x t = G.dist x z + G.dist z t := by omega
        have h2' : G.dist z y = G.dist z t + G.dist t y := by omega
        have hzpos' : 0 < G.dist z t := by omega
        have hlt : G.dist t y < n := by omega
        have ih' := ih (G.dist t y) hlt hzpos' h1' h2'
        omega

omit [Finite M] in
private lemma predecessor_two (d e : Vertex R) (hde : 2 ≤ (cosetGraph R).dist d e) :
    ∃ e', (cosetGraph R).dist e' e = 2 ∧
      (cosetGraph R).dist d e' + 2 = (cosetGraph R).dist d e := by
  have hde_sym : 2 ≤ (cosetGraph R).dist e d := by simpa only [SimpleGraph.dist_comm] using hde
  obtain ⟨t, hte, htd⟩ := exists_adjacent_dist_sub_one R e d (by omega)
  obtain ⟨e', he't, hed2⟩ := exists_adjacent_dist_sub_one R t d (by omega)
  have htd' : (cosetGraph R).dist d t + 1 = (cosetGraph R).dist d e := by
    simpa only [SimpleGraph.dist_comm] using htd
  have hed2' : (cosetGraph R).dist d e' + 1 = (cosetGraph R).dist d t := by
    simpa only [SimpleGraph.dist_comm] using hed2
  have hde' : (cosetGraph R).dist d e' + 2 = (cosetGraph R).dist d e := by
    omega
  have hupper : (cosetGraph R).dist e' e ≤ 2 := by
    let hp : (cosetGraph R).Walk e' e :=
      .cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R he't))
        (.cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R hte)) .nil)
    have hh := SimpleGraph.dist_le hp
    simpa only [hp, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] using hh
  have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := e') (w := e)
  have hlower : 2 ≤ (cosetGraph R).dist e' e := by omega
  exact ⟨e', by omega, hde'⟩

omit [Finite M] in
private lemma shift_critical (g : Geometry R)
    (u : Vertex R) (hu : color R u = false)
    (v : Vertex R) (hv : color R v = false)
    (hc : CriticalPair R u v (g.exists_critical u hu))
    (hesc : Factorization.CriticalEscape R g) :
    ∀ n, 2 * n + 2 ≤ (cosetGraph R).dist u v →
      ∃ (d e : Vertex R) (hd : color R d = false) (_he : color R e = false),
        CriticalPair R d e (g.exists_critical d hd) ∧
        (cosetGraph R).dist d u = 2 * n ∧
        (cosetGraph R).dist e v = 2 * n ∧
        (cosetGraph R).dist d e = (cosetGraph R).dist u v ∧
        (cosetGraph R).dist d e = (cosetGraph R).dist d u + (cosetGraph R).dist u e ∧
        (cosetGraph R).dist d v = (cosetGraph R).dist d e + (cosetGraph R).dist e v := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨u, v, hu, hv, hc, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · rfl
      · simp
      · simp
  | succ n ih =>
      intro hn
      obtain ⟨d, e, hd, he, hpair, hdu, hev, hde, hue, hdev⟩ := ih (by omega)
      have hde2 : 2 ≤ (cosetGraph R).dist d e := by omega
      obtain ⟨e', he'e, hdee'⟩ := predecessor_two R d e hde2
      have he' : color R e' = false := by
        have hh := color_eq_of_dist_even (R := R) e' e (by rw [he'e]; decide)
        exact hh.trans he
      have hnot := hesc d hd e hpair e' he'e hdee'
      obtain ⟨d', hd', hdd', hpair'⟩ :=
        extend_critical_step R g d hd e he hpair e' he'e hdee' hnot
      have hde' : (cosetGraph R).dist d' e' = (cosetGraph R).dist u v := by
        have hconst : criticalDistance R d' (g.exists_critical d' hd') =
            criticalDistance R d (g.exists_critical d hd) := by
          rw [g.distance_constant d' hd', g.distance_constant d hd]
        have hcrit : criticalDistance R d (g.exists_critical d hd) =
            (cosetGraph R).dist u v := hpair.1.symm.trans hde
        have hcrit' : criticalDistance R d' (g.exists_critical d' hd') =
            (cosetGraph R).dist u v := by rw [hconst, hcrit]
        exact hpair'.1.trans hcrit'
      have hdeprev : (cosetGraph R).dist d e' + (cosetGraph R).dist e' e =
          (cosetGraph R).dist d e := by omega
      obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist d e
      have hpp := p.isPath_of_length_eq_dist hp
      have hcases := tree_geodesic_dist (G := cosetGraph R) g.tree
        hpp hp hue hdeprev.symm
      have hue' : (cosetGraph R).dist d e' =
          (cosetGraph R).dist d u + (cosetGraph R).dist u e' := by
        have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := u) (w := e')
        rcases hcases with hcase | hcase <;> omega
      have he'v : (cosetGraph R).dist e' v =
          (cosetGraph R).dist e' e + (cosetGraph R).dist e v := by
        have hup := (cosetGraph_connected R).dist_triangle (u := e') (v := e) (w := v)
        have hlo := (cosetGraph_connected R).dist_triangle (u := d) (v := e') (w := v)
        omega
      have hdev' : (cosetGraph R).dist d v =
          (cosetGraph R).dist d e' + (cosetGraph R).dist e' v := by omega
      have hdu' : (cosetGraph R).dist d' u = 2 * (n + 1) := by
        have hup := (cosetGraph_connected R).dist_triangle (u := d') (v := d) (w := u)
        have hlo := (cosetGraph_connected R).dist_triangle (u := d') (v := u) (w := e')
        omega
      have hde_chain : (cosetGraph R).dist d' e' =
          (cosetGraph R).dist d' d + (cosetGraph R).dist d e' := by omega
      have hdev_chain := tree_chain (cosetGraph R) g.tree
        (by omega : 0 < (cosetGraph R).dist d e') hde_chain hdev'
      have hdev'' : (cosetGraph R).dist d' v =
          (cosetGraph R).dist d' e' + (cosetGraph R).dist e' v := by
        omega
      refine ⟨d', e', hd', he', hpair', hdu', ?_, hde', ?_, hdev''⟩
      · omega
      · have hh := hue'
        omega

/-- MS93 2.2(v): the reverse critical product is nonnormal in its M-vertex stabilizer. -/
theorem critical_nonnormal_reverse (g : Geometry R) (hC : EdgeCentralizerCondition R)
    (hesc : Factorization.CriticalEscape R g)
    (a : Vertex R) (ha : color R a = false)
    (hb : 0 < criticalDistance R a (g.exists_critical a ha))
    {a' : Vertex R} (hcrit : CriticalPair R a a' (g.exists_critical a ha))
    (c : Vertex R) (hac : (cosetGraph R).dist a c = 2)
    (hpath : (cosetGraph R).dist c a' + 2 = (cosetGraph R).dist a a') :
    Z R c ⊔ X R a ≤ stabilizer R a ∧
      ¬ ((Z R c ⊔ X R a).subgroupOf (stabilizer R a)).Normal := by
  have hcontain := reverse_join_le_stabilizer_of_dist_two R g a ha hb c hac
  have hbn : 2 ≤ (cosetGraph R).dist a a' := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * k + 2 = (cosetGraph R).dist a a' := by
    obtain ⟨n, hn⟩ := g.even a ha
    have hdist := hcrit.1
    exact ⟨n - 1, by omega⟩
  obtain ⟨d, e, hd, he, hpair, hdu, hev, hde, hue, hdev⟩ :=
    shift_critical R g a ha a' (critical_endpoint_color R a ha _ hcrit) hcrit hesc k (by omega)
  have hdistue : (cosetGraph R).dist a e = 2 := by omega
  have hepath : (cosetGraph R).dist a e + (cosetGraph R).dist e a' =
      (cosetGraph R).dist a a' := by omega
  have hdistac : (cosetGraph R).dist a c + (cosetGraph R).dist c a' =
      (cosetGraph R).dist a a' := by omega
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a a'
  have hpp := p.isPath_of_length_eq_dist hp
  have hec_cases := tree_geodesic_dist (G := cosetGraph R) g.tree
    hpp hp hepath.symm hdistac.symm
  have hec : e = c := by
    have hzero : (cosetGraph R).dist e c = 0 := by
      rcases hec_cases with hcase | hcase <;> omega
    exact (cosetGraph_connected R).dist_eq_zero_iff.mp hzero
  subst e
  have hbd : 0 < criticalDistance R d (g.exists_critical d hd) := by
    rw [g.distance_constant d hd, ← g.distance_constant a ha]
    exact hb
  have hbc : 0 < criticalDistance R c (g.exists_critical c he) := by
    rw [g.distance_constant c he, ← g.distance_constant a ha]
    exact hb
  have hrev := critical_reverse R g hC d hd hbd c he hpair
  have hforward : (cosetGraph R).dist a d + 2 = (cosetGraph R).dist c d := by
    rw [SimpleGraph.dist_comm (u := a) (v := d),
      SimpleGraph.dist_comm (u := c) (v := d)]
    omega
  have hnorm := critical_nonnormal_forward R g hC c he hbc d hrev a
    (by rwa [SimpleGraph.dist_comm]) hforward
  exact ⟨hcontain, hnorm.2⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
