module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentRelation

/-!
# Shortening chains of equal-length paths in a tree

Two tree paths split into a common initial path and two disjoint tails.
This proves both the common-half lemma and the metric bound at a peak of
an identification chain. A shortest chain has no peak if every close
pair of consecutive identifications admits a shortcut. Its distance from
the initial vertex must therefore increase, giving separation of the
entire equivalence closure.

Source: DGS, *Groups and Graphs* (1985), Part II, (3.6), printed p.78.
The apartment shortcut is a local geometric premise here; the accompanying
apartment geometry derives it from uniqueness, path transitivity and exchange.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
variable {V : Type*} {Γ : SimpleGraph V}

theorem tree_path_length (ht : Γ.IsTree) {a b : V} (p : Γ.Walk a b) (hp : p.IsPath) :
    p.length = Γ.dist a b := by
  obtain ⟨q, hq, hl⟩ := ht.connected.exists_path_of_dist a b
  have he : p = q := congrArg Subtype.val (ht.isAcyclic.subsingleton_path a b |>.elim ⟨p,hp⟩ ⟨q,hq⟩)
  exact he ▸ hl

private theorem append_path_of_inter {a b c : V} (p : Γ.Walk a b) (q : Γ.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ z, z ∈ p.support → z ∈ q.support → z = b) :
    (p.append q).IsPath := by
  rw [isPath_def, support_append]
  apply List.Nodup.append hp.support_nodup hq.support_nodup.tail
  intro z hz hzq
  have he := hinter z hz (List.mem_of_mem_tail hzq)
  subst z
  have h := hq.support_nodup
  cases q with
  | nil => simp at hzq
  | cons h q => exact (List.nodup_cons.mp h).1 hzq

private theorem inter_eq_of_snd_ne (ht : Γ.IsAcyclic) {a b c : V}
    (p : Γ.Walk a b) (q : Γ.Walk a c) (hp : p.IsPath) (hq : q.IsPath)
    (hne : p.snd ≠ q.snd) :
    ∀ z, z ∈ p.support → z ∈ q.support → z = a := by
  classical
  intro z hz hzq
  by_contra hza
  have he : p.takeUntil z hz = q.takeUntil z hzq :=
    congrArg Subtype.val (ht.subsingleton_path a z |>.elim
      ⟨_, hp.takeUntil hz⟩ ⟨_, hq.takeUntil hzq⟩)
  apply hne
  simpa only [snd_takeUntil hza] using congrArg SimpleGraph.Walk.snd he

theorem tree_tripod (ht : Γ.IsTree) {a b c : V}
    (p : Γ.Walk a b) (q : Γ.Walk a c) (hp : p.IsPath) (hq : q.IsPath) :
    ∃ t, ∃ l : Γ.Walk a t, ∃ u : Γ.Walk t b, ∃ v : Γ.Walk t c,
      p = l.append u ∧ q = l.append v ∧ (u.reverse.append v).IsPath := by
  induction p generalizing c with
  | @nil a => exact ⟨a, .nil, .nil, q, rfl, rfl, hq⟩
  | @cons a a' b haa p ih =>
    cases q with
    | nil => exact ⟨a, .nil, .cons haa p, .nil, rfl, rfl, by simpa using hp.reverse⟩
    | @cons _ c' c hac q =>
      by_cases he : a' = c'
      · subst c'
        obtain ⟨t, l, u, v, he₁, he₂, hpath⟩ := ih q (cons_isPath_iff _ _ |>.mp hp).1
          (cons_isPath_iff _ _ |>.mp hq).1
        exact ⟨t, .cons haa l, u, v, by simp only [cons_append, he₁],
          by simp only [cons_append, he₂], hpath⟩
      · refine ⟨a, .nil, .cons haa p, .cons hac q, rfl, rfl, ?_⟩
        apply append_path_of_inter _ _ hp.reverse hq
        intro z hz hzq
        apply inter_eq_of_snd_ne ht.isAcyclic (.cons haa p) (.cons hac q) hp hq (by simpa only [SimpleGraph.Walk.snd, getVert_cons_succ, getVert_zero] using he) z
        · simpa only [support_reverse, List.mem_reverse] using hz
        · exact hzq

theorem tree_midpoint_toward (ht : Γ.IsTree) {o a b : V} {n : ℕ}
    (p : Γ.Walk b a) (q : Γ.Walk b o) (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length = 2*n) (hdown : Γ.dist o a ≤ Γ.dist o b) :
    p.getVert n = q.getVert n := by
  obtain ⟨t, l, u, v, he₁, he₂, huv⟩ := tree_tripod ht p q hp hq
  have hdist := tree_path_length ht (u.reverse.append v) huv
  have hdistq := tree_path_length ht q hq
  rw [length_append, length_reverse, SimpleGraph.dist_comm (u := a) (v := o)] at hdist
  rw [he₁, length_append] at hlen
  rw [he₂, length_append, SimpleGraph.dist_comm (u := b) (v := o)] at hdistq
  have hnl : n ≤ l.length := by omega
  simp only [he₁, he₂, getVert_append', if_pos hnl]

theorem tree_peak_distance (ht : Γ.IsTree) {o a b c : V} {n : ℕ}
    (hab : Γ.dist a b = 2*n) (hbc : Γ.dist b c = 2*n)
    (ha : Γ.dist o a ≤ Γ.dist o b) (hc : Γ.dist o c ≤ Γ.dist o b) :
    Γ.dist a c ≤ 2*n := by
  obtain ⟨p, hp, hlp⟩ := ht.connected.exists_path_of_dist b a
  obtain ⟨q, hq, hlq⟩ := ht.connected.exists_path_of_dist b c
  obtain ⟨r, hr, _⟩ := ht.connected.exists_path_of_dist b o
  have hpl : p.length = 2*n := by rw [hlp, SimpleGraph.dist_comm, hab]
  have hql : q.length = 2*n := hlq.trans hbc
  have he : p.getVert n = q.getVert n :=
    (tree_midpoint_toward ht p r hp hr hpl ha).trans
      (tree_midpoint_toward ht q r hq hr hql hc).symm
  have h₁ := SimpleGraph.dist_le (p.drop n)
  have h₂ := SimpleGraph.dist_le (q.drop n)
  rw [drop_length, hpl] at h₁
  rw [drop_length, hql] at h₂
  have htri := ht.connected.dist_triangle (u := a) (v := p.getVert n) (w := c)
  rw [SimpleGraph.dist_comm (u := a) (v := p.getVert n), he] at htri
  rw [he] at h₁
  omega

/-- Equal-length tree paths whose endpoints are at distance at most half their
combined length agree for at least their first half. -/
theorem tree_common_half (ht : Γ.IsTree) {b a c : V} {n : ℕ}
    (p : Γ.Walk b a) (q : Γ.Walk b c) (hp : p.IsPath) (hq : q.IsPath)
    (hp_len : p.length = 2*n) (hq_len : q.length = 2*n)
    (hclose : Γ.dist a c ≤ 2*n) :
    ∀ k ≤ n, p.getVert k = q.getVert k := by
  obtain ⟨t, l, u, v, he₁, he₂, huv⟩ := tree_tripod ht p q hp hq
  have hd := tree_path_length ht (u.reverse.append v) huv
  rw [length_append, length_reverse] at hd
  rw [he₁, length_append] at hp_len
  rw [he₂, length_append] at hq_len
  have hnl : n ≤ l.length := by omega
  intro k hk
  simp only [he₁, he₂, getVert_append', if_pos (hk.trans hnl)]

private theorem shortest_end_bound {Δ : SimpleGraph V} (f : V → ℕ)
    (hshortcut : ∀ {a b c}, Δ.Adj a b → Δ.Adj b c → f a ≤ f b → f c ≤ f b →
      a = c ∨ Δ.Adj a c)
    {a b : V} (p : Δ.Walk a b)
    (hmin : ∀ q : Δ.Walk a b, p.length ≤ q.length)
    (hstart : f a < f p.snd) : f p.snd ≤ f b := by
  induction p with
  | nil => exact le_rfl
  | @cons a c b hac p ih =>
    have hminp : ∀ q : Δ.Walk c b, p.length ≤ q.length := by
      intro q
      have hh := hmin (.cons hac q)
      simpa only [length_cons, Nat.add_le_add_iff_right] using hh
    cases p with
    | nil => exact le_rfl
    | @cons _ d _ hcd q =>
      have hinc : f c < f d := by
        by_contra hneg
        have hpeak := hshortcut hac hcd (by simpa only [snd_cons] using hstart.le)
          (Nat.le_of_not_gt hneg)
        rcases hpeak with rfl | hadj
        · have hh := hmin q
          simp only [length_cons] at hh
          omega
        · have hh := hmin (.cons hadj q)
          simp only [length_cons] at hh
          omega
      simpa only [snd_cons] using hinc.le.trans (by
        simpa only [snd_cons] using ih hminp (by simpa only [snd_cons] using hinc))

theorem separation_of_local_shortcut (ht : Γ.IsTree) {n : ℕ} (hn : 0 < n)
    (Δ : SimpleGraph V) (hlength : ∀ {a b}, Δ.Adj a b → Γ.dist a b = 2*n)
    (hshortcut : ∀ {a b c}, Δ.Adj a b → Δ.Adj b c → Γ.dist a c ≤ 2*n →
      a = c ∨ Δ.Adj a c)
    {a b : V} (hrel : Δ.Reachable a b) (hsmall : Γ.dist a b < 2*n) : a = b := by
  obtain ⟨p, _, hp⟩ := hrel.exists_path_of_dist
  cases p with
  | nil => rfl
  | @cons _ c _ hac p =>
    have hfirst := hlength hac
    have hh := shortest_end_bound (Γ.dist a) (Δ := Δ)
      (fun huv hvw hu hw => hshortcut huv hvw
        (tree_peak_distance ht (hlength huv) (hlength hvw) hu hw))
      (.cons hac p) (fun q => hp.trans_le (SimpleGraph.dist_le q))
      (by simpa only [snd_cons, SimpleGraph.dist_self, hfirst] using (by omega : 0 < 2*n))
    simp only [snd_cons, hfirst] at hh
    omega

theorem apartment_separated_of_shortcut {X : Type*} [Group X] [MulAction X V]
    {T : Set V} {n : ℕ} (ht : Γ.IsTree) (hn : 0 < n)
    (hshortcut : ∀ {a b c}, ApartmentStep (X := X) Γ T n a b →
      ApartmentStep (X := X) Γ T n b c → Γ.dist a c ≤ 2*n →
      a = c ∨ ApartmentStep (X := X) Γ T n a c) :
    Separated (apartmentSetoid (X := X) Γ T n) Γ (2*n) := by
  let Δ : SimpleGraph V := {
    Adj := ApartmentStep (X := X) Γ T n
    symm := ⟨fun _ _ => apartmentStep_symm⟩
    loopless := ⟨fun a h => by
      have hh := apartmentStep_distance ht h
      rw [SimpleGraph.dist_self] at hh
      omega⟩ }
  intro a b hab hsmall
  have hr : Δ.Reachable a b := by
    clear hsmall
    induction hab with
    | rel a b h => exact SimpleGraph.Adj.reachable (G := Δ) h
    | refl a => exact SimpleGraph.Reachable.refl a
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact separation_of_local_shortcut ht hn Δ (fun h => apartmentStep_distance ht h)
    hshortcut hr hsmall
end Theory.GroupTheory.WeakBNPair.RegularTree
