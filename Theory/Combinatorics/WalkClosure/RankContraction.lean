module
public import Theory.Combinatorics.PairGraphTriangleClosure.Triangulation

/-!
# Contracting graph walks by a vertex rank

A rank with one zero vertex contracts closed walks when horizontal edges
have a lower common neighbor and each two-edge peak can be replaced, modulo
triangles and squares, by a walk entirely below the peak. A length induction
lowers every walk whose endpoints are below the current rank, including the
case of consecutive vertices at the highest rank. Rank induction then kills
rooted loops; conjugation by paths handles every other base vertex.

This is a nonabelian normal-closure argument. Its native octad application is
the four-generation assertion of Aschbacher, *Sporadic Groups* (1994),
Exercise 13.2(2), using the descent idea of §§34 and 38.6–38.7.
-/

@[expose] public section
namespace SimpleGraph.WalkClosure
variable {V : Type*} {Γ : SimpleGraph V}

def shortCycles (Γ : SimpleGraph V) : Cycles Γ := fun _ p => p.length ≤ 4

theorem short_paths {x y : V} (p q : Γ.Walk x y) (h : p.length + q.length ≤ 4) :
    Rel (shortCycles Γ) p q := by
  apply rel_of_closed
  apply Rel.cycle
  change (p.append q.reverse).length ≤ 4
  simpa only [Walk.length_append, Walk.length_reverse] using h

theorem lower_walk (rank : V → ℕ) (n : ℕ)
    (horizontal : ∀ a b, Γ.Adj a b → rank a = n → rank b = n →
      ∃ c, rank c < n ∧ Γ.Adj a c ∧ Γ.Adj c b)
    (peak : ∀ a x b (hax : Γ.Adj a x) (hxb : Γ.Adj x b), rank a < n → rank x = n → rank b < n →
      ∃ q : Γ.Walk a b, (∀ v ∈ q.support, rank v < n) ∧
        Rel (shortCycles Γ) (.cons hax (.cons hxb .nil)) q)
    {a b : V} (p : Γ.Walk a b) (ha : rank a < n) (hb : rank b < n)
    (hp : ∀ v ∈ p.support, rank v ≤ n) :
    ∃ q : Γ.Walk a b, (∀ v ∈ q.support, rank v < n) ∧ Rel (shortCycles Γ) p q := by
  generalize hl : p.length = l
  induction l using Nat.strong_induction_on generalizing a b with
  | h l ih =>
    cases p with
    | nil => exact ⟨.nil, by simpa using ha, .refl _⟩
    | @cons a x b hax p =>
      have hx : rank x ≤ n := hp x (by simp)
      by_cases hxn : rank x < n
      · obtain ⟨q,hq,he⟩ := ih p.length (by simp only [Walk.length_cons] at hl; omega)
          p hxn hb (fun v hv => hp v (by simp [hv])) rfl
        exact ⟨.cons hax q, by simpa using And.intro ha hq, rel_cons hax he⟩
      · have hxe : rank x = n := by omega
        cases p with
        | nil => exact False.elim (hxn hb)
        | @cons x y b hxy p =>
          have hy : rank y ≤ n := hp y (by simp)
          by_cases hyn : rank y < n
          · obtain ⟨q,hq,he⟩ := peak a x y hax hxy ha hxe hyn
            obtain ⟨r,hr,he'⟩ := ih p.length (by simp only [Walk.length_cons] at hl; omega)
              p hyn hb (fun v hv => hp v (by simp [hv])) rfl
            refine ⟨q.append r, ?_, ?_⟩
            · intro v hv
              rcases (Walk.mem_support_append_iff _ _).mp hv with hv | hv
              · exact hq v hv
              · exact hr v hv
            · simpa only [Walk.cons_append, Walk.nil_append] using Rel.append he he'
          · obtain ⟨c,hc,hxc,hcy⟩ := horizontal x y hxy hxe (by omega)
            obtain ⟨q,hq,he⟩ := peak a x c hax hxc ha hxe hc
            obtain ⟨r,hr,he'⟩ := ih (Walk.cons hcy p).length
              (by simp only [Walk.length_cons] at hl ⊢; omega)
              (.cons hcy p) hc hb (by
                intro v hv
                simp only [Walk.support_cons, List.mem_cons] at hv
                rcases hv with rfl | hv
                · omega
                · exact hp v (by simp [hv])) rfl
            refine ⟨q.append r, ?_, ?_⟩
            · intro v hv
              rcases (Walk.mem_support_append_iff _ _).mp hv with hv | hv
              · exact hq v hv
              · exact hr v hv
            · have ht := short_paths (.cons hxy .nil) (.cons hxc (.cons hcy .nil)) (by simp)
              exact (rel_cons hax (Rel.append ht (.refl p))).trans (Rel.append he he')

theorem rooted_short_null (rank : V → ℕ) (root : V) (hroot : rank root = 0)
    (horizontal : ∀ a b, Γ.Adj a b → rank a = rank b →
      ∃ c, rank c < rank a ∧ Γ.Adj a c ∧ Γ.Adj c b)
    (peak : ∀ a x b (hax : Γ.Adj a x) (hxb : Γ.Adj x b), rank a < rank x → rank b < rank x →
      ∃ q : Γ.Walk a b, (∀ v ∈ q.support, rank v < rank x) ∧
        Rel (shortCycles Γ) (.cons hax (.cons hxb .nil)) q)
    (zero : ∀ v, rank v = 0 → v = root) (n : ℕ)
    (p : Γ.Walk root root) (hp : ∀ v ∈ p.support, rank v ≤ n) :
    Rel (shortCycles Γ) p .nil := by
  induction n generalizing p with
  | zero =>
    cases p with
    | nil => exact .refl _
    | cons h p =>
      exact False.elim (h.ne (zero _ (Nat.eq_zero_of_le_zero (hp _ (by simp)))).symm)
  | succ n ih =>
    obtain ⟨q,hq,he⟩ := lower_walk rank (n+1)
      (fun a b hab ha hb => by simpa only [ha] using horizontal a b hab (ha.trans hb.symm))
      (fun a x b hax hxb ha hx hb => by
        simpa only [hx] using peak a x b hax hxb (by omega) (by omega))
      p (by omega) (by omega) hp
    exact he.trans (ih q (fun v hv => Nat.le_of_lt_succ (hq v hv)))

/-- A descending rank supplies paths from the unique zero-rank vertex. -/
theorem exists_walk_of_rank (rank : V → ℕ) (root : V)
    (zero : ∀ v, rank v = 0 → v = root)
    (descend : ∀ v, 0 < rank v → ∃ w, rank w < rank v ∧ Γ.Adj w v) :
    ∀ v, Nonempty (Γ.Walk root v) := by
  intro v
  generalize he : rank v = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hn : n = 0
    · have hv := zero v (he.trans hn)
      subst v
      exact ⟨.nil⟩
    · obtain ⟨w,hw,hwv⟩ := descend v (by omega)
      obtain ⟨p⟩ := ih (rank w) (by omega) w rfl
      exact ⟨p.concat hwv⟩

/-- It suffices to contract loops at a vertex reachable from every vertex. -/
theorem isCycleBase_of_root {S : Cycles Γ} (root : V)
    (paths : ∀ v, Nonempty (Γ.Walk root v))
    (loops : ∀ p : Γ.Walk root root, Rel S p .nil) : IsCycleBase S := by
  intro v p
  obtain ⟨q⟩ := paths v
  have h := rel_of_closed (q.append p) q (loops ((q.append p).append q.reverse))
  have h' := Rel.append (Rel.refl q.reverse) h
  have cancel : Rel S (q.reverse.append q) .nil := by
    simpa only [Walk.reverse_reverse] using Rel.cancel (S := S) q.reverse
  have left := Rel.append cancel (Rel.refl p)
  simp only [Walk.nil_append] at left
  rw [← Walk.append_assoc] at left
  exact left.symm.trans (h'.trans cancel)

/-- Rank descent contracts every loop using only triangles and squares. -/
theorem short_isCycleBase_of_rank (rank : V → ℕ) (root : V) (hroot : rank root = 0)
    (zero : ∀ v, rank v = 0 → v = root)
    (descend : ∀ v, 0 < rank v → ∃ w, rank w < rank v ∧ Γ.Adj w v)
    (horizontal : ∀ a b, Γ.Adj a b → rank a = rank b →
      ∃ c, rank c < rank a ∧ Γ.Adj a c ∧ Γ.Adj c b)
    (peak : ∀ a x b (hax : Γ.Adj a x) (hxb : Γ.Adj x b), rank a < rank x → rank b < rank x →
      ∃ q : Γ.Walk a b, (∀ v ∈ q.support, rank v < rank x) ∧
        Rel (shortCycles Γ) (.cons hax (.cons hxb .nil)) q)
    (n : ℕ) (bound : ∀ v, rank v ≤ n) : IsCycleBase (shortCycles Γ) :=
  isCycleBase_of_root root (exists_walk_of_rank rank root zero descend)
    (fun p => rooted_short_null rank root hroot horizontal peak zero n p (fun v _ => bound v))

end SimpleGraph.WalkClosure
