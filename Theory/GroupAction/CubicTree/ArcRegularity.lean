module

public import Theory.Combinatorics.SimpleGraph.TwoNeighborWalks

/-!
# Regular arcs in a cubic graph

The forward extensions of a nonbacktracking arc are its neighbors other than
the preceding vertex. At length zero they are all neighbors. Right regularity
means that the pointwise stabilizer of the arc is transitive on these extensions.
The local induction below is Goldschmidt's first assertion in (2.12): regularity
of every shorter arc propagates vertex-orbit congruence to arc transitivity.

Source: D. M. Goldschmidt, *Automorphisms of trivalent graphs* (1980),
Lemma (2.12), printed p.383.
-/

@[expose] public section

namespace Theory.GroupAction.CubicTree

open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon

universe u v
variable {V : Type u} {A : Type v} {Γ : SimpleGraph V}
variable [Group A] [MulAction A V]

/-- A possible nonbacktracking continuation, including the zero-length case. -/
def Forward : {n : ℕ} → {x : V} → BasedWalk Γ n x → V → Prop
  | 0, x, _, z => Γ.Adj x z
  | _ + 1, _, p, z => Γ.Adj p.endpoint z ∧ z ≠ p.penultimate

@[simp] theorem vertices_cast_base {n : ℕ} {x y : V} (hxy : x = y)
    (p : BasedWalk Γ n x) : (hxy ▸ p).vertices = p.vertices := by
  subst y
  rfl

@[simp] theorem nonbacktracking_cast_base {n : ℕ} {x y : V} (hxy : x = y)
    (p : BasedWalk Γ n x) : (hxy ▸ p).Nonbacktracking ↔ p.Nonbacktracking := by
  subst y
  rfl

@[simp] theorem forward_cast_base {n : ℕ} {x y z : V} (hxy : x = y)
    (p : BasedWalk Γ n x) : Forward (hxy ▸ p) z ↔ Forward p z := by
  subst y
  rfl

theorem forward_iff_snoc_nonbacktracking {n : ℕ} {x z : V}
    (p : BasedWalk Γ n x) (hp : p.Nonbacktracking)
    (hz : Γ.Adj p.endpoint z) :
    Forward p z ↔ (p.snoc hz).Nonbacktracking := by
  cases n with
  | zero =>
    change Γ.Adj x z ↔ True
    exact iff_true_intro (by change Γ.Adj x z at hz; exact hz)
  | succ n =>
    rw [Forward, nonbacktracking_snoc_iff]
    simp [hz, hp]

theorem snoc_take {n : ℕ} {x : V} (p : BasedWalk Γ (n + 1) x) :
    (p.take n (Nat.le_succ n)).snoc
      (show Γ.Adj (p.take n (Nat.le_succ n)).endpoint p.endpoint from
        by simpa only [BasedWalk.endpoint_take_penultimate] using
          p.adj_penultimate_endpoint) = p := by
  apply BasedWalk.vertices_injective (n + 1) x
  rw [BasedWalk.vertices_snoc, BasedWalk.vertices_eq_prefix_append_endpoint]

theorem penultimate_map (h : GraphAction Γ A) (a : A)
    {n : ℕ} {x : V} (p : BasedWalk Γ (n + 1) x) :
    (p.map (h.hom a)).penultimate = a • p.penultimate := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih p.2

/-- Graph automorphisms preserve precisely the forward extensions of an arc. -/
theorem forward_map_iff (h : GraphAction Γ A) (a : A)
    {n : ℕ} {x z : V} (p : BasedWalk Γ n x) :
    Forward (p.map (h.hom a)) (a • z) ↔ Forward p z := by
  cases n with
  | zero => exact h.adj_iff a
  | succ n =>
    simp only [Forward, BasedWalk.endpoint_map, penultimate_map]
    refine and_congr (h.adj_iff a) ?_
    exact not_congr (MulAction.toPerm a).injective.eq_iff

/-- Pointwise path stabilizer transitivity on forward extensions. -/
def RightRegular {n : ℕ} {x : V} (p : BasedWalk Γ n x) : Prop :=
  ∀ z w, Forward p z → Forward p w →
    ∃ a : A, (∀ y ∈ p.vertices, a • y = y) ∧ a • z = w

/-- The possible left extensions, excluding the first edge of a nontrivial arc. -/
def Backward : {n : ℕ} → {x : V} → BasedWalk Γ n x → V → Prop
  | 0, x, _, z => Γ.Adj x z
  | _ + 1, x, p, z => Γ.Adj x z ∧ z ≠ (p.1 : V)

def LeftRegular {n : ℕ} {x : V} (p : BasedWalk Γ n x) : Prop :=
  ∀ z w, Backward p z → Backward p w →
    ∃ a : A, (∀ y ∈ p.vertices, a • y = y) ∧ a • z = w

def Regular {n : ℕ} {x : V} (p : BasedWalk Γ n x) : Prop :=
  LeftRegular (A := A) p ∧ RightRegular (A := A) p

theorem nonbacktracking_tail {n : ℕ} {x : V} (p : BasedWalk Γ (n + 1) x)
    (hp : p.Nonbacktracking) : p.2.Nonbacktracking := by
  cases n with
  | zero => trivial
  | succ n => exact hp.2

theorem forward_tail {n : ℕ} {x z : V} (p : BasedWalk Γ (n + 1) x)
    (hz : Forward p z) : Forward p.2 z := by
  cases n with
  | zero => exact hz.1
  | succ n => exact hz

theorem forward_adj {n : ℕ} {x z : V} (p : BasedWalk Γ n x)
    (hz : Forward p z) : Γ.Adj p.endpoint z := by
  cases n with
  | zero => exact hz
  | succ n => exact hz.1

/-- The rectangle argument in (2.12). A shorter right-regular arc transports
two nonequivalent forward choices; left regularity at the shifted arc would
then identify them under the original stabilizer, a contradiction. -/
theorem shifted_not_leftRegular (h : GraphAction Γ A)
    {n : ℕ} {x : V} (p : BasedWalk Γ (n + 1) x) (hp : p.Nonbacktracking)
    (htail : RightRegular (A := A) p.2) (hnot : ¬ RightRegular (A := A) p) :
    ∃ z, ∃ hz : Γ.Adj p.2.endpoint z,
      (p.2.snoc hz).Nonbacktracking ∧ ¬ LeftRegular (A := A) (p.2.snoc hz) := by
  classical
  obtain ⟨u, v, hu, hv, hsep⟩ : ∃ u v, Forward p u ∧ Forward p v ∧
      ¬ ∃ a : A, (∀ y ∈ p.vertices, a • y = y) ∧ a • u = v := by
    simp only [RightRegular, not_forall] at hnot
    obtain ⟨u, v, hu, hv, hsep⟩ := hnot
    exact ⟨u, v, hu, hv, hsep⟩
  obtain ⟨g, hgfix, hgu⟩ := htail u v (forward_tail p hu) (forward_tail p hv)
  have hvadj := forward_adj p.2 (forward_tail p hv)
  let q := p.2.snoc hvadj
  refine ⟨v, hvadj, (forward_iff_snoc_nonbacktracking p.2
    (nonbacktracking_tail p hp) hvadj).1 (forward_tail p hv), ?_⟩
  intro hleft
  have hx : Backward q x := by
    cases n with
    | zero => exact ⟨p.1.property.symm, (hv.2).symm⟩
    | succ n => exact ⟨p.1.property.symm, hp.1.symm⟩
  have hgx : Backward q (g • x) := by
    have hy : g • (p.1 : V) = p.1 := hgfix p.1 (by
      have hm := p.2.toWalk.start_mem_support
      simpa only [BasedWalk.support_toWalk] using hm)
    have hadj : Γ.Adj (p.1 : V) (g • x) := by
      simpa only [hy] using h.map_adj g p.1.property.symm
    cases n with
    | zero =>
      refine ⟨hadj, ?_⟩
      change g • x ≠ v
      rw [← hgu]
      exact fun he => hu.2 ((MulAction.toPerm g).injective he).symm
    | succ n =>
      refine ⟨hadj, ?_⟩
      have hy₂ : g • (p.2.1 : V) = p.2.1 := hgfix p.2.1 (by
        change (p.2.1 : V) ∈ (p.1 : V) :: p.2.2.vertices
        exact List.mem_cons_of_mem _ (by
          have hm := p.2.2.toWalk.start_mem_support
          simpa only [BasedWalk.support_toWalk] using hm))
      change g • x ≠ (p.2.1 : V)
      rw [← hy₂]
      exact fun he => hp.1 ((MulAction.toPerm g).injective he).symm
  obtain ⟨a, hafix, hagx⟩ := hleft (g • x) x hgx hx
  apply hsep
  refine ⟨a * g, ?_, ?_⟩
  · intro y hy
    change y ∈ x :: p.2.vertices at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · simpa only [mul_smul] using hagx
    · rw [mul_smul, hgfix y hy]
      apply hafix
      simpa only [BasedWalk.vertices_snoc] using List.mem_append_left [v] hy
  · rw [mul_smul, hgu]
    apply hafix
    simpa only [BasedWalk.vertices_snoc] using
      List.mem_append_right p.2.vertices (List.mem_singleton_self v)

theorem rightRegular_zero_of_neighbor_transitive
    (hlocal : ∀ {x y z : V}, Γ.Adj x y → Γ.Adj x z →
      ∃ a : A, a • x = x ∧ a • y = z) (x : V) :
    RightRegular (Γ := Γ) (A := A) (show BasedWalk Γ 0 x from PUnit.unit) := by
  intro y z hy hz
  obtain ⟨a, hax, hay⟩ := hlocal hy hz
  exact ⟨a, by simpa [BasedWalk.vertices] using hax, hay⟩

/-- Goldschmidt's induction: right regularity of each proper prefix makes the
vertex stabilizer transitive on nonbacktracking arcs of the chosen length. -/
theorem rootPathTransitive_of_short_rightRegular (h : GraphAction Γ A)
    (N : ℕ) (hshort : ∀ (k : ℕ) (x : V) (p : BasedWalk Γ k x),
      k < N → p.Nonbacktracking → RightRegular (A := A) p)
    (x : V) (n : ℕ) (hn : n ≤ N) : RootPathTransitive Γ A x n := by
  induction n with
  | zero =>
    intro p q hp hq
    refine ⟨1, one_smul A x, ?_⟩
    cases p
    cases q
    simp [BasedWalk.vertices]
  | succ n ih =>
    intro p q hp hq
    let p₀ := p.take n (Nat.le_succ n)
    let q₀ := q.take n (Nat.le_succ n)
    have hp₀ : p₀.Nonbacktracking := nonbacktracking_take (Nat.le_succ n) p hp
    have hq₀ : q₀.Nonbacktracking := nonbacktracking_take (Nat.le_succ n) q hq
    obtain ⟨g, hg, hprefix⟩ := ih (by omega) p₀ q₀ hp₀ hq₀
    let r : BasedWalk Γ n x := hg ▸ p₀.map (h.hom g)
    have hrq : r = q₀ := by
      apply BasedWalk.vertices_injective n x
      calc
        r.vertices = (p₀.map (h.hom g)).vertices := vertices_cast_base hg _
        _ = p₀.vertices.map (g • ·) := BasedWalk.vertices_map _ _
        _ = q₀.vertices := hprefix
    have hpforward : Forward p₀ p.endpoint := by
      have hadj : Γ.Adj p₀.endpoint p.endpoint := by
        simpa only [p₀, endpoint_take_penultimate] using p.adj_penultimate_endpoint
      apply (forward_iff_snoc_nonbacktracking p₀ hp₀ hadj).2
      simpa only [p₀, snoc_take] using hp
    have hqforward : Forward q₀ q.endpoint := by
      have hadj : Γ.Adj q₀.endpoint q.endpoint := by
        simpa only [q₀, endpoint_take_penultimate] using q.adj_penultimate_endpoint
      apply (forward_iff_snoc_nonbacktracking q₀ hq₀ hadj).2
      simpa only [q₀, snoc_take] using hq
    have hgforward : Forward q₀ (g • p.endpoint) := by
      rw [← hrq]
      exact (forward_cast_base hg (p₀.map (h.hom g))).2
        ((forward_map_iff h g p₀).2 hpforward)
    obtain ⟨a, hafix, haend⟩ :=
      (hshort n x q₀ (by omega) hq₀) (g • p.endpoint) q.endpoint
        hgforward hqforward
    have hxmem : x ∈ q₀.vertices := by
      have hmem := q₀.toWalk.start_mem_support
      simpa only [BasedWalk.support_toWalk] using hmem
    refine ⟨a * g, by rw [mul_smul, hg]; exact hafix x hxmem, ?_⟩
    have hfixed : q₀.vertices.map (a • ·) = q₀.vertices := by
      simpa only [List.map_id] using
        (List.map_congr_left (f := fun y => a • y) (g := id) hafix)
    calc
      p.vertices.map ((a * g) • ·) =
          (p₀.vertices ++ [p.endpoint]).map ((a * g) • ·) := by
            rw [BasedWalk.vertices_eq_prefix_append_endpoint]
      _ = (p₀.vertices.map (g • ·)).map (a • ·) ++ [a • (g • p.endpoint)] := by
        simp only [List.map_append, List.map_singleton, List.map_map, mul_smul,
          Function.comp_def]
      _ = q₀.vertices ++ [q.endpoint] := by rw [hprefix, hfixed, haend]
      _ = q.vertices := (BasedWalk.vertices_eq_prefix_append_endpoint q).symm

theorem arcTransitive_of_short_rightRegular (h : GraphAction Γ A)
    (N : ℕ) (hshort : ∀ (k : ℕ) (x : V) (p : BasedWalk Γ k x),
      k < N → p.Nonbacktracking → RightRegular (A := A) p)
    {n : ℕ} (hn : n ≤ N) {x y : V}
    (p : BasedWalk Γ n x) (q : BasedWalk Γ n y)
    (hp : p.Nonbacktracking) (hq : q.Nonbacktracking)
    (hxy : ∃ g : A, g • x = y) :
    ∃ a : A, p.vertices.map (a • ·) = q.vertices := by
  obtain ⟨g, hg⟩ := hxy
  let r : BasedWalk Γ n y := hg ▸ p.map (h.hom g)
  have hr : r.Nonbacktracking := by
    unfold r
    cases hg
    exact (h.nonbacktracking_map_iff g p).2 hp
  obtain ⟨a, _, ha⟩ := rootPathTransitive_of_short_rightRegular h N hshort y n hn r q hr hq
  refine ⟨a * g, ?_⟩
  calc
    p.vertices.map ((a * g) • ·) = (p.vertices.map (g • ·)).map (a • ·) := by
      simp only [List.map_map, mul_smul, Function.comp_def]
    _ = r.vertices.map (a • ·) := by
      rw [show r.vertices = p.vertices.map (g • ·) from by
        calc
          r.vertices = (p.map (h.hom g)).vertices := vertices_cast_base hg _
          _ = p.vertices.map (g • ·) := BasedWalk.vertices_map _ _]
    _ = q.vertices := ha

end Theory.GroupAction.CubicTree
