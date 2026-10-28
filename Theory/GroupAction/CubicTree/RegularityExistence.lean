module

public import Theory.GroupAction.CubicTree.TotalSingularity
public import Theory.GroupAction.CubicTree.SingularKernel
public import Theory.GroupAction.CubicTree.WeissEven
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# A regularity length for a locally finite cubic action

For a faithful, vertex-transitive and locally transitive action on a connected
cubic graph, finite vertex stabilizers force a first singular arc length.
Transitivity on shorter arcs and reversal make every arc of that length
singular at both endpoints. Kernel propagation proves that its stabilizer is
trivial. The orbit map then counts the vertex stabilizer as `3 * 2^(s-1)`.

The acting group and vertex set need not be finite. This is the regularity
existence step of Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(5.2), using the finite-stabilizer argument of Tutte (1959), Sections 2.1--2.2.
The separate upper bound on the regularity length is not asserted here.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree

open SimpleGraph SimpleGraph.PathTransitivePolygon
universe u v
variable {V : Type u} {A : Type v} {Γ : SimpleGraph V}
variable [Group A] [MulAction A V]

private theorem card_forward_cubic
    (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    [∀ x, Finite (Γ.neighborSet x)] (n : ℕ) (a b : V) (hab : Γ.Adj a b) :
    Nat.card (BasedWalk.Forward Γ n a b) = 2 ^ n := by
  classical
  induction n generalizing a b with
  | zero => simp [BasedWalk.Forward]
  | succ n ih =>
    let p : BasedWalk Γ 1 a := ⟨⟨b, hab⟩, PUnit.unit⟩
    let e : {c : Γ.neighborSet b // c.val ≠ a} ≃ {z : V // Forward p z} := {
      toFun c := ⟨c.val, c.val.property, c.property⟩
      invFun z := ⟨⟨z, z.property.1⟩, z.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    have htwo : Nat.card {c : Γ.neighborSet b // c.val ≠ a} = 2 :=
      (Nat.card_congr e).trans (card_forward_of_cubic p (hcubic b))
    let : Fintype {c : Γ.neighborSet b // c.val ≠ a} := Fintype.ofFinite _
    change Nat.card (Σ c : {c : Γ.neighborSet b // c.val ≠ a},
      BasedWalk.Forward Γ n b c.val) = _
    rw [Nat.card_sigma]
    have hs : (∑ c : {c : Γ.neighborSet b // c.val ≠ a},
        Nat.card (BasedWalk.Forward Γ n b c.val)) =
        ∑ _c : {c : Γ.neighborSet b // c.val ≠ a}, 2 ^ n := by
      apply Finset.sum_congr rfl
      intro c _
      exact ih b c.val c.val.property
    rw [hs]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, htwo, pow_succ]
    exact Nat.mul_comm _ _

/-- Cubic arc counting needs no bipartition or finiteness of the vertex set. -/
theorem card_nonbacktracking_cubic
    (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3) (n : ℕ) (x : V) :
    Nat.card {p : BasedWalk Γ (n + 1) x // p.Nonbacktracking} = 3 * 2 ^ n := by
  classical
  let : ∀ x, Finite (Γ.neighborSet x) := fun x =>
    Nat.finite_of_card_ne_zero (by rw [hcubic x]; decide)
  let : Fintype (Γ.neighborSet x) := Fintype.ofFinite _
  rw [Nat.card_congr (BasedWalk.nonbacktrackingEquivForward Γ n x), Nat.card_sigma]
  have hs : (∑ y : Γ.neighborSet x, Nat.card (BasedWalk.Forward Γ n x y)) =
      ∑ _y : Γ.neighborSet x, 2 ^ n := by
    apply Finset.sum_congr rfl
    intro y _
    exact card_forward_cubic hcubic n x y y.property
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, hcubic x]
  rfl

private def arcOrbit (hact : GraphAction Γ A) {n : ℕ} {x : V}
    (p : BasedWalk Γ n x) (hp : p.Nonbacktracking) (a : MulAction.stabilizer A x) :
    {q : BasedWalk Γ n x // q.Nonbacktracking} :=
  ⟨(show (hact.hom a) x = x from a.property) ▸ p.map (hact.hom a),
    (nonbacktracking_cast_base (show (hact.hom a) x = x from a.property)
      (p.map (hact.hom a))).2 ((hact.nonbacktracking_map_iff a p).2 hp)⟩

private theorem vertices_arcOrbit (hact : GraphAction Γ A) {n : ℕ} {x : V}
    (p : BasedWalk Γ n x) (hp : p.Nonbacktracking) (a : MulAction.stabilizer A x) :
    (arcOrbit hact p hp a).val.vertices = p.vertices.map ((a : A) • ·) := by
  exact (vertices_cast_base (show (hact.hom a) x = x from a.property)
    (p.map (hact.hom a))).trans (BasedWalk.vertices_map _ _)

private theorem arcOrbit_surjective (hact : GraphAction Γ A)
    {n : ℕ} {x : V} (ht : RootPathTransitive Γ A x n)
    (p : BasedWalk Γ n x) (hp : p.Nonbacktracking) :
    Function.Surjective (arcOrbit hact p hp) := by
  intro q
  obtain ⟨a, hax, ha⟩ := ht p q.val hp q.property
  refine ⟨⟨a, hax⟩, Subtype.ext ?_⟩
  apply BasedWalk.vertices_injective n x
  exact (vertices_arcOrbit hact p hp _).trans ha

/-- Pointwise arc freeness makes the stabilizer orbit map injective. -/
theorem card_stabilizer_of_arcFree
    (hact : GraphAction Γ A) (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    {s : ℕ} (hs : 0 < s) (hfree : WeissEven.ArcFree (Γ := Γ) (G := A) s)
    (hshort : ∀ (k : ℕ) (x : V) (p : BasedWalk Γ k x),
      k < s → p.Nonbacktracking → RightRegular (A := A) p) (x : V) :
    Nat.card (MulAction.stabilizer A x) = 3 * 2 ^ (s - 1) := by
  have hc : Nat.card {p : BasedWalk Γ s x // p.Nonbacktracking} = 3 * 2 ^ (s - 1) := by
    have he : (s - 1) + 1 = s := by omega
    have hc := card_nonbacktracking_cubic hcubic (s - 1) x
    rw [he] at hc
    exact hc
  obtain ⟨p, hp⟩ := (Nat.card_pos_iff.mp (show
    0 < Nat.card {p : BasedWalk Γ s x // p.Nonbacktracking} by rw [hc]; positivity)).1
  have ht := rootPathTransitive_of_short_rightRegular hact s hshort x s le_rfl
  have hinj : Function.Injective (arcOrbit hact p hp) := by
    intro a b hab
    have he : p.vertices.map ((a : A) • ·) = p.vertices.map ((b : A) • ·) := by
      rw [← vertices_arcOrbit hact p hp a, ← vertices_arcOrbit hact p hp b, hab]
    have hab' : ∀ y ∈ p.vertices, (a : A) • y = (b : A) • y :=
      List.map_eq_map_iff.mp he
    have hfix : ∀ y ∈ p.vertices, ((b : A)⁻¹ * a) • y = y := by
      intro y hy
      rw [mul_smul, hab' y hy, inv_smul_smul]
    have hba := hfree x p hp _ hfix
    exact Subtype.ext (inv_mul_eq_one.mp hba).symm
  exact (Nat.card_congr (Equiv.ofBijective _
    ⟨hinj, arcOrbit_surjective hact ht p hp⟩)).trans hc

private theorem exists_nonregular_arc_of_finite_stabilizer
    (hact : GraphAction Γ A) (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (x : V) [Finite (MulAction.stabilizer A x)] :
    ∃ n, ∃ y, ∃ p : BasedWalk Γ n y,
      p.Nonbacktracking ∧ ¬ RightRegular (A := A) p := by
  classical
  by_contra hall
  push Not at hall
  let d := Nat.card (MulAction.stabilizer A x)
  have hc := card_nonbacktracking_cubic hcubic d x
  obtain ⟨p, hp⟩ := (Nat.card_pos_iff.mp (show
      0 < Nat.card {p : BasedWalk Γ (d + 1) x // p.Nonbacktracking} by
        rw [hc]; positivity)).1
  have ht : RootPathTransitive Γ A x (d + 1) :=
    rootPathTransitive_of_short_rightRegular hact (d + 1)
      (fun k y q _ hq => hall k y q hq) x (d + 1) le_rfl
  have hle := Nat.card_le_card_of_surjective _ (arcOrbit_surjective hact ht p hp)
  have hpow : d < 2 ^ d := Nat.lt_two_pow_self
  rw [hc] at hle
  change 3 * 2 ^ d ≤ d at hle
  omega

private theorem exists_first_singular_length
    (hact : GraphAction Γ A) (hconn : Γ.Connected)
    (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (hlocal : ∀ {x y z : V}, Γ.Adj x y → Γ.Adj x z →
      ∃ a : A, a • x = x ∧ a • y = z)
    (hfin : ∀ x : V, Finite (MulAction.stabilizer A x)) :
    ∃ s : ℕ, 0 < s ∧
      (∀ (k : ℕ) (x : V) (p : BasedWalk Γ k x),
        k < s → p.Nonbacktracking → RightRegular (A := A) p) ∧
      ∃ x, ∃ p : BasedWalk Γ s x, p.Nonbacktracking ∧ ¬ RightRegular (A := A) p := by
  classical
  let x := hconn.nonempty.some
  let : Finite (MulAction.stabilizer A x) := hfin x
  have hbad := exists_nonregular_arc_of_finite_stabilizer hact hcubic x
  let s := Nat.find hbad
  have hmin : ∀ k < s, ¬ ∃ x, ∃ p : BasedWalk Γ k x,
      p.Nonbacktracking ∧ ¬ RightRegular (A := A) p :=
    fun k hk => Nat.find_min hbad hk
  have hs : s ≠ 0 := by
    intro he
    have hb : ∃ x, ∃ p : BasedWalk Γ s x,
        p.Nonbacktracking ∧ ¬ RightRegular (A := A) p := Nat.find_spec hbad
    rw [he] at hb
    obtain ⟨y, p, _, hn⟩ := hb
    cases p
    exact hn (rightRegular_zero_of_neighbor_transitive hlocal y)
  refine ⟨s, Nat.pos_of_ne_zero hs, ?_, Nat.find_spec hbad⟩
  intro k y p hk hp
  by_contra hn
  exact hmin k hk ⟨y, p, hp, hn⟩

private theorem arcFree_of_first_singular_length [FaithfulSMul A V]
    (hact : GraphAction Γ A) (hconn : Γ.Connected)
    (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (hvertex : ∀ x y : V, ∃ a : A, a • x = y)
    {s : ℕ} (hs : 0 < s)
    (hshort : ∀ (k : ℕ) (x : V) (p : BasedWalk Γ k x),
      k < s → p.Nonbacktracking → RightRegular (A := A) p)
    {x : V} (p : BasedWalk Γ s x) (hp : p.Nonbacktracking)
    (hn : ¬ RightRegular (A := A) p) : WeissEven.ArcFree (Γ := Γ) (G := A) s := by
  have hnot : ∀ (y : V) (q : BasedWalk Γ s y),
      q.Nonbacktracking → ¬ RightRegular (A := A) q := by
    intro y q hq hreg
    obtain ⟨a, ha⟩ := arcTransitive_of_short_rightRegular hact s hshort le_rfl
      q p hq hp (hvertex y x)
    exact hn (rightRegular_of_conjugate hact q p a ha hreg)
  have hdeg : BasedWalk.HasTwoNeighbors Γ := by
    intro y z
    apply Set.exists_ne_of_one_lt_ncard
    change 1 < Nat.card (Γ.neighborSet y)
    rw [hcubic y]
    decide
  have hsing : ∀ (y : V) (q : BasedWalk Γ s y), q.Nonbacktracking →
      ∀ a : A, (∀ z ∈ q.vertices, a • z = z) →
      (∀ z, Forward q z → a • z = z) ∧ (∀ z, Backward q z → a • z = z) := by
    intro y q hq a ha
    have hnright := hnot y q hq
    have hnleft : ¬ LeftRegular (A := A) q := fun hr =>
      hnot _ (reverse q) (nonbacktracking_reverse q hq)
        ((rightRegular_reverse_iff q).2 hr)
    cases s with
    | zero => omega
    | succ n =>
      exact ⟨fun _ hz => fixes_forward_of_not_rightRegular hact q
          (hcubic q.endpoint) hnright a ha hz,
        fun _ hz => fixes_backward_of_not_leftRegular hact q (hcubic y) hnleft a ha hz⟩
  intro y q hq a ha
  exact eq_one_of_all_totallySingular hconn.preconnected hdeg hs hsing q hq a ha

/-- A faithful, vertex-transitive, locally transitive cubic action with finite
vertex stabilizers has a finite regularity length, and its literal local order
is the number of nonbacktracking arcs of that length. -/
theorem exists_arcRegularityLength [FaithfulSMul A V]
    (hact : GraphAction Γ A) (hconn : Γ.Connected)
    (hcubic : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (hvertex : ∀ x y : V, ∃ a : A, a • x = y)
    (hlocal : ∀ {x y z : V}, Γ.Adj x y → Γ.Adj x z →
      ∃ a : A, a • x = x ∧ a • y = z)
    (hfin : ∀ x : V, Finite (MulAction.stabilizer A x)) :
    ∃ s : ℕ, 0 < s ∧
      (∀ (k : ℕ) (x : V) (p : BasedWalk Γ k x),
        k < s → p.Nonbacktracking → RightRegular (A := A) p) ∧
      WeissEven.ArcFree (Γ := Γ) (G := A) s ∧
      ∀ x : V, Nat.card (MulAction.stabilizer A x) = 3 * 2 ^ (s - 1) := by
  obtain ⟨s, hs, hshort, x, p, hp, hn⟩ :=
    exists_first_singular_length hact hconn hcubic hlocal hfin
  have hfree := arcFree_of_first_singular_length hact hconn hcubic hvertex hs hshort p hp hn
  exact ⟨s, hs, hshort, hfree, card_stabilizer_of_arcFree hact hcubic hs hfree hshort⟩

end Theory.GroupAction.CubicTree
