module

public import Theory.GroupAction.CubicTree.Tracks
public import Theory.GroupAction.CubicTree.ArcReversal
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# The even case of Weiss's local arc-regularity bound

For a faithful locally arc-regular cubic tree action, an even regularity length
is at most four. We prove only the even branch needed by Goldschmidt (4.3).
The acting group may be infinite; its edge stabilizers are finite two-groups.

Write the contrary even length as `2*m+2`, with `m ≥ 2`. A nonidentity central
element of an edge stabilizer fixes the closed edge ball of radius `m` and
moves every vertex in the next layer. Two such elements centered `m+1` edges
apart have a commutator fixing a `3*m`-arc but moving its next vertex. Arc
freeness gives the contradiction. Acyclicity supplies the unique-geodesic
arguments for which the original graph proof invokes a girth bound.

Source: R. M. Weiss, *Über lokal s-reguläre Graphen*, Journal of Combinatorial
Theory B 20 (1976), 124--127, specifically the even case on pp.124--125;
D. M. Goldschmidt, *Automorphisms of trivalent graphs* (1980), (4.3), p.393.
-/

@[expose] public section
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree

namespace Theory.GroupAction.CubicTree.WeissEven
variable {V G : Type*} {Γ : SimpleGraph V} [Group G] [MulAction G V]

private theorem first_base {n : ℕ} {x y : V} (h : x=y) (p : BasedWalk Γ (n+1) x) :
    ((h ▸ p).1 : V) = p.1 := by subst y; rfl

private theorem endpoint_base {n : ℕ} {x y : V} (h : x=y) (p : BasedWalk Γ n x) :
    (h ▸ p).endpoint = p.endpoint := by subst y; rfl

private def append : {n m : ℕ} → {x : V} → (p : BasedWalk Γ n x) →
    BasedWalk Γ m p.endpoint → BasedWalk Γ (m+n) x
  | 0, _, _, _, q => q
  | _+1, _, _, p, q => ⟨p.1, append p.2 q⟩

private theorem endpoint_append {n m : ℕ} {x : V} (p : BasedWalk Γ n x)
    (q : BasedWalk Γ m p.endpoint) : (append p q).endpoint = q.endpoint := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih p.2 q

private def Joins : {n m : ℕ} → {x : V} → (p : BasedWalk Γ n x) →
    BasedWalk Γ m p.endpoint → Prop
  | 0, _, _, _, _ => True
  | _, 0, _, _, _ => True
  | _+1, _+1, _, p, q => (q.1 : V) ≠ p.penultimate

private theorem nb_append {n m : ℕ} {x : V} (p : BasedWalk Γ n x)
    (q : BasedWalk Γ m p.endpoint) (hp : p.Nonbacktracking)
    (hq : q.Nonbacktracking) (hjoin : Joins p q) : (append p q).Nonbacktracking := by
  induction n generalizing x with
  | zero => exact hq
  | succ n ih =>
    cases n with
    | zero =>
      cases m with
      | zero => trivial
      | succ m => exact ⟨hjoin, hq⟩
    | succ n =>
      have ht : Joins p.2 q := by cases m <;> exact hjoin
      exact ⟨hp.1, ih p.2 q hp.2 hq ht⟩

private theorem path_length_eq_dist (hΓ : Γ.IsAcyclic) {x y : V}
    (p : Γ.Walk x y) (hp : p.IsPath) : p.length = Γ.dist x y := by
  obtain ⟨q, hq, hlen⟩ := p.reachable.exists_path_of_dist
  have he : p = q := Subtype.mk.inj
    ((hΓ.subsingleton_path x y).elim ⟨p, hp⟩ ⟨q, hq⟩)
  exact he ▸ hlen

private theorem nonbacktracking_dist (hΓ : Γ.IsAcyclic) {n : ℕ} {x : V}
    (p : BasedWalk Γ n x) (hp : p.Nonbacktracking) :
    Γ.dist x p.endpoint = n := by
  have hp' := isPath_of_nonbacktracking_of_cycle_bound
    (N := n) (fun v c hc => (hΓ c hc).elim) p hp le_rfl
  exact (path_length_eq_dist hΓ p.toWalk hp').symm.trans (BasedWalk.length_toWalk p)

private theorem line_dist (hΓ : Γ.IsAcyclic) (l : Line Γ) (i : ℤ) (n : ℕ) :
    Γ.dist (l.vertex i) (l.vertex (i+n)) = n := by
  let p := sequenceWalk l.vertex l.adjacent i n
  have hp := sequenceWalk_nonbacktracking l.vertex l.adjacent
    (fun j h => by have := l.injective h; omega) i n
  rw [← sequenceWalk_endpoint l.vertex l.adjacent i n]
  exact nonbacktracking_dist hΓ p hp

private theorem fork_first_distance (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    {n : ℕ} {x : V} (p : BasedWalk Γ (n+1) x) (hp : p.Nonbacktracking)
    (a : G) (hx : a • x = x) (hmoved : a • (p.1 : V) ≠ p.1) :
    Γ.dist (p.1 : V) (a • p.endpoint) = n + 2 := by
  let q : BasedWalk Γ (n+1) x := hx ▸ p.map (hact.hom a)
  have hq : q.Nonbacktracking := (nonbacktracking_cast_base hx _).2
    ((hact.nonbacktracking_map_iff a p).2 hp)
  have hfirst : (q.1 : V) = a • (p.1 : V) := by
    exact first_base hx _
  let r : BasedWalk Γ (n+2) (p.1 : V) := ⟨⟨x, p.1.property.symm⟩, q⟩
  have hr : r.Nonbacktracking := ⟨by change (q.1 : V) ≠ p.1; rw [hfirst]; exact hmoved, hq⟩
  have hend : r.endpoint = a • p.endpoint := by
    change q.endpoint = _
    exact (endpoint_base hx _).trans (BasedWalk.endpoint_map _ _)
  rw [← hend]
  exact nonbacktracking_dist hΓ r hr

private theorem fork_endpoint_distance (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    {n : ℕ} {x : V} (p : BasedWalk Γ (n+1) x) (hp : p.Nonbacktracking)
    (a : G) (hx : a • x = x) (hmoved : a • (p.1 : V) ≠ p.1) :
    Γ.dist p.endpoint (a • p.endpoint) = 2*(n+1) := by
  let r := reverse p
  let q : BasedWalk Γ (n+1) r.endpoint :=
    (hx.trans (endpoint_reverse p).symm) ▸ p.map (hact.hom a)
  have hq : q.Nonbacktracking := (nonbacktracking_cast_base _ _).2
    ((hact.nonbacktracking_map_iff a p).2 hp)
  have hfirst : (q.1 : V) = a • (p.1 : V) := first_base _ _
  have hjoin : Joins r q := by
    change (q.1 : V) ≠ r.penultimate
    rw [hfirst, penultimate_reverse]
    exact hmoved
  have hnb := nb_append r q (nonbacktracking_reverse p hp) hq hjoin
  have hend : (append r q).endpoint = a • p.endpoint :=
    (endpoint_append r q).trans ((endpoint_base _ _).trans (BasedWalk.endpoint_map _ _))
  rw [← hend]
  convert nonbacktracking_dist hΓ (append r q) hnb using 1
  omega

private theorem line_dist_le (hΓ : Γ.IsAcyclic) (l : Line Γ) (i j : ℤ) (m : ℕ)
    (hlo : i-m ≤ j) (hhi : j ≤ i+m) : Γ.dist (l.vertex i) (l.vertex j) ≤ m := by
  rcases le_total i j with hij | hji
  · have he : i + ((j-i).toNat : ℤ) = j := by omega
    have hd := line_dist hΓ l i (j-i).toNat
    rw [he] at hd
    rw [hd]
    omega
  · have he : j + ((i-j).toNat : ℤ) = i := by omega
    have hd := line_dist hΓ l j (i-j).toNat
    rw [he] at hd
    rw [Γ.dist_comm, hd]
    omega

private def FixesEdgeBall (a : G) (x y : V) (m : ℕ) : Prop :=
  ∀ v, Γ.dist x v ≤ m ∨ Γ.dist y v ≤ m → a • v = v

private def MovesEdgeSphere (a : G) (x y : V) (m : ℕ) : Prop :=
  ∀ v, min (Γ.dist x v) (Γ.dist y v) = m+1 → a • v ≠ v

open scoped commutatorElement

private theorem commutator_fixes_interval (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (l : Line Γ) (m : ℕ) (b c : G)
    (hb : FixesEdgeBall (Γ := Γ) b (l.vertex 0) (l.vertex 1) m)
    (hc : FixesEdgeBall (Γ := Γ) c (l.vertex (m+1)) (l.vertex (m+2)) m)
    (i : ℤ) (hlo : -(m:ℤ)+1 ≤ i) (hhi : i ≤ 2*m+1) :
    ⁅b,c⁆ • l.vertex i = l.vertex i := by
  have hbmid : b • l.vertex (m+1) = l.vertex (m+1) :=
    hb _ (Or.inr (line_dist_le hΓ l 1 (m+1) m (by omega) (by omega)))
  have hcfirst : c • l.vertex 1 = l.vertex 1 :=
    hc _ (Or.inl (line_dist_le hΓ l (m+1) 1 m (by omega) (by omega)))
  by_cases hi : i ≤ m+1
  · have hdist := line_dist_le hΓ l 1 i m (by omega) (by omega)
    have hbi : b • l.vertex i = l.vertex i := hb _ (Or.inr hdist)
    have hbci : b • (c⁻¹ • l.vertex i) = c⁻¹ • l.vertex i := by
      apply hb _
      right
      have he := hact.dist_smul c⁻¹ (l.vertex 1) (l.vertex i)
      rw [(inv_smul_eq_iff).2 hcfirst.symm] at he
      exact he.le.trans hdist
    simp only [commutatorElement_def, mul_smul,
      (inv_smul_eq_iff).2 hbci.symm, smul_inv_smul, hbi]
  · have hdist := line_dist_le hΓ l (m+1) i m (by omega) (by omega)
    have hci : c • l.vertex i = l.vertex i := hc _ (Or.inl hdist)
    have hcbi : c • (b⁻¹ • l.vertex i) = b⁻¹ • l.vertex i := by
      apply hc _
      left
      have he := hact.dist_smul b⁻¹ (l.vertex (m+1)) (l.vertex i)
      rw [(inv_smul_eq_iff).2 hbmid.symm] at he
      exact he.le.trans hdist
    simp only [commutatorElement_def, mul_smul,
      (inv_smul_eq_iff).2 hci.symm, hcbi, smul_inv_smul]

private theorem commutator_moves_endpoint (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (l : Line Γ) (m : ℕ) (b c : G)
    (hb : FixesEdgeBall (Γ := Γ) b (l.vertex 0) (l.vertex 1) m)
    (hc : FixesEdgeBall (Γ := Γ) c (l.vertex (m+1)) (l.vertex (m+2)) m)
    (hbmove : MovesEdgeSphere (Γ := Γ) b (l.vertex 0) (l.vertex 1) m)
    (hcmove : MovesEdgeSphere (Γ := Γ) c (l.vertex (m+1)) (l.vertex (m+2)) m) :
    ⁅b,c⁆ • l.vertex (2*m+2) ≠ l.vertex (2*m+2) := by
  have hbmid : b • l.vertex (m+1) = l.vertex (m+1) :=
    hb _ (Or.inr (line_dist_le hΓ l 1 (m+1) m (by omega) (by omega)))
  have hbnext : b • l.vertex (m+2) ≠ l.vertex (m+2) := by
    apply hbmove
    have h0 := line_dist hΓ l 0 (m+2)
    have h1 := line_dist hΓ l 1 (m+1)
    rw [show (0:ℤ)+(m+2:ℕ)=m+2 by omega] at h0
    rw [show (1:ℤ)+(m+1:ℕ)=m+2 by omega] at h1
    rw [h0,h1, min_eq_right (by omega)]
  let p := sequenceWalk l.vertex l.adjacent (m+1) (m+1)
  have hp : p.Nonbacktracking := sequenceWalk_nonbacktracking _ _
    (fun i h => by have := l.injective h; omega) _ _
  have hend : p.endpoint = l.vertex (2*m+2) := by
    rw [sequenceWalk_endpoint]
    congr 1
    omega
  have hfirst : (p.1 : V) = l.vertex (m+2) := by
    change l.vertex ((m+1)+1) = _
    congr 1
  have hbi : b⁻¹ • l.vertex (m+1) = l.vertex (m+1) :=
    (inv_smul_eq_iff).2 hbmid.symm
  have hbinext : b⁻¹ • (p.1 : V) ≠ p.1 := by
    rw [hfirst]
    intro he
    exact hbnext ((inv_smul_eq_iff).1 he).symm
  have hdist₂ := fork_first_distance hΓ hact p hp b⁻¹ hbi hbinext
  rw [hend, hfirst] at hdist₂
  have hdist₁ : Γ.dist (l.vertex (m+1)) (b⁻¹ • l.vertex (2*m+2)) = m+1 := by
    have he := hact.dist_smul b⁻¹ (l.vertex (m+1)) (l.vertex (2*m+2))
    rw [hbi] at he
    rw [he]
    convert line_dist hΓ l (m+1) (m+1) using 1
    congr 2
    omega
  have hcbi : c • (b⁻¹ • l.vertex (2*m+2)) ≠ b⁻¹ • l.vertex (2*m+2) := by
    apply hcmove
    rw [hdist₁, hdist₂, min_eq_left (by omega)]
  have hcy : c • l.vertex (2*m+2) = l.vertex (2*m+2) :=
    hc _ (Or.inr (line_dist_le hΓ l (m+2) (2*m+2) m (by omega) (by omega)))
  simp only [commutatorElement_def, mul_smul, (inv_smul_eq_iff).2 hcy.symm]
  intro he
  exact hcbi ((MulAction.toPerm b).injective (he.trans (smul_inv_smul b _).symm))

private theorem sequenceWalk_vertices_mem (l : Line Γ) (i : ℤ) (n : ℕ) (x : V)
    (hx : x ∈ (sequenceWalk l.vertex l.adjacent i n).vertices) :
    ∃ k : ℕ, k ≤ n ∧ x = l.vertex (i+k) := by
  induction n generalizing i with
  | zero =>
    have he : x = l.vertex i := by simpa [sequenceWalk, BasedWalk.vertices] using hx
    exact ⟨0, le_rfl, by simpa using he⟩
  | succ n ih =>
    change x ∈ l.vertex i :: (sequenceWalk l.vertex l.adjacent (i+1) n).vertices at hx
    rcases List.mem_cons.mp hx with he | ht
    · exact ⟨0, Nat.zero_le _, by simpa using he⟩
    · obtain ⟨k,hk,he⟩ := ih (i+1) ht
      refine ⟨k+1, by omega, he.trans ?_⟩
      congr 1
      omega

/-- Every nonbacktracking arc of length `s` has trivial pointwise stabilizer. -/
def ArcFree (s : ℕ) : Prop :=
  ∀ (x : V) (p : BasedWalk Γ s x), p.Nonbacktracking →
    ∀ a : G, (∀ y ∈ p.vertices, a • y = y) → a = 1

private theorem fixed_distance_lt (hΓ : Γ.IsTree) (hact : GraphAction Γ G)
    {s : ℕ} (hfree : ArcFree (Γ := Γ) (G := G) s) {a : G} (ha : a ≠ 1)
    {x y : V} (hx : a • x = x) (hy : a • y = y) : Γ.dist x y < s := by
  by_contra hn
  have hs : s ≤ Γ.dist x y := by omega
  obtain ⟨p,hp,hend⟩ := BasedWalk.exists_geodesic (hΓ.connected x y)
  have hfix := BasedWalk.fixes_short_walk (N := 2*Γ.dist x y)
    (fun v c hc => (hΓ.isAcyclic c hc).elim) p hp le_rfl
    (actionIso hact a) hx (by change a • p.endpoint = p.endpoint; rw [hend]; exact hy)
  apply ha
  apply hfree x (p.take s hs) (BasedWalk.nonbacktracking_take hs p hp) a
  intro z hz
  apply hfix z
  rw [BasedWalk.vertices_take] at hz
  exact List.mem_of_mem_take hz

private theorem nontrivial_arc_fixer_of_regular
    (hdegree : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    {n : ℕ} {x : V} (p : BasedWalk Γ (n+1) x) (hreg : RightRegular (A := G) p) :
    ∃ a : G, a ≠ 1 ∧ ∀ y ∈ p.vertices, a • y = y := by
  have hcard : (Γ.neighborSet p.endpoint).ncard = 3 := by
    exact hdegree p.endpoint
  obtain ⟨u,v,w,huv,huw,hvw,he⟩ := Set.ncard_eq_three.mp hcard
  have hu : Γ.Adj p.endpoint u := by
    change u ∈ Γ.neighborSet p.endpoint
    rw [he]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
  have hv : Γ.Adj p.endpoint v := by
    change v ∈ Γ.neighborSet p.endpoint
    rw [he]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
  have hw : Γ.Adj p.endpoint w := by
    change w ∈ Γ.neighborSet p.endpoint
    rw [he]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  have htwo : ∃ v w, Forward p v ∧ Forward p w ∧ v ≠ w := by
    by_cases hpu : p.penultimate = u
    · exact ⟨v,w,⟨hv,by simpa [hpu] using huv.symm⟩,
        ⟨hw,by simpa [hpu] using huw.symm⟩,hvw⟩
    by_cases hpv : p.penultimate = v
    · exact ⟨u,w,⟨hu,Ne.symm hpu⟩,⟨hw,by simpa [hpv] using hvw.symm⟩,huw⟩
    · exact ⟨u,v,⟨hu,Ne.symm hpu⟩,⟨hv,Ne.symm hpv⟩,huv⟩
  obtain ⟨v,w,hv,hw,hvw⟩ := htwo
  obtain ⟨a,hafix,ha⟩ := hreg v w hv hw
  refine ⟨a,?_,hafix⟩
  intro he
  subst a
  exact hvw (by simpa only [one_smul] using ha)

private theorem center_fixes_half_line (hΓ : Γ.IsTree) (hact : GraphAction Γ G)
    (l : Line Γ) (m : ℕ) (hfree : ArcFree (Γ := Γ) (G := G) (2*m+2))
    (hlong : ∃ a : G, a ≠ 1 ∧ ∀ i : ℕ, i ≤ 2*m+1 → a • l.vertex i = l.vertex i)
    (b : G) (hb0 : b • l.vertex 0 = l.vertex 0)
    (hcentral : ∀ a : G, a • l.vertex 0 = l.vertex 0 →
      a • l.vertex 1 = l.vertex 1 → Commute a b) :
    ∀ i : ℕ, i ≤ m+1 → b • l.vertex i = l.vertex i := by
  obtain ⟨a,hane,hafix⟩ := hlong
  have hab := hcentral a (hafix 0 (by omega)) (hafix 1 (by omega))
  have hay : a • l.vertex (2*m+1) = l.vertex (2*m+1) := hafix _ le_rfl
  have haby : a • (b • l.vertex (2*m+1)) = b • l.vertex (2*m+1) := by
    rw [← mul_smul,hab.eq,mul_smul,hay]
  have hbound := fixed_distance_lt hΓ hact hfree hane hay haby
  intro i hi
  induction i with
  | zero => exact hb0
  | succ i ih =>
    have hbi : b • l.vertex i = l.vertex i := ih (by omega)
    by_contra hn
    let p := sequenceWalk l.vertex l.adjacent (i:ℤ) (2*m-i+1)
    have hp : p.Nonbacktracking := sequenceWalk_nonbacktracking _ _
      (fun j h => by have := l.injective h; omega) _ _
    have hend : p.endpoint = l.vertex (2*m+1) := by
      rw [sequenceWalk_endpoint]
      congr 1
      omega
    have hfirst : (p.1 : V) = l.vertex (i+1:ℕ) := by
      change l.vertex ((i:ℤ)+1) = _
      congr 1
    have hmoved : b • (p.1 : V) ≠ p.1 := by rw [hfirst]; exact hn
    have hd := fork_endpoint_distance hΓ.isAcyclic hact p hp b hbi hmoved
    rw [hend] at hd
    omega

private theorem first_smul_of_vertices
    {n : ℕ} {x y : V} (p : BasedWalk Γ (n+1) x) (q : BasedWalk Γ (n+1) y)
    (a : G) (he : p.vertices.map (a • ·) = q.vertices) :
    a • (p.1 : V) = q.1 := by
  have ht : p.2.vertices.map (a • ·) = q.2.vertices := (List.cons.inj he).2
  exact Option.some.inj (by
    simpa only [List.head?_map, BasedWalk.head_vertices, Option.map_some] using
      congrArg List.head? ht)

private theorem central_endpoint_iff (hact : GraphAction Γ G)
    {n : ℕ} {x : V} (p q : BasedWalk Γ (n+1) x)
    (hp : p.Nonbacktracking) (hq : q.Nonbacktracking)
    (hfirst : (p.1 : V) = q.1) (htrans : RootPathTransitive Γ G x (n+1))
    (b : G) (hcentral : ∀ a : G, a • x = x → a • (p.1 : V) = p.1 → Commute a b) :
    b • p.endpoint = p.endpoint ↔ b • q.endpoint = q.endpoint := by
  obtain ⟨a,hax,ha⟩ := htrans p q hp hq
  have hafirst : a • (p.1 : V) = p.1 := (first_smul_of_vertices p q a ha).trans hfirst.symm
  have hab := hcentral a hax hafirst
  have hend := endpoint_smul_of_vertices hact a p q ha
  rw [← hend, ← mul_smul, ← hab.eq, mul_smul]
  exact ((MulAction.toPerm a).injective.eq_iff).symm

private def flipLine (l : Line Γ) : Line Γ where
  vertex i := l.vertex (1-i)
  injective := fun i j he => by have := l.injective he; omega
  adjacent i := by
    have ha := (l.adjacent (-i)).symm
    convert ha using 1 <;> congr 1 <;> omega

private theorem central_fixes_oriented_endpoint (hΓ : Γ.IsTree) (hact : GraphAction Γ G)
    (l : Line Γ) (m : ℕ) (hfree : ArcFree (Γ := Γ) (G := G) (2*m+2))
    (hlong : ∃ a : G, a ≠ 1 ∧ ∀ i : ℕ, i ≤ 2*m+1 → a • l.vertex i = l.vertex i)
    (b : G) (hb0 : b • l.vertex 0 = l.vertex 0)
    (hcentral : ∀ a : G, a • l.vertex 0 = l.vertex 0 →
      a • l.vertex 1 = l.vertex 1 → Commute a b)
    {n : ℕ} (hn : n ≤ m) (p : BasedWalk Γ (n+1) (l.vertex 0))
    (hp : p.Nonbacktracking) (hfirst : (p.1 : V) = l.vertex 1)
    (htrans : RootPathTransitive Γ G (l.vertex 0) (n+1)) :
    b • p.endpoint = p.endpoint := by
  let q := sequenceWalk l.vertex l.adjacent 0 (n+1)
  have hq : q.Nonbacktracking := sequenceWalk_nonbacktracking _ _
    (fun i h => by have := l.injective h; omega) _ _
  have he : (q.1 : V) = l.vertex 1 := rfl
  apply (central_endpoint_iff hact q p hq hp (he.trans hfirst.symm) htrans b
    (fun a ha hb => hcentral a ha (he ▸ hb))).1
  have hfix := center_fixes_half_line hΓ hact l m hfree hlong b hb0 hcentral (n+1) (by omega)
  simpa only [q,sequenceWalk_endpoint,zero_add] using hfix

private theorem exists_edge_geodesic (hΓ : Γ.IsTree) {x y z : V} (hxy : Γ.Adj x y)
    (hd : Γ.dist x z = Γ.dist y z + 1) :
    ∃ p : BasedWalk Γ (Γ.dist y z+1) x,
      p.Nonbacktracking ∧ (p.1 : V) = y ∧ p.endpoint = z := by
  obtain ⟨q,hq,hend⟩ := BasedWalk.exists_geodesic (hΓ.connected y z)
  let p : BasedWalk Γ (Γ.dist y z+1) x := ⟨⟨y,hxy⟩,q⟩
  refine ⟨p,?_,rfl,hend⟩
  exact BasedWalk.nonbacktracking_of_geodesic p (by change Γ.dist x q.endpoint = _; rw [hend,hd])

private theorem long_line_fixer
    (hdegree : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (l : Line Γ) (m : ℕ)
    (hreg : ∀ (x : V) (p : BasedWalk Γ (2*m+1) x),
      p.Nonbacktracking → RightRegular (A := G) p) :
    ∃ a : G, a ≠ 1 ∧ ∀ i : ℕ, i ≤ 2*m+1 → a • l.vertex i = l.vertex i := by
  let p := sequenceWalk l.vertex l.adjacent 0 (2*m+1)
  have hp : p.Nonbacktracking := sequenceWalk_nonbacktracking _ _
    (fun i h => by have := l.injective h; omega) _ _
  obtain ⟨a,hane,hafix⟩ := nontrivial_arc_fixer_of_regular hdegree p (hreg _ p hp)
  refine ⟨a,hane,?_⟩
  intro i hi
  apply hafix
  simpa only [zero_add] using sequenceWalk_mem_vertices l.vertex l.adjacent 0 _ i hi

private theorem center_fixes_edgeBall (hΓ : Γ.IsTree) (hact : GraphAction Γ G)
    (hdegree : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (l : Line Γ) (m : ℕ) (hfree : ArcFree (Γ := Γ) (G := G) (2*m+2))
    (hshort : ∀ (k : ℕ) (x : V) (p : BasedWalk Γ k x),
      k < 2*m+2 → p.Nonbacktracking → RightRegular (A := G) p)
    (b : G) (hb0 : b • l.vertex 0 = l.vertex 0) (hb1 : b • l.vertex 1 = l.vertex 1)
    (hcentral : ∀ a : G, a • l.vertex 0 = l.vertex 0 →
      a • l.vertex 1 = l.vertex 1 → Commute a b) :
    FixesEdgeBall (Γ := Γ) b (l.vertex 0) (l.vertex 1) m := by
  have hlong (l' : Line Γ) := long_line_fixer hdegree l' m
    (fun x p hp => hshort _ x p (by omega) hp)
  have hroot (x : V) (n : ℕ) (hn : n ≤ 2*m+2) : RootPathTransitive Γ G x n :=
    rootPathTransitive_of_short_rightRegular hact _ hshort x n hn
  intro z hz
  have hd : Γ.dist (l.vertex 0) z = Γ.dist (l.vertex 1) z + 1 ∨
      Γ.dist (l.vertex 1) z = Γ.dist (l.vertex 0) z + 1 := by
    simpa only [SimpleGraph.dist_comm,zero_add] using hΓ.dist_eq_dist_add_one_of_adj z (l.adjacent 0)
  rcases hd with hd | hd
  · obtain ⟨p,hp,hfirst,hend⟩ := exists_edge_geodesic hΓ (l.adjacent 0) hd
    have hn : Γ.dist (l.vertex 1) z ≤ m := by rcases hz with hz | hz <;> omega
    have he := central_fixes_oriented_endpoint hΓ hact l m hfree (hlong l) b hb0
      hcentral hn p hp hfirst (hroot _ _ (by omega))
    rwa [hend] at he
  · let l' := flipLine l
    have he0 : l'.vertex 0 = l.vertex 1 := by simp [l',flipLine]
    have he1 : l'.vertex 1 = l.vertex 0 := by simp [l',flipLine]
    have hadj : Γ.Adj (l'.vertex 0) (l'.vertex 1) := l'.adjacent 0
    have hd' : Γ.dist (l'.vertex 0) z = Γ.dist (l'.vertex 1) z + 1 := by rwa [he0,he1]
    obtain ⟨p,hp,hfirst,hend⟩ := exists_edge_geodesic hΓ hadj hd'
    have hn : Γ.dist (l'.vertex 1) z ≤ m := by rw [he1]; rcases hz with hz | hz <;> omega
    have hb0' : b • l'.vertex 0 = l'.vertex 0 := by rwa [he0]
    have hcentral' : ∀ a : G, a • l'.vertex 0 = l'.vertex 0 →
        a • l'.vertex 1 = l'.vertex 1 → Commute a b := by
      intro a ha0 ha1
      rw [he0] at ha0
      rw [he1] at ha1
      exact hcentral a ha1 ha0
    have he := central_fixes_oriented_endpoint hΓ hact l' m hfree (hlong l') b hb0'
      hcentral' hn p hp hfirst (hroot _ _ (by omega))
    rwa [hend] at he

private theorem central_moves_oriented_endpoint (hΓ : Γ.IsTree) (hact : GraphAction Γ G)
    (l : Line Γ) (m : ℕ) (hfree : ArcFree (Γ := Γ) (G := G) (2*m+2))
    (b : G) (hbne : b ≠ 1)
    (hb : FixesEdgeBall (Γ := Γ) b (l.vertex 0) (l.vertex 1) m)
    (hcentral : ∀ a : G, a • l.vertex 0 = l.vertex 0 →
      a • l.vertex 1 = l.vertex 1 → Commute a b)
    {n : ℕ} (hn : n = m+1) (p : BasedWalk Γ (n+1) (l.vertex 0))
    (hp : p.Nonbacktracking) (hfirst : (p.1 : V) = l.vertex 1)
    (htrans : RootPathTransitive Γ G (l.vertex 0) (n+1)) :
    b • p.endpoint ≠ p.endpoint := by
  intro hfix
  let q := sequenceWalk l.vertex l.adjacent 0 (n+1)
  have hq : q.Nonbacktracking := sequenceWalk_nonbacktracking _ _
    (fun i h => by have := l.injective h; omega) _ _
  have he : (q.1 : V) = l.vertex 1 := rfl
  have hqfix := (central_endpoint_iff hact q p hq hp (he.trans hfirst.symm) htrans b
    (fun a ha hb => hcentral a ha (he ▸ hb))).2 hfix
  have hbneg : b • l.vertex (-(m:ℤ)) = l.vertex (-(m:ℤ)) :=
    hb _ (Or.inl (line_dist_le hΓ.isAcyclic l 0 (-(m:ℤ)) m (by omega) (by omega)))
  have hd := fixed_distance_lt hΓ hact hfree hbne hbneg hqfix
  have hlen := line_dist hΓ.isAcyclic l (-(m:ℤ)) (2*m+2)
  have hend : q.endpoint = l.vertex (-(m:ℤ)+(2*m+2:ℕ)) := by
    rw [sequenceWalk_endpoint]
    congr 1
    omega
  rw [hend,hlen] at hd
  omega

private theorem center_moves_edgeSphere (hΓ : Γ.IsTree) (hact : GraphAction Γ G)
    (l : Line Γ) (m : ℕ) (hfree : ArcFree (Γ := Γ) (G := G) (2*m+2))
    (htrans : ∀ (x : V) (n : ℕ), n ≤ 2*m+2 → RootPathTransitive Γ G x n)
    (b : G) (hbne : b ≠ 1)
    (hb : FixesEdgeBall (Γ := Γ) b (l.vertex 0) (l.vertex 1) m)
    (hcentral : ∀ a : G, a • l.vertex 0 = l.vertex 0 →
      a • l.vertex 1 = l.vertex 1 → Commute a b) :
    MovesEdgeSphere (Γ := Γ) b (l.vertex 0) (l.vertex 1) m := by
  intro z hz
  have hd : Γ.dist (l.vertex 0) z = Γ.dist (l.vertex 1) z + 1 ∨
      Γ.dist (l.vertex 1) z = Γ.dist (l.vertex 0) z + 1 := by
    simpa only [SimpleGraph.dist_comm,zero_add] using hΓ.dist_eq_dist_add_one_of_adj z (l.adjacent 0)
  rcases hd with hd | hd
  · obtain ⟨p,hp,hfirst,hend⟩ := exists_edge_geodesic hΓ (l.adjacent 0) hd
    have hn : Γ.dist (l.vertex 1) z = m+1 := by omega
    have he := central_moves_oriented_endpoint hΓ hact l m hfree b hbne hb
      hcentral hn p hp hfirst (htrans _ _ (by omega))
    rwa [hend] at he
  · let l' := flipLine l
    have he0 : l'.vertex 0 = l.vertex 1 := by simp [l',flipLine]
    have he1 : l'.vertex 1 = l.vertex 0 := by simp [l',flipLine]
    have hadj : Γ.Adj (l'.vertex 0) (l'.vertex 1) := l'.adjacent 0
    have hd' : Γ.dist (l'.vertex 0) z = Γ.dist (l'.vertex 1) z + 1 := by rwa [he0,he1]
    obtain ⟨p,hp,hfirst,hend⟩ := exists_edge_geodesic hΓ hadj hd'
    have hn : Γ.dist (l'.vertex 1) z = m+1 := by rw [he1]; omega
    have hb' : FixesEdgeBall (Γ := Γ) b (l'.vertex 0) (l'.vertex 1) m := by
      intro w hw
      rw [he0,he1] at hw
      exact hb w hw.symm
    have hcentral' : ∀ a : G, a • l'.vertex 0 = l'.vertex 0 →
        a • l'.vertex 1 = l'.vertex 1 → Commute a b := by
      intro a ha0 ha1
      rw [he0] at ha0
      rw [he1] at ha1
      exact hcentral a ha1 ha0
    have he := central_moves_oriented_endpoint hΓ hact l' m hfree b hbne hb'
      hcentral' hn p hp hfirst (htrans _ _ (by omega))
    rwa [hend] at he

/-- The pointwise stabilizer of the ordered edge. -/
def edgeStabilizer (G : Type*) [Group G] [MulAction G V] (x y : V) : Subgroup G :=
  MulAction.stabilizer G x ⊓ MulAction.stabilizer G y

private theorem exists_radial_element (hΓ : Γ.IsTree) (hact : GraphAction Γ G)
    (hdegree : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (l : Line Γ) (m : ℕ) (hfree : ArcFree (Γ := Γ) (G := G) (2*m+2))
    (hshort : ∀ (k : ℕ) (x : V) (p : BasedWalk Γ k x),
      k < 2*m+2 → p.Nonbacktracking → RightRegular (A := G) p)
    [Finite (edgeStabilizer G (l.vertex 0) (l.vertex 1))]
    (htwo : IsPGroup 2 (edgeStabilizer G (l.vertex 0) (l.vertex 1))) :
    ∃ b : G, FixesEdgeBall (Γ := Γ) b (l.vertex 0) (l.vertex 1) m ∧
      MovesEdgeSphere (Γ := Γ) b (l.vertex 0) (l.vertex 1) m := by
  let H := edgeStabilizer G (l.vertex 0) (l.vertex 1)
  obtain ⟨a,hane,hafix⟩ := long_line_fixer hdegree l m
    (fun x p hp => hshort _ x p (by omega) hp)
  let aH : H := ⟨a,⟨hafix 0 (by omega),hafix 1 (by omega)⟩⟩
  have haH : aH ≠ 1 := fun he => hane (congrArg Subtype.val he)
  let : Nontrivial H := ⟨⟨aH,1,haH⟩⟩
  let : Nontrivial (Subgroup.center H) := htwo.center_nontrivial
  obtain ⟨z,hzne⟩ := exists_ne (1 : Subgroup.center H)
  let b : G := z.val.val
  have hbne : b ≠ 1 := fun he => hzne (Subtype.ext (Subtype.ext he))
  have hb0 : b • l.vertex 0 = l.vertex 0 := z.val.property.1
  have hb1 : b • l.vertex 1 = l.vertex 1 := z.val.property.2
  have hcentral : ∀ a : G, a • l.vertex 0 = l.vertex 0 →
      a • l.vertex 1 = l.vertex 1 → Commute a b := by
    intro a ha0 ha1
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property ⟨a,ha0,ha1⟩)
  have hb := center_fixes_edgeBall hΓ hact hdegree l m hfree hshort b hb0 hb1 hcentral
  refine ⟨b,hb,center_moves_edgeSphere hΓ hact l m hfree ?_ b hbne hb hcentral⟩
  intro x n hn
  exact rootPathTransitive_of_short_rightRegular hact _ hshort x n hn

private def shiftLine (l : Line Γ) (j : ℤ) : Line Γ where
  vertex i := l.vertex (i+j)
  injective := fun i k he => by have := l.injective he; omega
  adjacent i := by
    convert l.adjacent (i+j) using 1
    congr 1
    omega

private theorem radial_pair_impossible (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (l : Line Γ) (m : ℕ) (hm : 2 ≤ m) (hfree : ArcFree (Γ := Γ) (G := G) (2*m+2))
    (b c : G)
    (hb : FixesEdgeBall (Γ := Γ) b (l.vertex 0) (l.vertex 1) m)
    (hc : FixesEdgeBall (Γ := Γ) c (l.vertex (m+1)) (l.vertex (m+2)) m)
    (hbmove : MovesEdgeSphere (Γ := Γ) b (l.vertex 0) (l.vertex 1) m)
    (hcmove : MovesEdgeSphere (Γ := Γ) c (l.vertex (m+1)) (l.vertex (m+2)) m) : False := by
  let p := sequenceWalk l.vertex l.adjacent (-(m:ℤ)+1) (2*m+2)
  have hp : p.Nonbacktracking := sequenceWalk_nonbacktracking _ _
    (fun i h => by have := l.injective h; omega) _ _
  have he : ⁅b,c⁆ = 1 := hfree _ p hp _ (by
    intro x hx
    obtain ⟨k,hk,rfl⟩ := sequenceWalk_vertices_mem l _ _ x hx
    exact commutator_fixes_interval hΓ hact l m b c hb hc _ (by omega) (by omega))
  have hn := commutator_moves_endpoint hΓ hact l m b c hb hc hbmove hcmove
  rw [he, one_smul] at hn
  exact hn rfl


/-- Weiss's even bound, with finite two-group edge stabilizers and the literal
nonbacktracking-arc action. No finiteness assumption on the tree is needed. -/
theorem even_arc_length_le_four (hΓ : Γ.IsTree) (hact : GraphAction Γ G)
    (hdegree : ∀ x, Nat.card (Γ.neighborSet x) = 3)
    (l : Line Γ) (s : ℕ) (hseven : Even s)
    (hfree : ArcFree (Γ := Γ) (G := G) s)
    (hshort : ∀ (k : ℕ) (x : V) (p : BasedWalk Γ k x),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hfinite : ∀ x y, Γ.Adj x y → Finite (edgeStabilizer G x y))
    (htwo : ∀ x y, Γ.Adj x y → IsPGroup 2 (edgeStabilizer G x y)) : s ≤ 4 := by
  by_contra hlarge
  obtain ⟨k,hk⟩ := hseven
  have hs : s = 2*(k-1)+2 := by omega
  rw [hs] at hfree hshort
  let m := k-1
  let : Finite (edgeStabilizer G (l.vertex 0) (l.vertex 1)) :=
    hfinite _ _ (l.adjacent 0)
  obtain ⟨b,hb,hbm⟩ := exists_radial_element hΓ hact hdegree l m hfree hshort
    (htwo _ _ (l.adjacent 0))
  let l' := shiftLine l (m+1)
  let : Finite (edgeStabilizer G (l'.vertex 0) (l'.vertex 1)) :=
    hfinite _ _ (l'.adjacent 0)
  obtain ⟨c,hc,hcm⟩ := exists_radial_element hΓ hact hdegree l' m hfree hshort
    (htwo _ _ (l'.adjacent 0))
  have he0 : l'.vertex 0 = l.vertex (m+1) := by simp [l',shiftLine]
  have he1 : l'.vertex 1 = l.vertex (m+2) := by
    change l.vertex (1+(m+1)) = _
    congr 1
    omega
  rw [he0,he1] at hc hcm
  exact radial_pair_impossible hΓ.isAcyclic hact l m (by dsimp [m]; omega)
    hfree b c hb hc hbm hcm


end Theory.GroupAction.CubicTree.WeissEven
