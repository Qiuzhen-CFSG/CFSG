module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.AlternatingLength
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.EndpointIndices
public import Theory.GroupAction.RankTwoCosetGeometry.ProjectivePlane
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry

/-!
# The generalized triangle of a marked BN quotient

When the product of the two marked simple reflections has order three,
the incidence graph of the two actual singleton parabolics has diameter
at most three and unique geodesics of length less than three.

Three alternating transitions in a hypothetical four-cycle lie in a
length-three Bruhat cell, while the final transition has length one.
Bruhat-index uniqueness rules this out. For the diameter, lift reduced
alternating Weyl words to paths between the literal normalizer cosets;
the longest word may start at either endpoint. Bruhat coverage then puts
any two vertices in a translate of that apartment. Neither splitness,
local perfectness nor a model-group identification is used.

Source: the BN-pair geometry in DGS, Groups and Graphs, Theorem D,
printed p.224, and Carter §2.5. This is its m=3 geometry step, not the
subsequent Fong–Seitz group recognition.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleGeometry
open RootCoordinates Subgroup.CosetGeometry.RankTwo
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)

/-- The original two marked parabolics, with their endpoint order unchanged. -/
def family (b : Bool) : Subgroup (X ⧸ d.D) :=
  d.tits.standardParabolic {d.simple (if b then 1 else 0)}

private theorem borel_le (b : Bool) : d.tits.B ≤ family d b :=
  d.tits.B_le_standardParabolic _

private theorem mem_parabolic (b : Bool) (x : X ⧸ d.D) :
    x ∈ family d b ↔ x ∈ d.tits.B ∨ x ∈ d.tits.bruhatCell (d.simple (if b then 1 else 0)) := by
  change x ∈ (d.tits.standardParabolic {_} : Set _) ↔ _
  rw [singleton_parabolic_cells (d.simple_mem _)]
  rfl

private theorem flip_type {v w : Vertex (family d)} (h : (graph (family d)).Adj v w) :
    w.type = !v.type := by
  have := h.1
  cases hv : v.type <;> cases hw : w.type <;> simp_all

private theorem transition_cell {u v w : Vertex (family d)}
    (huv : (graph (family d)).Adj u v) (hvw : (graph (family d)).Adj v w) (hne : u ≠ w)
    (g h : X ⧸ d.D)
    (hgu : g • base (family d) u.type = u)
    (hgv : g • base (family d) v.type = v)
    (hhv : h • base (family d) v.type = v)
    (hhw : h • base (family d) w.type = w) :
    g⁻¹ * h ∈ d.tits.bruhatCell (d.simple (if v.type then 1 else 0)) := by
  have hm : g⁻¹ * h ∈ family d v.type :=
    (DihedralGeometry.smul_base_eq_iff (family d) g h v.type).mp (hgv.trans hhv.symm)
  apply (mem_parabolic d v.type _).mp hm |>.resolve_left
  intro hb
  apply hne
  have ht : u.type = w.type := by
    rw [flip_type d hvw, flip_type d huv, Bool.not_not]
  have he : g • base (family d) u.type = h • base (family d) u.type :=
    (DihedralGeometry.smul_base_eq_iff (family d) g h u.type).mpr (borel_le d u.type hb)
  exact hgu.symm.trans (he.trans (ht ▸ hhw))

private theorem short_gallery_cell (g : ℕ → X ⧸ d.D) (t : ℕ → Bool)
    {n : ℕ} (hn : n ≤ rotationOrder d)
    (hstep : ∀ k < n, (g k)⁻¹ * g (k + 1) ∈ d.tits.bruhatCell (d.simple (if t k then 1 else 0)))
    (hflip : ∀ k, k + 1 < n → t (k + 1) = !(t k)) :
    (g 0)⁻¹ * g n ∈ d.tits.bruhatCell (alternatingWord d (t 0) n) := by
  induction n generalizing g t with
  | zero => simp [alternatingWord, d.tits.bruhatCell_one]
  | succ n ih =>
    have htail := ih (fun k => g (k + 1)) (fun k => t (k + 1)) (by omega)
      (fun k hk => hstep (k + 1) (by omega)) (fun k hk => hflip (k + 1) (by omega))
    have hindex : d.simple (if t 0 then 1 else 0) * alternatingWord d (t 1) n =
        alternatingWord d (t 0) (n + 1) := by
      by_cases hz : n = 0
      · simp [hz, alternatingWord]
      · rw [hflip 0 (by omega)]
        rfl
    have hlen : d.tits.wordLength (alternatingWord d (t 1) n) ≤
        d.tits.wordLength (d.simple (if t 0 then 1 else 0) * alternatingWord d (t 1) n) := by
      rw [hindex, wordLength_alternatingWord d _ hn,
        wordLength_alternatingWord d _ (by omega : n ≤ rotationOrder d)]
      omega
    rw [← hindex]
    apply d.tits.bruhatCell_mul_bruhatCell_subset_of_wordLength_le (d.simple_mem _) _ hlen
    refine ⟨(g 0)⁻¹ * g 1, hstep 0 (by omega), (g 1)⁻¹ * g (n + 1), htail, ?_⟩
    simp only [mul_assoc, mul_inv_cancel_left]

private theorem inv_mem_cell (w : Weyl d) {x : X ⧸ d.D}
    (hx : x ∈ d.tits.bruhatCell w) : x⁻¹ ∈ d.tits.bruhatCell w⁻¹ := by
  obtain ⟨y, hy, b₂, hb₂, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨b₁, hb₁, n, ⟨nN, hnw, rfl⟩, rfl⟩ := Set.mem_mul.mp hy
  refine ⟨(b₂⁻¹ * (nN⁻¹ : d.tits.N) : X ⧸ d.D), ?_, b₁⁻¹, d.tits.B.inv_mem hb₁, ?_⟩
  · exact ⟨b₂⁻¹, d.tits.B.inv_mem hb₂, (nN⁻¹ : d.tits.N),
      ⟨nN⁻¹, by rw [map_inv, hnw], rfl⟩, rfl⟩
  · simp only [mul_inv_rev, Subgroup.coe_inv, mul_assoc]

/-- Three reduced transitions cannot close with one simple transition. -/
theorem commonNeighbor_unique (hm : rotationOrder d = 3)
    {x y u v : Vertex (family d)} (hxy : x ≠ y)
    (hxu : (graph (family d)).Adj x u) (hyu : (graph (family d)).Adj y u)
    (hxv : (graph (family d)).Adj x v) (hyv : (graph (family d)).Adj y v) : u = v := by
  by_contra huv
  obtain ⟨a,hax,hau⟩ := incident_common_translate (family d) hxu.2
  obtain ⟨b,hbu,hby⟩ := incident_common_translate (family d) hyu.symm.2
  obtain ⟨c,hcy,hcv⟩ := incident_common_translate (family d) hyv.2
  obtain ⟨e,hev,hex⟩ := incident_common_translate (family d) hxv.symm.2
  have h0 := transition_cell d hxu hyu.symm hxy a b hax hau hbu hby
  have h1 := transition_cell d hyu.symm hyv huv b c hbu hby hcy hcv
  have h2 := transition_cell d hyv hxv.symm hxy.symm c e hcy hcv hev hex
  have h3 := transition_cell d hxv.symm hxu (Ne.symm huv) e a hev hex hax hau
  let g : ℕ → X ⧸ d.D := fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else e
  let t : ℕ → Bool := fun i => if i = 0 then u.type else if i = 1 then y.type else v.type
  have hc := short_gallery_cell d g t (n := 3) (by omega) (by
    intro i hi
    interval_cases i <;> simpa [g,t] using (by assumption)) (by
    intro i hi
    have hi2 : i ≤ 1 := by omega
    interval_cases i
    · simpa [t] using flip_type d hyu.symm
    · simpa [t] using flip_type d hyv)
  change a⁻¹ * e ∈ d.tits.bruhatCell (alternatingWord d u.type 3) at hc
  have hi := inv_mem_cell d _ h3
  simp only [mul_inv_rev, inv_inv] at hi
  have he := d.tits.doubleCoset_index_unique hc hi
  have hlen := wordLength_alternatingWord d u.type (by omega : 3 ≤ rotationOrder d)
  rw [he, wordLength_inv d, d.tits.wordLength_mem_S (d.simple_mem _)] at hlen
  omega

/-- Short-geodesic uniqueness follows from the BN axioms and m=3. -/
theorem uniqueGeodesicsBelow (hm : rotationOrder d = 3) :
    (graph (family d)).UniqueGeodesicsBelow 3 := by
  intro x y p q hp hq hshort
  by_cases hsmall : (graph (family d)).dist x y ≤ 1
  · exact SimpleGraph.Walk.eq_of_length_le_one (by omega) (by omega)
  have htwo : (graph (family d)).dist x y = 2 := by omega
  have hxy : x ≠ y := by intro he; subst y; simp at htwo
  rw [htwo] at hp hq
  cases p with
  | nil => simp at hp
  | @cons x u y hxu p =>
    cases p with
    | nil => simp at hp
    | @cons u z y huz p =>
      have hz : z = y := p.eq_of_length_eq_zero (by simp only [SimpleGraph.Walk.length_cons] at hp; omega)
      subst z
      have hp0 : p = .nil := SimpleGraph.Walk.eq_of_length_le_one (by simp only [SimpleGraph.Walk.length_cons] at hp; omega) (by simp)
      subst p
      cases q with
      | nil => simp at hq
      | @cons x v y hxv q =>
        cases q with
        | nil => simp at hq
        | @cons v z y hvz q =>
          have hz : z = y := q.eq_of_length_eq_zero (by simp only [SimpleGraph.Walk.length_cons] at hq; omega)
          subst z
          have hq0 : q = .nil := SimpleGraph.Walk.eq_of_length_le_one (by simp only [SimpleGraph.Walk.length_cons] at hq; omega) (by simp)
          subst q
          have huv := commonNeighbor_unique d hm hxy hxu huz.symm hxv hvz.symm
          subst v
          rfl

private def liftedWord : Bool → ℕ → d.tits.N
  | _, 0 => 1
  | b, n+1 => representative (d.simple (if b then 1 else 0)) * liftedWord (!b) n

private theorem liftedWord_spec (b : Bool) (n : ℕ) :
    QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) (liftedWord d b n) =
      alternatingWord d b n := by
  induction n generalizing b with
  | zero => simp [liftedWord, alternatingWord]
  | succ n ih => simp only [liftedWord, map_mul, representative_spec, alternatingWord, ih]

private theorem same_class_same_vertex (n m : d.tits.N) (b : Bool)
    (he : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n =
      QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) m) :
    (n : X ⧸ d.D) • base (family d) b = (m : X ⧸ d.D) • base (family d) b := by
  apply (DihedralGeometry.smul_base_eq_iff (family d) _ _ b).mpr
  have hmem := QuotientGroup.eq.mp he
  exact borel_le d b hmem.1

private theorem base_walk (i j : Bool) :
    ∃ p : (graph (family d)).Walk (base (family d) i) (base (family d) j), p.length ≤ 1 := by
  by_cases hij : i = j
  · subst j
    exact ⟨.nil, by simp⟩
  · have ha : (graph (family d)).Adj (base (family d) i) (base (family d) j) :=
      ⟨hij,CosetGeometry.incident_base _ i j⟩
    exact ⟨.cons ha .nil, by simp⟩

private theorem liftedWord_walk (b j : Bool) {n : ℕ} (hn : 0 < n) :
    ∃ p : (graph (family d)).Walk (base (family d) b)
      ((liftedWord d b n : X ⧸ d.D) • base (family d) j), p.length ≤ n := by
  have hfix (b : Bool) : (representative (d.simple (if b then 1 else 0)) : X ⧸ d.D) •
      base (family d) b = base (family d) b := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [CosetGeometry.stabilizer_base]
    apply (mem_parabolic d b _).mpr
    exact Or.inr (d.tits.representative_mem_bruhatCell _ _ (representative_spec _))
  induction n generalizing b with
  | zero => omega
  | succ n ih =>
    let a : X ⧸ d.D := representative (d.simple (if b then 1 else 0))
    by_cases hz : n = 0
    · subst n
      obtain ⟨p,hp⟩ := base_walk d b j
      have hend : (CosetGeometry.translationGraphIso (family d) a).toHom (base (family d) j) =
          (liftedWord d b (0+1) : X ⧸ d.D) • base (family d) j := by
        simp only [liftedWord, mul_one]
        rfl
      have hstart : (CosetGeometry.translationGraphIso (family d) a).toHom (base (family d) b) = base (family d) b := hfix b
      exact ⟨(p.map (CosetGeometry.translationGraphIso (family d) a).toHom).copy hstart hend,
        by rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]; exact hp⟩
    · obtain ⟨p,hp⟩ := ih (!b) (by omega)
      let e : (graph (family d)).Walk (base (family d) b) (base (family d) (!b)) :=
        .cons ⟨by change b ≠ !b; cases b <;> decide, CosetGeometry.incident_base _ _ _⟩ .nil
      have hstart : (CosetGeometry.translationGraphIso (family d) a).toHom (base (family d) b) = base (family d) b := hfix b
      have hend : (CosetGeometry.translationGraphIso (family d) a).toHom
          ((liftedWord d (!b) n : X ⧸ d.D) • base (family d) j) =
          (liftedWord d b (n+1) : X ⧸ d.D) • base (family d) j := by
        simp only [liftedWord, Subgroup.coe_mul, mul_smul]
        rfl
      exact ⟨((e.append p).map (CosetGeometry.translationGraphIso (family d) a).toHom).copy
        hstart hend, by
          rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_append]
          change 1 + p.length ≤ n+1
          omega⟩

private theorem normalizer_walk (hm : rotationOrder d = 3) (i j : Bool) (n : d.tits.N) :
    ∃ p : (graph (family d)).Walk (base (family d) i)
      ((n : X ⧸ d.D) • base (family d) j), p.length ≤ 3 := by
  let w := QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n
  obtain ⟨b,k,hk,he⟩ := exists_alternatingWord d w
  by_cases hk3 : k = 3
  · have he' : alternatingWord d i 3 = w := by
      rw [← hm, alternatingWord_longest]
      rw [hk3, ← hm, alternatingWord_longest] at he
      exact he
    obtain ⟨p,hp⟩ := liftedWord_walk d i j (n := 3) (by omega)
    have hv := same_class_same_vertex d (liftedWord d i 3) n j
      ((liftedWord_spec d i 3).trans he')
    exact ⟨p.copy rfl hv, by simpa only [SimpleGraph.Walk.length_copy] using hp⟩
  · have hk2 : k ≤ 2 := by omega
    by_cases hk0 : k = 0
    · subst k
      have hv : (n : X ⧸ d.D) • base (family d) j = base (family d) j := by
        have hh := same_class_same_vertex d n 1 j (by simpa [alternatingWord,w] using he.symm)
        simpa only [Subgroup.coe_one, one_smul] using hh
      obtain ⟨p,hp⟩ := base_walk d i j
      exact ⟨p.copy rfl hv.symm, by simp only [SimpleGraph.Walk.length_copy]; omega⟩
    · obtain ⟨p,hp⟩ := liftedWord_walk d b j (n := k) (by omega)
      obtain ⟨q,hq⟩ := base_walk d i b
      have hv := same_class_same_vertex d (liftedWord d b k) n j
        ((liftedWord_spec d b k).trans he)
      exact ⟨(q.append p).copy rfl hv, by
        simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_append]; omega⟩

/-- Bruhat coverage and the three-step normalizer paths give the actual diameter bound. -/
theorem diameter_le_three (hm : rotationOrder d = 3) (v w : Vertex (family d)) :
    (graph (family d)).dist v w ≤ 3 := by
  obtain ⟨k,hv,hw⟩ := DihedralGeometry.exists_apartment_for_vertices (family d) d.tits
    (borel_le d) v w
  obtain ⟨v',hv',rfl⟩ := Set.mem_smul_set.mp hv
  obtain ⟨w',hw',rfl⟩ := Set.mem_smul_set.mp hw
  obtain ⟨n,hn,i,rfl⟩ := hv'
  obtain ⟨m,hmN,j,rfl⟩ := hw'
  let nN : d.tits.N := ⟨n,hn⟩
  let mN : d.tits.N := ⟨m,hmN⟩
  obtain ⟨p,hp⟩ := normalizer_walk d hm i j (nN⁻¹*mN)
  have hd := (graph (family d)).dist_le p
  have hd' : (graph (family d)).dist (n • base (family d) i) (m • base (family d) j) ≤ 3 := by
    rw [← dist_smul (family d) n] at hd
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, nN, mN, mul_smul, smul_inv_smul] using hd.trans hp
  simpa only [dist_smul] using hd'

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleGeometry
