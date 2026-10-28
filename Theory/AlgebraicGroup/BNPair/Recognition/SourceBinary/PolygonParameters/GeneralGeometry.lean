module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TriangleGeometry
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.Valence
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Metric

/-!
# The finite polygon at an unselected marked Weyl order

The actual two standard parabolics define a finite thick polygon whose
parameter is the order of the original ordered simple-reflection product.
A nonbacktracking closed gallery has at least twice that order: its first
m transitions lie in the longest Bruhat cell and its complementary gallery
must have length at least m. Alternating normalizer words and Bruhat coverage
bound the diameter by m. The valences are the actual two simple-root orders
plus one, with the complete Borel and endpoint orientation unchanged.

This constructs the geometric input to Feit--Higman for every m; it does
not assume or prove the restriction m = 2, 3, 4, 6, 8. In particular the
construction is independent of the selected hexagon and octagon metrics.
Source: Fong--Seitz I (1J), printed p.6; the finite BN-pair geometry in
DGS, Groups and Graphs (1985), Theorem D, printed p.224. The gallery and
normalizer arguments generalize the existing triangle and octagon proofs.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters.GeneralGeometry
open RootCoordinates Subgroup.CosetGeometry.RankTwo
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)

/-- The original endpoint order, expressed on the Boolean type set. -/
abbrev family := TriangleGeometry.family d

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

private theorem gallery_wordLength_le (g : ℕ → X ⧸ d.D) (t : ℕ → Bool) (n : ℕ)
    (hstep : ∀ k < n, (g k)⁻¹ * g (k + 1) ∈ d.tits.bruhatCell (d.simple (if t k then 1 else 0))) :
    ∃ w, (g 0)⁻¹ * g n ∈ d.tits.bruhatCell w ∧ d.tits.wordLength w ≤ n := by
  induction n generalizing g t with
  | zero => exact ⟨1, by simp [d.tits.bruhatCell_one], by rw [d.tits.wordLength_one]⟩
  | succ n ih =>
    obtain ⟨w, hw, hlen⟩ := ih (fun k => g (k + 1)) (fun k => t (k + 1))
      (fun k hk => hstep (k + 1) (by omega))
    have hprod : (g 0)⁻¹ * g (n + 1) ∈ d.tits.bruhatCell (d.simple (if t 0 then 1 else 0)) * d.tits.bruhatCell w := by
      refine ⟨(g 0)⁻¹ * g 1, hstep 0 (by omega), (g 1)⁻¹ * g (n + 1), hw, ?_⟩
      simp only [mul_assoc, mul_inv_cancel_left]
    rcases d.tits.doubleCoset_mul_doubleCoset_subset_of_mem_S (d.simple_mem _) w hprod with h | h
    · exact ⟨d.simple (if t 0 then 1 else 0) * w, h,
        (d.tits.wordLength_mul_left_le (d.simple_mem _) w).trans (Nat.add_le_add_right hlen 1)⟩
    · exact ⟨w, h, by omega⟩

private theorem closed_gallery_bound (g : ℕ → X ⧸ d.D) (t : ℕ → Bool)
    {n : ℕ} (hn : 0 < n) (hclosed : g n = g 0)
    (hstep : ∀ k < n, (g k)⁻¹ * g (k+1) ∈ d.tits.bruhatCell (d.simple (if t k then 1 else 0)))
    (hflip : ∀ k, k+1 < n → t (k+1) = !(t k)) :
    2 * rotationOrder d ≤ n := by
  by_cases hshort : n ≤ rotationOrder d
  · have hc := short_gallery_cell d g t hshort hstep hflip
    have hb : (g 0)⁻¹ * g n ∈ d.tits.bruhatCell 1 := by
      simp [hclosed, d.tits.bruhatCell_one]
    have he := d.tits.doubleCoset_index_unique hc hb
    have hl := wordLength_alternatingWord d (t 0) hshort
    rw [he, d.tits.wordLength_one] at hl
    omega
  · have hc := short_gallery_cell d g t (n := rotationOrder d) le_rfl
      (fun k hk => hstep k (by omega)) (fun k hk => hflip k (by omega))
    obtain ⟨w, hw, hl⟩ := gallery_wordLength_le d (fun k => g (k+rotationOrder d))
      (fun k => t (k+rotationOrder d)) (n-rotationOrder d) (fun k hk => by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hstep (k+rotationOrder d) (by omega))
    have hw' := inv_mem_cell d w hw
    have hi : alternatingWord d (t 0) (rotationOrder d) = w⁻¹ := by
      apply d.tits.doubleCoset_index_unique hc
      change (g 0)⁻¹ * g (rotationOrder d) ∈ d.tits.bruhatCell w⁻¹
      simpa only [Nat.zero_add, Nat.sub_add_cancel (by omega : rotationOrder d ≤ n),
        hclosed, mul_inv_rev, inv_inv] using hw'
    have he := wordLength_alternatingWord d (t 0) (n := rotationOrder d) le_rfl
    rw [hi, wordLength_inv] at he
    omega

/-- Every cycle has length at least twice the actual Weyl rotation order. -/
theorem cycle_bound (v : Vertex (family d)) (p : (graph (family d)).Walk v v)
    (hp : p.IsCycle) : 2 * rotationOrder d ≤ p.length := by
  classical
  have hn := hp.three_le_length
  have hrep : ∀ k : Fin p.length, ∃ g : X ⧸ d.D,
      g • base (family d) (p.getVert k).type = p.getVert k ∧
      g • base (family d) (p.getVert (k + 1)).type = p.getVert (k + 1) := by
    intro k
    exact incident_common_translate (family d) (p.adj_getVert_succ k.isLt).2
  choose r hr using hrep
  let g : ℕ → X ⧸ d.D := fun k => if hk : k < p.length then r ⟨k, hk⟩ else r ⟨0, by omega⟩
  have hg (k : ℕ) (hk : k < p.length) :
      g k • base (family d) (p.getVert k).type = p.getVert k ∧
      g k • base (family d) (p.getVert (k + 1)).type = p.getVert (k + 1) := by
    simpa only [g, dif_pos hk] using hr ⟨k, hk⟩
  have hclosed : g p.length = g 0 := by simp [g, show 0 < p.length by omega]
  apply closed_gallery_bound d g (fun k => (p.getVert (k + 1)).type) (by omega) hclosed
  · intro k hk
    by_cases hk' : k + 1 < p.length
    · apply transition_cell d (p.adj_getVert_succ hk) (p.adj_getVert_succ hk')
        (by simpa using hp.getVert_sub_one_ne_getVert_add_one (i := k + 1) (by omega))
        (g k) (g (k + 1)) (hg k hk).1 (hg k hk).2 (hg (k + 1) hk').1 (hg (k + 1) hk').2
    · have hklen : k + 1 = p.length := by omega
      have hne : p.getVert k ≠ p.getVert 1 := by
        intro he
        have := hp.getVert_injOn' (by change k ≤ p.length - 1; omega)
          (by change 1 ≤ p.length - 1; omega) he
        omega
      have hvw : (graph (family d)).Adj (p.getVert (k + 1)) (p.getVert 1) := by
        simpa only [hklen, SimpleGraph.Walk.getVert_length,
          SimpleGraph.Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
      apply transition_cell d (p.adj_getVert_succ hk) hvw hne (g k) (g (k + 1))
        (hg k hk).1 (hg k hk).2
      · simpa only [hklen, hclosed, SimpleGraph.Walk.getVert_length,
          SimpleGraph.Walk.getVert_zero] using (hg 0 (by omega)).1
      · simpa only [hklen, hclosed] using (hg 0 (by omega)).2
  · intro k hk
    exact flip_type d (p.adj_getVert_succ hk)

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

private theorem normalizer_walk (i j : Bool) (n : d.tits.N) :
    ∃ p : (graph (family d)).Walk (base (family d) i)
      ((n : X ⧸ d.D) • base (family d) j), p.length ≤ rotationOrder d := by
  let w := QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n
  obtain ⟨b,k,hk,he⟩ := exists_alternatingWord d w
  by_cases hk3 : k = rotationOrder d
  · have he' : alternatingWord d i (rotationOrder d) = w := by
      rw [alternatingWord_longest]
      rw [hk3, alternatingWord_longest] at he
      exact he
    obtain ⟨p,hp⟩ := liftedWord_walk d i j (n := rotationOrder d) (by have := rotationOrder_ge_two d; omega)
    have hv := same_class_same_vertex d (liftedWord d i (rotationOrder d)) n j
      ((liftedWord_spec d i (rotationOrder d)).trans he')
    exact ⟨p.copy rfl hv, by simpa only [SimpleGraph.Walk.length_copy] using hp⟩
  · have hk2 : k < rotationOrder d := by omega
    by_cases hk0 : k = 0
    · subst k
      have hv : (n : X ⧸ d.D) • base (family d) j = base (family d) j := by
        have hh := same_class_same_vertex d n 1 j (by simpa [alternatingWord,w] using he.symm)
        simpa only [Subgroup.coe_one, one_smul] using hh
      obtain ⟨p,hp⟩ := base_walk d i j
      exact ⟨p.copy rfl hv.symm, by simp only [SimpleGraph.Walk.length_copy]; have := rotationOrder_ge_two d; omega⟩
    · obtain ⟨p,hp⟩ := liftedWord_walk d b j (n := k) (by omega)
      obtain ⟨q,hq⟩ := base_walk d i b
      have hv := same_class_same_vertex d (liftedWord d b k) n j
        ((liftedWord_spec d b k).trans he)
      exact ⟨(q.append p).copy rfl hv, by
        simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_append]; omega⟩

/-- Any two vertices are joined by a walk no longer than the actual rotation order. -/
theorem bounded_walk (v w : Vertex (family d)) :
    ∃ p : (graph (family d)).Walk v w, p.length ≤ rotationOrder d := by
  obtain ⟨k,hv,hw⟩ := DihedralGeometry.exists_apartment_for_vertices (family d) d.tits
    (borel_le d) v w
  obtain ⟨v',hv',rfl⟩ := Set.mem_smul_set.mp hv
  obtain ⟨w',hw',rfl⟩ := Set.mem_smul_set.mp hw
  obtain ⟨n,hn,i,rfl⟩ := hv'
  obtain ⟨m,hmN,j,rfl⟩ := hw'
  let nN : d.tits.N := ⟨n,hn⟩
  let mN : d.tits.N := ⟨m,hmN⟩
  obtain ⟨p,hp⟩ := normalizer_walk d i j (nN⁻¹*mN)
  let f := CosetGeometry.translationGraphIso (family d) (k*n)
  have hs : f (base (family d) i) = k • n • base (family d) i := by
    simp [f, mul_smul]
  have ht : f (((nN⁻¹*mN : d.tits.N) : X ⧸ d.D) • base (family d) j) =
      k • m • base (family d) j := by
    simp [f, nN, mN, mul_smul]
  exact ⟨(p.map f.toHom).copy hs ht, by
    simpa only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map] using hp⟩

/-- The actual parabolic graph is connected, for every rotation order. -/
theorem connected : (graph (family d)).Connected := by
  let : Nonempty (Vertex (family d)) := ⟨base (family d) false⟩
  refine { preconnected := ?_ }
  intro v w
  obtain ⟨p,_⟩ := bounded_walk d v w
  exact ⟨p⟩

/-- Bruhat coverage bounds the diameter without selecting a Lie row. -/
theorem diameter (v w : Vertex (family d)) :
    (graph (family d)).dist v w ≤ rotationOrder d := by
  obtain ⟨p,hp⟩ := bounded_walk d v w
  exact ((graph _).dist_le p).trans hp

/-- Valence at the literal original type, including both binary panels. -/
theorem neighbor_card (split : SplitData d.tits) (v : Vertex (family d)) :
    Nat.card ((graph (family d)).neighborSet v) =
      1 + Nat.card (simpleRoot d split (if v.type then 1 else 0)) := by
  obtain ⟨g,hg⟩ := CosetGeometry.exists_smul_base (family d) v
  have he := Nat.card_congr ((CosetGeometry.translationGraphIso (family d) g).mapNeighborSet
    (base (family d) v.type))
  change Nat.card ((graph _).neighborSet _) = Nat.card ((graph _).neighborSet (g • _)) at he
  rw [hg] at he
  rw [←he, card_neighbor_base]
  have hI : family d v.type ⊓ family d (!v.type) = d.tits.B := by
    cases v.type
    · exact d.standard_intersection
    · exact (inf_comm _ _).trans d.standard_intersection
  have hsub : (family d (!v.type)).subgroupOf (family d v.type) =
      d.tits.B.subgroupOf (family d v.type) := by
    ext x
    change (x : X ⧸ d.D) ∈ family d (!v.type) ↔ (x : X ⧸ d.D) ∈ d.tits.B
    rw [←hI]
    exact ⟨fun h => ⟨x.property,h⟩, fun h => h.2⟩
  rw [hsub]
  exact singleton_parabolic_root_index d split (if v.type then 1 else 0)

noncomputable instance vertexFintype : Fintype (Vertex (family d)) := Fintype.ofFinite _

/-- Its colors are the two original ordered endpoint types. -/
def color (v : Vertex (family d)) : ZMod 2 := if v.type then 1 else 0

private theorem color_adj {v w : Vertex (family d)} (h : (graph (family d)).Adj v w) :
    color d v + 1 = color d w := by
  have ht := flip_type d h
  simp only [color, ht]
  cases v.type <;> decide

/-- The metric datum used by Feit--Higman, at the actual unselected Weyl order. -/
def metricDatum (split : SplitData d.tits) :
    SimpleGraph.PolygonParameters.Datum (graph (family d)) (rotationOrder d)
      (Nat.card (simpleRoot d split 1)) (Nat.card (simpleRoot d split 0)) where
  color := color d
  color_adj := fun {_ _} h => color_adj d h
  connected := connected d
  cycle_bound := cycle_bound d
  diameter := diameter d
  valence := by
    classical
    intro v
    have hc : SimpleGraph.OctagonShortPaths.neighborCard (graph (family d)) v =
        Nat.card ((graph (family d)).neighborSet v) := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_ofFinset _ (by intro w; simp)).symm
    rw [hc, neighbor_card d split]
    cases hv : v.type <;> norm_num [color, hv, Nat.add_comm]

/-- Thickness is proved from the actual simple roots, with no field restriction. -/
theorem metricDatum_thick (split : SplitData d.tits) :
    1 < Nat.card (simpleRoot d split 1) ∧ 1 < Nat.card (simpleRoot d split 0) :=
  ⟨simpleRoot_card_gt_one d split 1, simpleRoot_card_gt_one d split 0⟩

/-- The distinguished first endpoint supplies a point of the polygon. -/
theorem metricDatum_point (split : SplitData d.tits) :
    ∃ v, (metricDatum d split).color v = 0 :=
  ⟨base (family d) false, rfl⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters.GeneralGeometry
