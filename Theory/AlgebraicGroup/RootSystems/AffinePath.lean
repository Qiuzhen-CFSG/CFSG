module

public import Theory.AlgebraicGroup.RootSystems.Defs
public import Theory.AlgebraicGroup.RootSystems.GraphDegree

namespace Theory.AlgebraicGroup

/-- A five-vertex path with one internal double bond and all other bonds
simple cannot occur in a diagonally symmetrized positive-definite Cartan
matrix.  The displayed matrix has kernel vector `(u, 2u, 3u, -4, -2)` when
the opposite middle entries have product two. -/
public lemma not_cartan_five_path_internal_heavy_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (e : Fin 5 ↪ κ) (u v : ℤ)
    (hA : ∀ i j, A (e i) (e j) =
      if i = j then 2 else if
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
        (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) then -1 else if
        (i = 2 ∧ j = 3) then u else if
        (i = 3 ∧ j = 2) then v else 0)
    (huv : u * v = 2) : False := by
  have hsub :
      (Matrix.diagonal (d ∘ e) * A.submatrix e e).PosDef :=
    diagonal_mul_submatrix_posDef A d e hpos
  let x : Fin 5 → ℤ := ![u, 2 * u, 3 * u, -4, -2]
  have hx : x ≠ 0 := by
    intro h
    have h3 := congrFun h 3
    have hx3 : x 3 = -4 := by rfl
    rw [hx3] at h3
    norm_num at h3
  have hker : (A.submatrix e e).mulVec x = 0 := by
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Matrix.submatrix, hA, x,
        Fin.sum_univ_succ] <;>
      nlinarith
  exact not_diagonal_mul_posDef_of_nonzero_mulVec_eq_zero
    (A.submatrix e e) (d ∘ e) x hx hker hsub

/-- Conditional affine-`D` obstruction for two branch vertices.

The tree decomposition supplies an embedding `e` of the finite affine-`D`
subtree (the center-to-center path together with the two off-path leaves at
each endpoint), and a nonzero integral vector `x` whose Cartan submatrix
annihilates it.  This core deliberately keeps that decomposition as an
ordinary premise; it introduces no conclusion-bearing structure. -/
public lemma not_cartan_two_degree_three_vertices_of_diagonal_mul_posDef
    {k : Type*} [Fintype k] [DecidableEq k]
    (A : Matrix k k ℤ) (d : k → ℤ)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {n : ℕ} (e : Fin n ↪ k) (x : Fin n → ℤ)
    (hx : x ≠ 0)
    (hker : (A.submatrix e e).mulVec x = 0) : False := by
  have hsub : (Matrix.diagonal (d ∘ e) * A.submatrix e e).PosDef :=
    diagonal_mul_submatrix_posDef A d e hpos
  exact (not_diagonal_mul_posDef_of_nonzero_mulVec_eq_zero
    (A.submatrix e e) (d ∘ e) x hx hker) hsub

open SimpleGraph

/-- A path-graph numbering can be oriented so that a specified vertex of
degree at most one is numbered zero.  Endpoint selection is proved directly
from the path adjacency relation and is not stored in auxiliary data. -/
public lemma simpleGraph_pathGraph_numbering_reorient_at_degree_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (e : Fin (n + 1) ≃ V)
    (hpath : ∀ i j, G.Adj (e i) (e j) ↔
      (pathGraph (n + 1)).Adj i j)
    (u : V) (hdeg : G.degree u ≤ 1) :
    ∃ e' : Fin (n + 1) ≃ V,
      e' 0 = u ∧
      ∀ i j, G.Adj (e' i) (e' j) ↔
        (pathGraph (n + 1)).Adj i j := by
  classical
  let k : Fin (n + 1) := e.symm u
  have hek : e k = u := e.apply_symm_apply u
  let f : pathGraph (n + 1) →g G :=
    { toFun := e
      map_rel' := fun {i j} hij => (hpath i j).2 hij }
  have hkdeg : (pathGraph (n + 1)).degree k ≤ 1 := by
    calc
      (pathGraph (n + 1)).degree k ≤ G.degree (f k) :=
        simpleGraph_degree_le_of_injective_hom
          (pathGraph (n + 1)) G f e.injective k
      _ = G.degree u := by rw [show f k = u by exact hek]
      _ ≤ 1 := hdeg
  have hkend : k = 0 ∨ k = Fin.last n := by
    by_contra hk
    push Not at hk
    have hkpos : 0 < k.val := by
      by_contra h
      apply hk.1
      apply Fin.ext
      have hval : k.val = 0 := by omega
      exact hval
    have hklt : k.val < n := by
      by_contra h
      apply hk.2
      apply Fin.ext
      have hval : k.val = n := by omega
      exact hval
    let a : Fin (n + 1) := ⟨k.val - 1, by omega⟩
    let b : Fin (n + 1) := ⟨k.val + 1, by omega⟩
    have ha : (pathGraph (n + 1)).Adj k a := by
      rw [pathGraph_adj]
      right
      dsimp [a]
      omega
    have hb : (pathGraph (n + 1)).Adj k b := by
      rw [pathGraph_adj]
      left
      dsimp [b]
    have hab : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [a, b] at hv
      omega
    let two : Fin 2 → (pathGraph (n + 1)).neighborSet k := fun i =>
      if i = 0 then ⟨a, ha⟩ else ⟨b, hb⟩
    have htwo : Function.Injective two := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        apply hab
        exact congrArg Subtype.val hij
      · exfalso
        apply hab
        exact (congrArg Subtype.val hij).symm
      · rfl
    have htwoCard : 2 ≤ (pathGraph (n + 1)).degree k := by
      simpa only [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree] using
        (Fintype.card_le_of_injective two htwo)
    omega
  rcases hkend with hk0 | hklast
  · refine ⟨e, ?_, hpath⟩
    rw [← hek, hk0]
  · let e' : Fin (n + 1) ≃ V := (Fin.revPerm (n := n + 1)).trans e
    refine ⟨e', ?_, ?_⟩
    · change e (Fin.rev (0 : Fin (n + 1))) = u
      simpa [Fin.rev_zero, ← hklast] using hek
    · intro i j
      change G.Adj (e (Fin.rev i)) (e (Fin.rev j)) ↔ _
      rw [hpath, pathGraph_adj, pathGraph_adj]
      simp only [Fin.val_rev]
      omega

open SimpleGraph

/-- Deleting a vertex adjacent to `a` removes exactly that one neighbor from
the degree of `a`. -/
public lemma simpleGraph_induce_compl_singleton_degree_add_one_eq_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {c a : V} (hca : G.Adj c a) :
    (G.induce {c}ᶜ).degree ⟨a, by simpa using hca.ne.symm⟩ + 1 =
      G.degree a := by
  classical
  let v : ({c}ᶜ : Set V) := ⟨a, by simpa using hca.ne.symm⟩
  have hmap := G.map_neighborFinset_induce v
  have hinter : G.neighborFinset a ∩ ({c}ᶜ : Set V).toFinset =
      (G.neighborFinset a).erase c := by
    ext x
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Set.mem_toFinset, Set.mem_compl_iff, Set.mem_singleton_iff,
      Finset.mem_erase]
    tauto
  have hc : c ∈ G.neighborFinset a := by
    simpa only [SimpleGraph.mem_neighborFinset] using hca.symm
  rw [← (G.induce {c}ᶜ).card_neighborFinset_eq_degree,
    ← G.card_neighborFinset_eq_degree]
  calc
    ((G.induce {c}ᶜ).neighborFinset v).card + 1 =
        (((G.induce {c}ᶜ).neighborFinset v).map
          (.subtype (· ∈ ({c}ᶜ : Set V)))).card + 1 := by simp
    _ = (G.neighborFinset a ∩ ({c}ᶜ : Set V).toFinset).card + 1 := by
      rw [hmap]
    _ = ((G.neighborFinset a).erase c).card + 1 := by rw [hinter]
    _ = (G.neighborFinset a).card := Finset.card_erase_add_one hc

open SimpleGraph

/-- The vertices of a simple path in an acyclic graph, numbered by their walk
indices, induce exactly the corresponding path graph. -/
public theorem simpleGraph_isAcyclic_path_pathGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) (hG : G.IsAcyclic) :
    ∀ i j : Fin (p.length + 1),
      G.Adj (p.getVert i.val) (p.getVert j.val) ↔
        (pathGraph (p.length + 1)).Adj i j := by
  intro i j
  rw [pathGraph_adj]
  constructor
  · intro hadj
    have hij : i ≠ j := by
      intro h
      subst j
      exact hadj.ne rfl
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · left
      by_contra hnot
      have hgap : i.val + 1 < j.val := by omega
      exact simpleGraph_isAcyclic_path_nonadjacent hp hG hgap hadj
    · right
      by_contra hnot
      have hgap : j.val + 1 < i.val := by omega
      exact simpleGraph_isAcyclic_path_nonadjacent hp hG hgap hadj.symm
  · intro hadj
    rcases hadj with hij | hji
    · have hbound : i.val < p.length := by omega
      simpa [hij] using p.adj_getVert_succ hbound
    · have hbound : j.val < p.length := by omega
      simpa [hji] using (p.adj_getVert_succ hbound).symm

open SimpleGraph

/-- Removing the initial vertex from a nonempty simple path in an acyclic
graph leaves an exactly numbered path graph. -/
public theorem simpleGraph_isAcyclic_path_tail_pathGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) (hG : G.IsAcyclic) :
    ∀ i j : Fin p.length,
      G.Adj (p.getVert (i.val + 1)) (p.getVert (j.val + 1)) ↔
        (pathGraph p.length).Adj i j := by
  intro i j
  rw [pathGraph_adj]
  constructor
  · intro hadj
    have hij : i ≠ j := by
      intro h
      subst j
      exact hadj.ne rfl
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · left
      by_contra hnot
      have hgap : i.val + 1 < j.val := by omega
      let i' : Fin (p.length + 1) := ⟨i.val + 1, by omega⟩
      let j' : Fin (p.length + 1) := ⟨j.val + 1, by omega⟩
      exact simpleGraph_isAcyclic_path_nonadjacent hp hG
        (i := i') (j := j') (by simp [i', j']; omega) hadj
    · right
      by_contra hnot
      have hgap : j.val + 1 < i.val := by omega
      let i' : Fin (p.length + 1) := ⟨j.val + 1, by omega⟩
      let j' : Fin (p.length + 1) := ⟨i.val + 1, by omega⟩
      exact simpleGraph_isAcyclic_path_nonadjacent hp hG
        (i := i') (j := j') (by simp [i', j']; omega) hadj.symm
  · intro hadj
    rcases hadj with hij | hji
    · have hbound : i.val + 1 < p.length := by omega
      have h := p.adj_getVert_succ hbound
      simpa [hij] using h
    · have hbound : j.val + 1 < p.length := by omega
      have h := p.adj_getVert_succ hbound
      simpa [hji] using h.symm

open SimpleGraph

/-- A simple path in an acyclic graph, together with two off-path neighbors at
each endpoint, induces the displayed affine-`D` support. -/
public theorem simpleGraph_central_path_plus_four_offpath_support
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hpNil : ¬p.Nil)
    (hG : G.IsAcyclic) {a₁ a₂ b₁ b₂ : V}
    (ha₁₂ : a₁ ≠ a₂) (hb₁₂ : b₁ ≠ b₂)
    (hab₁ : a₁ ≠ b₁) (hab₂ : a₁ ≠ b₂)
    (ha₂b₁ : a₂ ≠ b₁) (ha₂b₂ : a₂ ≠ b₂)
    (ha₁adj : G.Adj u a₁) (ha₂adj : G.Adj u a₂)
    (hb₁adj : G.Adj v b₁) (hb₂adj : G.Adj v b₂)
    (ha₁off : a₁ ∉ p.support) (ha₂off : a₂ ∉ p.support)
    (hb₁off : b₁ ∉ p.support) (hb₂off : b₂ ∉ p.support)
    (e : Fin (p.length + 5) ↪ V)
    (hepath : ∀ i : Fin (p.length + 1),
      e ⟨i.val, by omega⟩ = p.getVert i.val)
    (hea₁ : e ⟨p.length + 1, by omega⟩ = a₁)
    (hea₂ : e ⟨p.length + 2, by omega⟩ = a₂)
    (heb₁ : e ⟨p.length + 3, by omega⟩ = b₁)
    (heb₂ : e ⟨p.length + 4, by omega⟩ = b₂) :
    ∀ i j : Fin (p.length + 5), G.Adj (e i) (e j) ↔
      (i.val + 1 = j.val ∧ j.val ≤ p.length) ∨
      (j.val + 1 = i.val ∧ i.val ≤ p.length) ∨
      (i.val = 0 ∧ j.val = p.length + 1) ∨
      (i.val = p.length + 1 ∧ j.val = 0) ∨
      (i.val = 0 ∧ j.val = p.length + 2) ∨
      (i.val = p.length + 2 ∧ j.val = 0) ∨
      (i.val = p.length ∧ j.val = p.length + 3) ∨
      (i.val = p.length + 3 ∧ j.val = p.length) ∨
      (i.val = p.length ∧ j.val = p.length + 4) ∨
      (i.val = p.length + 4 ∧ j.val = p.length) := by
  have hm : 0 < p.length := Walk.not_nil_iff_lt_length.mp hpNil
  have hePathVal : ∀ (i : Fin (p.length + 5)), i.val ≤ p.length →
      e i = p.getVert i.val := by
    intro i hi
    have h := hepath ⟨i.val, by omega⟩
    simpa using h
  have hstartLeaf : ∀ {a : V}, G.Adj u a → a ∉ p.support →
      ∀ (i : Fin (p.length + 1)), i ≠ 0 → ¬ G.Adj (p.getVert i.val) a := by
    intro a ha haoff i hi
    have hnot := simpleGraph_isAcyclic_path_offpath_start_nonadjacent
      hp hpNil hG ha haoff hi
    simpa [G.adj_comm] using hnot
  have hendLeaf : ∀ {b : V}, G.Adj v b → b ∉ p.support →
      ∀ (i : Fin (p.length + 1)), i.val ≠ p.length →
        ¬ G.Adj (p.getVert i.val) b := by
    intro b hb hboff i hi
    let r : Fin (p.reverse.length + 1) := ⟨p.length - i.val, by simp⟩
    have hr : r ≠ 0 := by
      intro hr0
      have hv := congrArg Fin.val hr0
      simp [r] at hv
      omega
    have hboffrev : b ∉ p.reverse.support := by
      simpa [p.support_reverse] using hboff
    have hnot := simpleGraph_isAcyclic_path_offpath_start_nonadjacent
      hp.reverse (by simpa using hpNil) hG hb hboffrev hr
    have hsub : p.length - (p.length - i.val) = i.val := Nat.sub_sub_self (by omega)
    simpa [r, Walk.getVert_reverse, hsub, G.adj_comm] using hnot
  have hsameEnd : ∀ {c a b : V}, G.Adj c a → G.Adj c b → a ≠ b →
      ¬ G.Adj a b := by
    intro c a b ha hb hab hadj
    let q : G.Walk a b := Walk.cons ha.symm (Walk.cons hb Walk.nil)
    have hqpath : q.IsPath := by
      apply (Walk.cons_isPath_iff _ _).2
      refine ⟨?_, ?_⟩
      · apply (Walk.cons_isPath_iff _ _).2
        exact ⟨Walk.IsPath.nil, by simpa using hb.ne⟩
      · intro hmem
        simp at hmem
        rcases hmem with hmem | hmem
        · exact ha.ne hmem.symm
        · exact hab hmem
    have hnot := simpleGraph_isAcyclic_path_nonadjacent hqpath hG
      (i := (0 : Fin (q.length + 1))) (j := ⟨2, by simp [q]⟩) (by simp [q])
    exact hnot (by simpa [q] using hadj)
  intro i j
  constructor
  · intro hij
    by_cases hi : i.val ≤ p.length
    · by_cases hj : j.val ≤ p.length
      · have hij' : G.Adj (p.getVert i.val) (p.getVert j.val) := by
          simpa [hePathVal i hi, hePathVal j hj] using hij
        have hine : i.val ≠ j.val := by
          intro heq
          exact G.irrefl (heq ▸ hij')
        rcases lt_or_gt_of_ne hine with hlt | hgt
        · by_cases hnext : i.val + 1 = j.val
          · exact Or.inl ⟨hnext, hj⟩
          · have hgap : i.val + 1 < j.val := by omega
            have hnot := simpleGraph_isAcyclic_path_nonadjacent hp hG
              (i := ⟨i.val, by omega⟩) (j := ⟨j.val, by omega⟩) hgap
            exact (hnot hij').elim
        · by_cases hnext : j.val + 1 = i.val
          · exact Or.inr (Or.inl ⟨hnext, hi⟩)
          · have hgap : j.val + 1 < i.val := by omega
            have hnot := simpleGraph_isAcyclic_path_nonadjacent hp hG
              (i := ⟨j.val, by omega⟩) (j := ⟨i.val, by omega⟩) hgap
            exact (hnot hij'.symm).elim
      · have hjcases : j.val = p.length + 1 ∨ j.val = p.length + 2 ∨
            j.val = p.length + 3 ∨ j.val = p.length + 4 := by omega
        rcases hjcases with hj1 | hj2 | hj3 | hj4
        · by_cases hi0 : i.val = 0
          · exact Or.inr (Or.inr (Or.inl ⟨hi0, hj1⟩))
          · have hnot := hstartLeaf ha₁adj ha₁off ⟨i.val, by omega⟩ (by
                intro h; exact hi0 (congrArg Fin.val h))
            have hj : j = ⟨p.length + 1, by omega⟩ := Fin.ext hj1
            exact (hnot (by simpa [hePathVal i hi, hj, hea₁] using hij)).elim
        · by_cases hi0 : i.val = 0
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi0, hj2⟩))))
          · have hnot := hstartLeaf ha₂adj ha₂off ⟨i.val, by omega⟩ (by
                intro h; exact hi0 (congrArg Fin.val h))
            have hj : j = ⟨p.length + 2, by omega⟩ := Fin.ext hj2
            exact (hnot (by simpa [hePathVal i hi, hj, hea₂] using hij)).elim
        · by_cases him : i.val = p.length
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨him, hj3⟩))))))
          · have hnot := hendLeaf hb₁adj hb₁off ⟨i.val, by omega⟩ him
            have hj : j = ⟨p.length + 3, by omega⟩ := Fin.ext hj3
            exact (hnot (by simpa [hePathVal i hi, hj, heb₁] using hij)).elim
        · by_cases him : i.val = p.length
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr (Or.inl ⟨him, hj4⟩))))))))
          · have hnot := hendLeaf hb₂adj hb₂off ⟨i.val, by omega⟩ him
            have hj : j = ⟨p.length + 4, by omega⟩ := Fin.ext hj4
            exact (hnot (by simpa [hePathVal i hi, hj, heb₂] using hij)).elim
    · by_cases hj : j.val ≤ p.length
      · have hsymm : G.Adj (e j) (e i) := (G.adj_comm _ _).mp hij
        have h := (show
          (j.val + 1 = i.val ∧ i.val ≤ p.length) ∨
          (i.val + 1 = j.val ∧ j.val ≤ p.length) ∨
          (j.val = 0 ∧ i.val = p.length + 1) ∨
          (j.val = p.length + 1 ∧ i.val = 0) ∨
          (j.val = 0 ∧ i.val = p.length + 2) ∨
          (j.val = p.length + 2 ∧ i.val = 0) ∨
          (j.val = p.length ∧ i.val = p.length + 3) ∨
          (j.val = p.length + 3 ∧ i.val = p.length) ∨
          (j.val = p.length ∧ i.val = p.length + 4) ∨
          (j.val = p.length + 4 ∧ i.val = p.length) from by
            -- Reuse the already proved path/leaf analysis with the vertices swapped.
            have ih := (show G.Adj (e j) (e i) from hsymm)
            clear hij hsymm
            -- The same arithmetic split is smaller after `j` is known to be on the path.
            have hicases : i.val = p.length + 1 ∨ i.val = p.length + 2 ∨
                i.val = p.length + 3 ∨ i.val = p.length + 4 := by omega
            rcases hicases with hi1 | hi2 | hi3 | hi4
            · by_cases hj0 : j.val = 0
              · exact Or.inr (Or.inr (Or.inl ⟨hj0, hi1⟩))
              · have hnot := hstartLeaf ha₁adj ha₁off ⟨j.val, by omega⟩ (by
                    intro h0; exact hj0 (congrArg Fin.val h0))
                have hi : i = ⟨p.length + 1, by omega⟩ := Fin.ext hi1
                exact (hnot (by simpa [hePathVal j hj, hi, hea₁] using ih)).elim
            · by_cases hj0 : j.val = 0
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hj0, hi2⟩))))
              · have hnot := hstartLeaf ha₂adj ha₂off ⟨j.val, by omega⟩ (by
                    intro h0; exact hj0 (congrArg Fin.val h0))
                have hi : i = ⟨p.length + 2, by omega⟩ := Fin.ext hi2
                exact (hnot (by simpa [hePathVal j hj, hi, hea₂] using ih)).elim
            · by_cases hjm : j.val = p.length
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inl ⟨hjm, hi3⟩))))))
              · have hnot := hendLeaf hb₁adj hb₁off ⟨j.val, by omega⟩ hjm
                have hi : i = ⟨p.length + 3, by omega⟩ := Fin.ext hi3
                exact (hnot (by simpa [hePathVal j hj, hi, heb₁] using ih)).elim
            · by_cases hjm : j.val = p.length
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inr (Or.inl ⟨hjm, hi4⟩))))))))
              · have hnot := hendLeaf hb₂adj hb₂off ⟨j.val, by omega⟩ hjm
                have hi : i = ⟨p.length + 4, by omega⟩ := Fin.ext hi4
                exact (hnot (by simpa [hePathVal j hj, hi, hea₂, heb₂] using ih)).elim)
        rcases h with h | h | h | h | h | h | h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))
        · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inl ⟨h.2, h.1⟩)))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))))))))
      · have hicases : i.val = p.length + 1 ∨ i.val = p.length + 2 ∨
            i.val = p.length + 3 ∨ i.val = p.length + 4 := by omega
        have hjcases : j.val = p.length + 1 ∨ j.val = p.length + 2 ∨
            j.val = p.length + 3 ∨ j.val = p.length + 4 := by omega
        rcases hicases with hi1 | hi2 | hi3 | hi4
        · rcases hjcases with hj1 | hj2 | hj3 | hj4
          · have hi' : i = ⟨p.length + 1, by omega⟩ := Fin.ext hi1
            have hj' : j = ⟨p.length + 1, by omega⟩ := Fin.ext hj1
            simp [hi', hj', hea₁] at hij
          · have hi' : i = ⟨p.length + 1, by omega⟩ := Fin.ext hi1
            have hj' : j = ⟨p.length + 2, by omega⟩ := Fin.ext hj2
            exact (hsameEnd ha₁adj ha₂adj ha₁₂ (by simpa [hi', hj', hea₁, hea₂] using hij)).elim
          · have hi' : i = ⟨p.length + 1, by omega⟩ := Fin.ext hi1
            have hj' : j = ⟨p.length + 3, by omega⟩ := Fin.ext hj3
            exact (simpleGraph_isAcyclic_path_cross_offpath_nonadjacent hp hpNil hG ha₁adj hb₁adj ha₁off hb₁off hab₁ (by simpa [hi', hj', hea₁, heb₁] using hij)).elim
          · have hi' : i = ⟨p.length + 1, by omega⟩ := Fin.ext hi1
            have hj' : j = ⟨p.length + 4, by omega⟩ := Fin.ext hj4
            exact (simpleGraph_isAcyclic_path_cross_offpath_nonadjacent hp hpNil hG ha₁adj hb₂adj ha₁off hb₂off hab₂ (by simpa [hi', hj', hea₁, heb₂] using hij)).elim
        · rcases hjcases with hj1 | hj2 | hj3 | hj4
          · have hi' : i = ⟨p.length + 2, by omega⟩ := Fin.ext hi2
            have hj' : j = ⟨p.length + 1, by omega⟩ := Fin.ext hj1
            exact (hsameEnd ha₁adj ha₂adj ha₁₂ (by simpa [G.adj_comm, hi', hj', hea₁, hea₂] using hij)).elim
          · have hi' : i = ⟨p.length + 2, by omega⟩ := Fin.ext hi2
            have hj' : j = ⟨p.length + 2, by omega⟩ := Fin.ext hj2
            simp [hi', hj', hea₂] at hij
          · have hi' : i = ⟨p.length + 2, by omega⟩ := Fin.ext hi2
            have hj' : j = ⟨p.length + 3, by omega⟩ := Fin.ext hj3
            exact (simpleGraph_isAcyclic_path_cross_offpath_nonadjacent hp hpNil hG ha₂adj hb₁adj ha₂off hb₁off ha₂b₁ (by simpa [hi', hj', hea₂, heb₁] using hij)).elim
          · have hi' : i = ⟨p.length + 2, by omega⟩ := Fin.ext hi2
            have hj' : j = ⟨p.length + 4, by omega⟩ := Fin.ext hj4
            exact (simpleGraph_isAcyclic_path_cross_offpath_nonadjacent hp hpNil hG ha₂adj hb₂adj ha₂off hb₂off ha₂b₂ (by simpa [hi', hj', hea₂, heb₂] using hij)).elim
        · rcases hjcases with hj1 | hj2 | hj3 | hj4
          · have hi' : i = ⟨p.length + 3, by omega⟩ := Fin.ext hi3
            have hj' : j = ⟨p.length + 1, by omega⟩ := Fin.ext hj1
            exact (simpleGraph_isAcyclic_path_cross_offpath_nonadjacent hp hpNil hG ha₁adj hb₁adj ha₁off hb₁off hab₁ (by simpa [G.adj_comm, hi', hj', hea₁, heb₁] using hij)).elim
          · have hi' : i = ⟨p.length + 3, by omega⟩ := Fin.ext hi3
            have hj' : j = ⟨p.length + 2, by omega⟩ := Fin.ext hj2
            exact (simpleGraph_isAcyclic_path_cross_offpath_nonadjacent hp hpNil hG ha₂adj hb₁adj ha₂off hb₁off ha₂b₁ (by simpa [G.adj_comm, hi', hj', hea₂, heb₁] using hij)).elim
          · have hi' : i = ⟨p.length + 3, by omega⟩ := Fin.ext hi3
            have hj' : j = ⟨p.length + 3, by omega⟩ := Fin.ext hj3
            simp [hi', hj', heb₁] at hij
          · have hi' : i = ⟨p.length + 3, by omega⟩ := Fin.ext hi3
            have hj' : j = ⟨p.length + 4, by omega⟩ := Fin.ext hj4
            exact (hsameEnd hb₁adj hb₂adj hb₁₂ (by simpa [hi', hj', heb₁, heb₂] using hij)).elim
        · rcases hjcases with hj1 | hj2 | hj3 | hj4
          · have hi' : i = ⟨p.length + 4, by omega⟩ := Fin.ext hi4
            have hj' : j = ⟨p.length + 1, by omega⟩ := Fin.ext hj1
            exact (simpleGraph_isAcyclic_path_cross_offpath_nonadjacent hp hpNil hG ha₁adj hb₂adj ha₁off hb₂off hab₂ (by simpa [G.adj_comm, hi', hj', hea₁, heb₂] using hij)).elim
          · have hi' : i = ⟨p.length + 4, by omega⟩ := Fin.ext hi4
            have hj' : j = ⟨p.length + 2, by omega⟩ := Fin.ext hj2
            exact (simpleGraph_isAcyclic_path_cross_offpath_nonadjacent hp hpNil hG ha₂adj hb₂adj ha₂off hb₂off ha₂b₂ (by simpa [G.adj_comm, hi', hj', hea₂, heb₂] using hij)).elim
          · have hi' : i = ⟨p.length + 4, by omega⟩ := Fin.ext hi4
            have hj' : j = ⟨p.length + 3, by omega⟩ := Fin.ext hj3
            exact (hsameEnd hb₁adj hb₂adj hb₁₂ (by simpa [G.adj_comm, hi', hj', heb₁, heb₂] using hij)).elim
          · have hi' : i = ⟨p.length + 4, by omega⟩ := Fin.ext hi4
            have hj' : j = ⟨p.length + 4, by omega⟩ := Fin.ext hj4
            simp [hi', hj', heb₂] at hij
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h
    · have hadj := p.adj_getVert_succ (i := i.val) (by omega)
      simpa [hePathVal i (by omega), hePathVal j (by omega), h.1] using hadj
    · have hadj := p.adj_getVert_succ (i := j.val) (by omega)
      simpa [hePathVal i (by omega), hePathVal j (by omega), h.1, G.adj_comm] using hadj
    · have hi : i = 0 := Fin.ext h.1
      have hj : j = ⟨p.length + 1, by omega⟩ := Fin.ext h.2
      simpa [hi, hj, hePathVal 0 (by omega), hea₁] using ha₁adj
    · have hi : i = ⟨p.length + 1, by omega⟩ := Fin.ext h.1
      have hj : j = 0 := Fin.ext h.2
      simpa [hi, hj, hePathVal 0 (by omega), hea₁, G.adj_comm] using ha₁adj
    · have hi : i = 0 := Fin.ext h.1
      have hj : j = ⟨p.length + 2, by omega⟩ := Fin.ext h.2
      simpa [hi, hj, hePathVal 0 (by omega), hea₂] using ha₂adj
    · have hi : i = ⟨p.length + 2, by omega⟩ := Fin.ext h.1
      have hj : j = 0 := Fin.ext h.2
      simpa [hi, hj, hePathVal 0 (by omega), hea₂, G.adj_comm] using ha₂adj
    · have hi : i = ⟨p.length, by omega⟩ := Fin.ext h.1
      have hj : j = ⟨p.length + 3, by omega⟩ := Fin.ext h.2
      simpa [hi, hj, hePathVal ⟨p.length, by omega⟩ (by omega), heb₁] using hb₁adj
    · have hi : i = ⟨p.length + 3, by omega⟩ := Fin.ext h.1
      have hj : j = ⟨p.length, by omega⟩ := Fin.ext h.2
      simpa [hi, hj, hePathVal ⟨p.length, by omega⟩ (by omega), heb₁,
        G.adj_comm] using hb₁adj
    · have hi : i = ⟨p.length, by omega⟩ := Fin.ext h.1
      have hj : j = ⟨p.length + 4, by omega⟩ := Fin.ext h.2
      simpa [hi, hj, hePathVal ⟨p.length, by omega⟩ (by omega), heb₂] using hb₂adj
    · have hi : i = ⟨p.length + 4, by omega⟩ := Fin.ext h.1
      have hj : j = ⟨p.length, by omega⟩ := Fin.ext h.2
      simpa [hi, hj, hePathVal ⟨p.length, by omega⟩ (by omega), heb₂,
        G.adj_comm] using hb₂adj

open SimpleGraph

/-- An off-path neighbor of the initial vertex of a nonempty simple path is
adjacent to exactly the initial path vertex. -/
public theorem simpleGraph_isAcyclic_path_offpath_start_adj_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v a : V} {p : G.Walk u v} (hp : p.IsPath) (hpNil : ¬p.Nil)
    (hG : G.IsAcyclic) (ha : G.Adj u a) (haoff : a ∉ p.support) :
    ∀ j : Fin (p.length + 1), G.Adj a (p.getVert j) ↔ j = 0 := by
  intro j
  constructor
  · intro haj
    by_contra hj
    exact simpleGraph_isAcyclic_path_offpath_start_nonadjacent
      hp hpNil hG ha haoff hj haj
  · intro hj
    subst j
    simpa using ha.symm

open SimpleGraph

/-- Two distinct neighbors of a vertex cannot be adjacent in an acyclic
graph. -/
public theorem simpleGraph_isAcyclic_two_start_neighbors_nonadjacent
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsAcyclic) {u a b : V}
    (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b) :
    ¬ G.Adj a b := by
  let p := hb.toWalk
  have hp : p.IsPath := Walk.IsPath.of_adj hb
  have hpNil : ¬p.Nil := by simp [p]
  have haoff : a ∉ p.support := by
    simp [p, ha.ne.symm, hab]
  simpa [p] using
    (simpleGraph_isAcyclic_path_offpath_start_nonadjacent hp hpNil hG
      ha haoff (j := (1 : Fin (p.length + 1))) (by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        exact hpNil hv))

open SimpleGraph

/-- A finite tree of maximum degree at most two is isomorphic to a finite path
graph, expressed by an explicit numbering of its vertices. -/
public lemma simpleGraph_pathGraph_numbering_of_isTree_degree_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree)
    (hdegree : ∀ x, G.degree x ≤ 2) :
    ∃ n : ℕ, ∃ e : Fin n ≃ V,
      ∀ i j, G.Adj (e i) (e j) ↔ (pathGraph n).Adj i j := by
  obtain ⟨u, v, p, hp, hspan, hedge⟩ :=
    simpleGraph_spanningPath_of_isTree_degree_le_two G hG hdegree
  exact simpleGraph_spanningPath_numbering G u v p hp hspan hedge

open scoped SimpleGraph

/-- Deleting a degree-three vertex from a tree yields exactly the three
components determined by its three neighbors.  The conclusion exposes an
ordinary neighbor numbering and component cover, with no Dynkin data. -/
public theorem simpleGraph_tree_degree_three_deleted_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (c : V) (hdeg : G.degree c = 3) :
    ∃ a : Fin 3 → V, ∃ ha : ∀ i, G.Adj c (a i),
      Function.Injective a ∧
      Function.Injective (fun i =>
        (G.induce {c}ᶜ).connectedComponentMk
          ⟨a i, by simpa using (ha i).ne.symm⟩) ∧
      ∀ v : {v : V // v ≠ c}, ∃ i,
        (G.induce {c}ᶜ).connectedComponentMk
            ⟨v, by
              simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using v.property⟩ =
          (G.induce {c}ᶜ).connectedComponentMk
            ⟨a i, by simpa using (ha i).ne.symm⟩ := by
  obtain ⟨a0, a1, a2, h01, h02, h12, ha0, ha1, ha2, hall⟩ :=
    simpleGraph_degree_three_neighbors G c hdeg
  let a : Fin 3 → V := ![a0, a1, a2]
  have ha : ∀ i, G.Adj c (a i) := by
    intro i
    fin_cases i <;> simp [a, ha0, ha1, ha2]
  have hainj : Function.Injective a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [a]
  refine ⟨a, ha, hainj, ?_, ?_⟩
  · intro i j hij
    have hajc : a j ≠ c := (ha j).ne.symm
    obtain ⟨x, hx, hxreach, hxuniq⟩ :=
      simpleGraph_tree_existsUnique_neighbor_reachable_without_center
        G hG c (a j) hajc
    have hjreach : (G.induce {c}ᶜ).Reachable
        ⟨a j, by simpa using hajc⟩ ⟨a j, by simpa using hajc⟩ :=
      ⟨SimpleGraph.Walk.nil⟩
    have hjx : a j = x := hxuniq (a j) (ha j) hjreach
    have hireach : (G.induce {c}ᶜ).Reachable
        ⟨a i, by simpa using (ha i).ne.symm⟩
        ⟨a j, by simpa using hajc⟩ := by
      exact SimpleGraph.ConnectedComponent.exact hij
    have hix : a i = x := hxuniq (a i) (ha i) hireach
    apply hainj
    exact hix.trans hjx.symm
  · intro v
    obtain ⟨x, hx, hxreach, hxuniq⟩ :=
      simpleGraph_tree_existsUnique_neighbor_reachable_without_center
        G hG c v v.property
    rcases (hall x).mp hx with h0 | h1 | h2
    · refine ⟨0, ?_⟩
      apply SimpleGraph.ConnectedComponent.sound
      simpa [a, h0] using hxreach.symm
    · refine ⟨1, ?_⟩
      apply SimpleGraph.ConnectedComponent.sound
      simpa [a, h1] using hxreach.symm
    · refine ⟨2, ?_⟩
      apply SimpleGraph.ConnectedComponent.sound
      simpa [a, h2] using hxreach.symm

/-- The reverse implication of Theorem 1.8.7: an isomorphism of Dynkin
diagrams extends to an equivalence of reduced crystallographic root systems. -/
public theorem rootPairing_equiv_of_dynkinDiagramIso
    {ι ι₂ R M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    {Q : RootPairing ι₂ R M₂ N₂} [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced] (b₂ : Q.Base)
    (d : P.DynkinDiagramIso b.support Q b₂.support) :
    Nonempty (P.Equiv Q) := by
  apply rootPairing_equiv_of_cartanMatrix b b₂ d.toEquiv
  intro i j
  change Q.pairingIn ℤ (d.toEquiv i) (d.toEquiv j) = P.pairingIn ℤ i j
  simpa [RootPairing.dynkinDiagramOn] using d.map_entry i j

/-- The rank-one case of the finite irreducible classification: reduced crystallographic root
systems admitting singleton bases are equivalent.

This is GLS3, Theorem 1.8.7. -/
public theorem rankOne_rootPairing_equiv
    {ι ι₂ R M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    {Q : RootPairing ι₂ R M₂ N₂} [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced] (b₂ : Q.Base)
    [Unique b.support] [Unique b₂.support] :
    Nonempty (P.Equiv Q) := by
  apply rootPairing_equiv_of_cartanMatrix b b₂ (Equiv.ofUnique _ _)
  intro i j
  have hij : j = i := Subsingleton.elim _ _
  rw [hij]
  simp only [RootPairing.Base.cartanMatrix_apply_same]

/-- The positive subsystem determined by a crystallographic base uniquely
determines that base.

This is GLS3, Theorem 1.8.2. -/
public theorem base_toPositiveSubsystem_injective
    {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] :
    Function.Injective (RootPairing.Base.toPositiveSubsystem (P := P)) := by
  intro b c hbc
  have hs : b.support = c.support := by
    ext i
    rw [base_mem_support_iff_isIndecomposablePositive,
      base_mem_support_iff_isIndecomposablePositive, hbc]
  cases b
  cases c
  cases hs
  rfl

open Set

open Set

open Set

open Set

open Set

/-- Starting from any base, some Weyl-group translate has any prescribed
positive subsystem.

This is GLS3, Theorem 1.8.2. -/
public theorem exists_weylGroup_translate_base_toPositiveSubsystem
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (b₀ : P.Base) (S : P.PositiveSubsystem) :
    ∃ g : P.weylGroup, (g • b₀).toPositiveSubsystem = S := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Finite P.weylGroup := weylGroup_finite P
  let bad (b : P.Base) : Finset ι := Finset.univ.filter fun i => b.IsPos i ∧ i ∉ S
  obtain ⟨g, hg⟩ := Finite.exists_min fun g : P.weylGroup => (bad (g • b₀)).card
  let b : P.Base := g • b₀
  have hposS {i : ι} (hi : b.IsPos i)
      (hall : ∀ j ∈ b.support, j ∈ S) : i ∈ S := by
    exact hi.induction_on_add hall fun i j k hk hi hj => S.add_mem hi (hall j hj) hk
  by_cases hall : ∀ j ∈ b.support, j ∈ S
  · refine ⟨g, RootPairing.PositiveSubsystem.ext fun i => ?_⟩
    rw [_root_.RootPairing.Base.mem_toPositiveSubsystem]
    constructor
    · exact fun hi => hposS hi hall
    · intro hiS
      by_contra hnot
      let := P.indexNeg
      have hnegpos : b.IsPos (-i) :=
        (RootPairing.Base.IsPos.neg_iff_not b i).mpr hnot
      have hnegS : -i ∈ S := hposS hnegpos hall
      have : P.reflectionPerm i i ∈ S := by simpa using hnegS
      exact (S.neg_mem_iff_not_mem i).mp this hiS
  · push Not at hall
    obtain ⟨j, hj, hjS⟩ := hall
    let := P.indexNeg
    let r : P.weylGroup :=
      ⟨RootPairing.Equiv.reflection P j, P.reflection_mem_weylGroup j⟩
    have hjnegS : P.reflectionPerm j j ∈ S := (S.neg_mem_iff_not_mem j).mpr hjS
    have hjne : j ≠ P.reflectionPerm j j := by
      change j ≠ -j
      exact P.ne_neg (i := j)
    have hbad :
        bad (RootPairing.Base.mapAut (RootPairing.Equiv.reflection P j) b) =
          (bad b).erase j := by
      ext i
      by_cases hij : i = j
      · subst i
        simp [bad, RootPairing.Base.isPos_mapReflection_iff b hj, hjS, hjne]
      · by_cases hineg : i = P.reflectionPerm j j
        · subst i
          simp [bad, RootPairing.Base.isPos_mapReflection_iff b hj, hjnegS]
        · simp [bad, RootPairing.Base.isPos_mapReflection_iff b hj, hij, hineg]
    have hjbad : j ∈ bad b := by
      simp [bad, b.isPos_of_mem_support hj, hjS]
    have hlt :
        (bad (RootPairing.Base.mapAut (RootPairing.Equiv.reflection P j) b)).card <
          (bad b).card := by
      rw [hbad]
      exact Finset.card_erase_lt_of_mem hjbad
    have hmin := hg (r * g)
    have horbit :
        (r * g) • b₀ =
          RootPairing.Base.mapAut (RootPairing.Equiv.reflection P j) b := by
      change ((r : RootPairing.Aut P) * (g : RootPairing.Aut P)) • b₀ = _
      rw [mul_smul]
      rfl
    rw [horbit] at hmin
    change (bad b).card ≤ _ at hmin
    omega

open scoped BigOperators

private lemma finset_sum_le_two_terms
    {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (u v : α) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (f : α → ℤ) (hrest : ∀ x ∈ (S.erase u).erase v, f x ≤ 0) :
    (∑ x ∈ S, f x) ≤ f u + f v := by
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hu]
  have hv' : v ∈ S \ {u} :=
    Finset.mem_sdiff.mpr ⟨hv, by simpa using huv.symm⟩
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hv']
  have hrestsum : (∑ x ∈ (S \ {u}) \ {v}, f x) ≤ 0 := by
    simpa [Finset.sdiff_singleton_eq_erase] using
      (Finset.sum_nonpos (fun x hx => hrest x hx))
  omega

/-- A cycle whose Cartan edges satisfy the finite rank-two patterns forces
nonpositive column sums on its principal submatrix, contradicting positive
diagonal symmetrizability.  This excludes weighted as well as simply-laced
cycles. -/
public lemma not_cartan_cycle_of_rankTwo_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    {n : ℕ} (e : Fin (n + 3) ↪ κ)
    (hcycle : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j →
      A (e i) (e j) ≠ 0) : False := by
  let B : Matrix (Fin (n + 3)) (Fin (n + 3)) ℤ := A.submatrix e e
  let d' : Fin (n + 3) → ℤ := fun i => d (e i)
  have hpos' : (Matrix.diagonal d' * B).PosDef := by
    have hsub := hpos.submatrix e.injective
    convert hsub using 1
    ext i j
    simp [B, d', Matrix.diagonal_mul]
  have hdiag' : ∀ i, B i i = 2 := by
    intro i
    exact hdiag (e i)
  have hcol : ∀ i, ∑ j, B j i ≤ 0 := by
    intro i
    let u : Fin (n + 3) := i - 1
    let v : Fin (n + 3) := i + 1
    have huv : u ≠ v := by
      have hc := SimpleGraph.cycleGraph_degree_three_le (n := n) (v := i)
      rw [SimpleGraph.cycleGraph_degree_two_le] at hc
      dsimp [u, v]
      by_contra h
      simp [h] at hc
    have huAdj : (SimpleGraph.cycleGraph (n + 3)).Adj i u := by
      dsimp [u]
      simp [SimpleGraph.cycleGraph_adj]
    have hvAdj : (SimpleGraph.cycleGraph (n + 3)).Adj i v := by
      dsimp [v]
      simp [SimpleGraph.cycleGraph_adj]
    have hui : u ≠ i := by
      exact Ne.symm huAdj.ne
    have hvi : v ≠ i := by
      exact Ne.symm hvAdj.ne
    have hu_ne : B u i ≤ -1 := by
      have hne := hcycle i u huAdj
      have heiu : e i ≠ e u := by
        intro h
        exact hui (e.injective h).symm
      have hb := cartan_rankTwo_nonzero_bounds A hrank
        heiu hne
      simpa [B] using hb.2.1
    have hv_ne : B v i ≤ -1 := by
      have hne := hcycle i v hvAdj
      have heiv : e i ≠ e v := by
        intro h
        exact hvi (e.injective h).symm
      have hb := cartan_rankTwo_nonzero_bounds A hrank
        heiv hne
      simpa [B] using hb.2.1
    have hoff : ∀ j, j ∈ ((Finset.univ.erase i).erase u).erase v →
        B j i ≤ 0 := by
      intro j hj
      have hji : j ≠ i := by
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).2).1
      by_cases hzero : A (e j) (e i) = 0
      · simp [B, hzero]
      · have heji : e j ≠ e i := by
          intro h
          exact hji (e.injective h)
        have hb := cartan_rankTwo_nonzero_bounds A hrank heji hzero
        exact le_trans (by simpa [B] using hb.1) (by norm_num)
    have hsum := finset_sum_le_two_terms (Finset.univ.erase i) u v
      (by simp [hui]) (by simp [hvi]) huv (fun j => B j i) hoff
    have hsum' : (∑ j ∈ Finset.univ.erase i, B j i) ≤ -2 := by
      calc
        _ ≤ B u i + B v i := hsum
        _ ≤ -2 := by omega
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    have hdi := hdiag' i
    omega
  exact not_diagonal_mul_posDef_of_columnSums_nonpos B d' hdiag' hpos' hcol

open scoped SimpleGraph
open SimpleGraph

/-- The support graph of a positive-definite Cartan-style matrix contains no
cycle, including cycles with double or triple bonds. -/
public lemma not_cartan_supportCycle_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (hcycle : cycleGraph (n + 3) ⊑
      (SimpleGraph.fromRel fun i j => A i j ≠ 0)) : False := by
  classical
  rcases hcycle with ⟨f⟩
  let e : Fin (n + 3) ↪ κ := f.toEmbedding
  have hpos' :
      (Matrix.diagonal (d ∘ e) * A.submatrix e e).PosDef := by
    exact diagonal_mul_submatrix_posDef A d e hpos
  apply not_diagonal_mul_posDef_of_columnSums_nonpos (A.submatrix e e) (d ∘ e)
  · intro i
    exact hdiag _
  · exact hpos'
  · intro i
    calc
      (∑ j, A.submatrix e e j i) ≤
          ∑ j, (cycleGraph (n + 3)).lapMatrix ℤ i j := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hji : j = i
        · subst j
          simp [Matrix.submatrix, hdiag, SimpleGraph.lapMatrix,
            SimpleGraph.degMatrix, SimpleGraph.cycleGraph_degree_three_le]
        · have heji : e j ≠ e i := fun h => hji (e.injective h)
          have hij : i ≠ j := fun h => hji h.symm
          by_cases hadj : (cycleGraph (n + 3)).Adj i j
          · have hadjG := f.toHom.map_adj hadj
            change (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj (e i) (e j) at hadjG
            rw [SimpleGraph.fromRel_adj] at hadjG
            have hne : A (e j) (e i) ≠ 0 := by
              rcases hadjG.2 with hforward | hreverse
              · have hb := cartan_rankTwo_nonzero_bounds A hrank heji.symm hforward
                omega
              · exact hreverse
            have hb := cartan_rankTwo_nonzero_bounds A hrank heji hne
            simp [Matrix.submatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
              SimpleGraph.adjMatrix, hij, hadj, hb.1]
          · rcases hrank (e j) (e i) heji with h0 | h11 | h12 | h21 | h13 | h31
            all_goals simp [Matrix.submatrix, SimpleGraph.lapMatrix,
              SimpleGraph.degMatrix, SimpleGraph.adjMatrix, *]
      _ = 0 := by
        have hz := congrFun
          (SimpleGraph.lapMatrix_mulVec_const_eq_zero (R := ℤ) (cycleGraph (n + 3))) i
        simpa [Matrix.mulVec, dotProduct] using hz

open Set

/-- The Weyl-group element given by reflection in a root of a base. -/
@[expose]
public noncomputable def _root_.RootPairing.Base.simpleReflection
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (j : b.support) : P.weylGroup :=
  RootPairing.weylGroup.ofIdx P j

/-- The Weyl-group element represented by a word in the simple reflections
of a fixed base. Products are read from left to right. -/
@[expose]
public noncomputable def _root_.RootPairing.Base.wordProd
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (l : List b.support) : P.weylGroup :=
  (l.map b.simpleReflection).prod

@[simp]
public theorem _root_.RootPairing.Base.wordProd_nil
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) : b.wordProd [] = 1 :=
  rfl

@[simp]
public theorem _root_.RootPairing.Base.wordProd_cons
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (j : b.support) (l : List b.support) :
    b.wordProd (j :: l) = b.simpleReflection j * b.wordProd l := by
  simp [RootPairing.Base.wordProd]

@[simp]
public theorem _root_.RootPairing.Base.wordProd_append
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (l₁ l₂ : List b.support) :
    b.wordProd (l₁ ++ l₂) = b.wordProd l₁ * b.wordProd l₂ := by
  simp [RootPairing.Base.wordProd]

@[simp]
public theorem _root_.RootPairing.Base.simpleReflection_inv
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (j : b.support) :
    (b.simpleReflection j)⁻¹ = b.simpleReflection j := by
  apply Subtype.ext
  simp [RootPairing.Base.simpleReflection, RootPairing.weylGroup.ofIdx]

@[simp]
public theorem _root_.RootPairing.Base.simpleReflection_mul_self
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (j : b.support) :
    b.simpleReflection j * b.simpleReflection j = 1 := by
  nth_rewrite 1 [← b.simpleReflection_inv j]
  exact inv_mul_cancel _

/-- Every Weyl-group element has a word in the simple reflections of any
fixed base. -/
public theorem _root_.RootPairing.Base.exists_wordProd_eq
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) : ∃ l : List b.support, b.wordProd l = g := by
  suffices ∃ l : List b.support,
      (b.wordProd l : RootPairing.Aut P) = (g : RootPairing.Aut P) by
    rcases this with ⟨l, hl⟩
    exact ⟨l, Subtype.ext hl⟩
  have hg : (g : RootPairing.Aut P) ∈ Subgroup.closure
      (Set.range fun j : b.support => RootPairing.Equiv.reflection P j) := by
    rw [← Theory.AlgebraicGroup.weylGroup_generated_by_simpleReflections b]
    exact g.property
  refine Subgroup.closure_induction''
    (s := Set.range fun j : b.support => RootPairing.Equiv.reflection P j)
    (p := fun x _ => ∃ l : List b.support,
      (b.wordProd l : RootPairing.Aut P) = x) ?_ ?_ ?_ ?_ hg
  · intro x hx
    rcases hx with ⟨j, rfl⟩
    exact ⟨[j], by rfl⟩
  · intro x hx
    rcases hx with ⟨j, rfl⟩
    refine ⟨[j], ?_⟩
    change RootPairing.Equiv.reflection P j =
      (RootPairing.Equiv.reflection P j)⁻¹
    simp
  · exact ⟨[], by simp⟩
  · intro x y hx hy hx' hy'
    rcases hx' with ⟨l, rfl⟩
    rcases hy' with ⟨m, rfl⟩
    exact ⟨l ++ m, by simp⟩

/-- A simple reflection can be moved through another simple reflection by
reflecting its root. -/
public theorem _root_.RootPairing.Base.simpleReflection_mul
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (j : b.support) (i : ι) :
    b.simpleReflection j * RootPairing.weylGroup.ofIdx P i =
      RootPairing.weylGroup.ofIdx P (P.reflectionPerm j i) * b.simpleReflection j := by
  apply Subtype.ext
  change RootPairing.Equiv.reflection P j * RootPairing.Equiv.reflection P i =
    RootPairing.Equiv.reflection P (P.reflectionPerm j i) *
      RootPairing.Equiv.reflection P j
  have h := _root_.RootPairing.Equiv.reflection_reflectionPerm P i j
  have hj2 : RootPairing.Equiv.reflection P j *
      RootPairing.Equiv.reflection P j = 1 := by
    nth_rewrite 1 [← RootPairing.Equiv.reflection_inv P j]
    exact inv_mul_cancel _
  apply mul_right_cancel (b := RootPairing.Equiv.reflection P j)
  calc
    (RootPairing.Equiv.reflection P j * RootPairing.Equiv.reflection P i) *
        RootPairing.Equiv.reflection P j =
      RootPairing.Equiv.reflection P (P.reflectionPerm j i) := h.symm
    _ = RootPairing.Equiv.reflection P (P.reflectionPerm j i) * 1 := by simp
    _ = RootPairing.Equiv.reflection P (P.reflectionPerm j i) *
        (RootPairing.Equiv.reflection P j * RootPairing.Equiv.reflection P j) := by rw [hj2]
    _ = (RootPairing.Equiv.reflection P (P.reflectionPerm j i) *
        RootPairing.Equiv.reflection P j) * RootPairing.Equiv.reflection P j := by
          rw [mul_assoc]

/-- Move an arbitrary root reflection through a word in simple reflections. -/
public theorem _root_.RootPairing.Base.wordProd_mul_ofIdx
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (l : List b.support) (i : ι) :
    b.wordProd l * RootPairing.weylGroup.ofIdx P i =
      RootPairing.weylGroup.ofIdx P (P.weylGroupToPerm (b.wordProd l) i) * b.wordProd l := by
  induction l with
  | nil => simp
  | cons j l ih =>
      rw [b.wordProd_cons, mul_assoc, ih, ← mul_assoc, b.simpleReflection_mul]
      change RootPairing.weylGroup.ofIdx P
          (P.reflectionPerm j (P.weylGroupToPerm (b.wordProd l) i)) *
            b.simpleReflection j * b.wordProd l =
        RootPairing.weylGroup.ofIdx P
          (P.reflectionPerm j (P.weylGroupToPerm (b.wordProd l) i)) *
            (b.simpleReflection j * b.wordProd l)
      rw [mul_assoc]

/-- Exchange lemma in the form needed for chamber stabilizers: if a word
sends a simple root negative, appending its reflection is not length-increasing. -/
public theorem _root_.RootPairing.Base.exchange_word
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (l : List b.support) (j : b.support)
    (hneg : ¬ b.IsPos (P.weylGroupToPerm (b.wordProd l) j)) :
    ∃ l' : List b.support,
      b.wordProd l' = b.wordProd l * b.simpleReflection j ∧ l'.length < l.length := by
  induction l with
  | nil =>
      exfalso
      apply hneg
      simpa using b.isPos_of_mem_support j.property
  | cons k l ih =>
      have hneg' : ¬ b.IsPos
          (P.reflectionPerm k (P.weylGroupToPerm (b.wordProd l) j)) := by
        rw [b.wordProd_cons] at hneg
        change ¬ b.IsPos
          (P.reflectionPerm k (P.weylGroupToPerm (b.wordProd l) j)) at hneg
        exact hneg
      by_cases hpos : b.IsPos (P.weylGroupToPerm (b.wordProd l) j)
      · have heq : P.weylGroupToPerm (b.wordProd l) j = k :=
          (Theory.AlgebraicGroup.simpleReflection_unique_positiveRoot
            P b k.property _).mp ⟨hpos, hneg'⟩
        refine ⟨l, ?_, by simp⟩
        rw [b.wordProd_cons]
        change b.wordProd l = b.simpleReflection k *
          (b.wordProd l * RootPairing.weylGroup.ofIdx P j)
        rw [b.wordProd_mul_ofIdx]
        rw [← mul_assoc]
        change b.wordProd l = b.simpleReflection k *
          RootPairing.weylGroup.ofIdx P (P.weylGroupToPerm (b.wordProd l) j) *
            b.wordProd l
        rw [heq]
        change b.wordProd l =
          (b.simpleReflection k * b.simpleReflection k) * b.wordProd l
        simp
      · rcases ih hpos with ⟨l', hl', hlen⟩
        refine ⟨k :: l', ?_, by simpa using Nat.succ_lt_succ hlen⟩
        rw [b.wordProd_cons, hl', b.wordProd_cons, mul_assoc]

/-- Weyl-group permutations commute with the negation of root indices. -/
public theorem _root_.RootPairing.weylGroupToPerm_neg
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (g : P.weylGroup) (i : ι) :
    letI := P.indexNeg
    P.weylGroupToPerm g (-i) = -(P.weylGroupToPerm g i) := by
  let := P.indexNeg
  apply P.root.injective
  calc
    P.root (P.weylGroupToPerm g (-i)) = g • P.root (-i) :=
      (P.weylGroup_apply_root g (-i)).symm
    _ = g • (-P.root i) := by simp
    _ = -(g • P.root i) := by simp
    _ = -P.root (P.weylGroupToPerm g i) := by rw [P.weylGroup_apply_root]
    _ = P.root (-(P.weylGroupToPerm g i)) := by
      symm
      change P.root (P.reflectionPerm (P.weylGroupToPerm g i)
        (P.weylGroupToPerm g i)) = _
      rw [P.root_reflectionPerm, P.reflection_apply_self]

set_option maxHeartbeats 800000 in
/-- An exact Cartan-support numbering of a degree-three branch with a first
heavy edge gives the explicit matrix obstruction used to contradict positive
definiteness.  All graph and entry conditions are ordinary hypotheses. -/
public lemma not_cartan_branch_single_heavy_of_support_numbering
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {m : ℕ} (hm : 0 < m) (e : Fin (m + 4) ↪ κ) (u v : ℤ)
    (hsupport : ∀ i j : Fin (m + 4),
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (e i) (e j) ↔
        ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
         (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
         (2 ≤ i.val ∧ i.val + 1 = j.val ∧ j.val ≤ m + 2) ∨
         (2 ≤ j.val ∧ j.val + 1 = i.val ∧ i.val ≤ m + 2) ∨
         (i.val = m + 2 ∧ j.val = m + 3) ∨
         (i.val = m + 3 ∧ j.val = m + 2)))
    (hleaf : ∀ i j : Fin (m + 4),
      ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
       (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1)) →
      A (e i) (e j) = -1)
    (hpathForward : ∀ i j : Fin (m + 4),
      2 ≤ i.val → i.val + 1 = j.val → j.val ≤ m + 2 →
      A (e i) (e j) = -1)
    (hpathReverse : ∀ i j : Fin (m + 4),
      2 ≤ j.val → j.val + 1 = i.val → i.val ≤ m + 2 →
      A (e i) (e j) = -1)
    (hheavyForward : ∀ i j : Fin (m + 4),
      i.val = m + 2 → j.val = m + 3 → A (e i) (e j) = u)
    (hheavyReverse : ∀ i j : Fin (m + 4),
      i.val = m + 3 → j.val = m + 2 → A (e i) (e j) = v)
    (hheavy : 2 ≤ u * v) : False := by
  have hA : ∀ i j : Fin (m + 4), A (e i) (e j) =
      if i = j then 2 else if
        ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
         (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1)) then -1 else if
        (2 ≤ i.val ∧ i.val + 1 = j.val ∧ j.val ≤ m + 2) then -1 else if
        (2 ≤ j.val ∧ j.val + 1 = i.val ∧ i.val ≤ m + 2) then -1 else if
        (i.val = m + 2 ∧ j.val = m + 3) then u else if
        (i.val = m + 3 ∧ j.val = m + 2) then v else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact hdiag _
    by_cases hleafij :
        (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
        (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1)
    · rw [hleaf i j hleafij]
      rw [if_neg hij, if_pos hleafij]
    by_cases hforward : 2 ≤ i.val ∧ i.val + 1 = j.val ∧ j.val ≤ m + 2
    · rw [hpathForward i j hforward.1 hforward.2.1 hforward.2.2]
      rw [if_neg hij, if_neg hleafij, if_pos hforward]
    by_cases hreverse : 2 ≤ j.val ∧ j.val + 1 = i.val ∧ i.val ≤ m + 2
    · rw [hpathReverse i j hreverse.1 hreverse.2.1 hreverse.2.2]
      rw [if_neg hij, if_neg hleafij, if_neg hforward, if_pos hreverse]
    by_cases hheavyF : i.val = m + 2 ∧ j.val = m + 3
    · rw [hheavyForward i j hheavyF.1 hheavyF.2]
      rw [if_neg hij, if_neg hleafij, if_neg hforward, if_neg hreverse,
        if_pos hheavyF]
    by_cases hheavyR : i.val = m + 3 ∧ j.val = m + 2
    · rw [hheavyReverse i j hheavyR.1 hheavyR.2]
      rw [if_neg hij, if_neg hleafij, if_neg hforward, if_neg hreverse,
        if_neg hheavyF, if_pos hheavyR]
    have hzero : A (e i) (e j) = 0 := by
      by_contra hne
      have hadj : (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (e i) (e j) := by
        rw [SimpleGraph.fromRel_adj]
        exact ⟨e.injective.ne hij, Or.inl hne⟩
      rcases (hsupport i j).mp hadj with h | h | h | h | h | h | h | h
      · exact hleafij (Or.inl h)
      · exact hleafij (Or.inr (Or.inl h))
      · exact hleafij (Or.inr (Or.inr (Or.inl h)))
      · exact hleafij (Or.inr (Or.inr (Or.inr h)))
      · exact hforward h
      · exact hreverse h
      · exact hheavyF h
      · exact hheavyR h
    rw [if_neg hij, if_neg hleafij, if_neg hforward, if_neg hreverse,
      if_neg hheavyF, if_neg hheavyR]
    exact hzero
  exact not_cartan_branch_single_heavy_of_diagonal_mul_posDef
    A d hpos hm e u v hA hheavy

/-- The arbitrary-gap path obstruction only needs matrix entries on the
interval `[p,q+1]`.  The embedding below restricts the positive-definite
matrix to that principal submatrix, so entries and edges outside the interval
are unconstrained. -/
public lemma not_cartan_path_two_heavy_edges_of_bounded_interval
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {n p q : ℕ} (e : Fin n ↪ κ)
    (hq : q + 1 < n) (hpq : p + 1 < q)
    (u v s t : ℤ)
    (hAint : ∀ (i j : Fin n),
      p ≤ i.val → i.val ≤ q + 1 → p ≤ j.val → j.val ≤ q + 1 →
      A (e i) (e j) =
        if i = j then 2 else if i.val + 1 = j.val then
          if i.val = p then u else if i.val = q then s else -1
        else if j.val + 1 = i.val then
          if j.val = p then v else if j.val = q then t else -1
        else 0)
    (huv : 2 ≤ u * v) (hst : 2 ≤ s * t) : False := by
  let N : ℕ := q - p + 2
  have hpq0 : p ≤ q := by omega
  have hEmbBound : ∀ i : Fin N, p + i.val < n := by
    intro i
    dsimp [N] at i
    omega
  let emb : Fin N ↪ κ :=
    ⟨fun i => e ⟨p + i.val, hEmbBound i⟩, by
      intro i j hij
      apply Fin.ext
      have hsub : (⟨p + i.val, hEmbBound i⟩ : Fin n) =
          ⟨p + j.val, hEmbBound j⟩ := e.injective hij
      have hv : p + i.val = p + j.val := by
        simpa using congrArg Fin.val hsub
      omega⟩
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hqshift : (q - p) + 1 < N := by dsimp [N]; omega
  have hA' : ∀ i j : Fin N, A (emb i) (emb j) =
      if i = j then 2 else if i.val + 1 = j.val then
        if i.val = 0 then u else if i.val = q - p then s else -1
      else if j.val + 1 = i.val then
        if j.val = 0 then v else if j.val = q - p then t else -1
      else 0 := by
    intro i j
    let ii : Fin n := ⟨p + i.val, hEmbBound i⟩
    let jj : Fin n := ⟨p + j.val, hEmbBound j⟩
    have hii : emb i = e ii := rfl
    have hjj : emb j = e jj := rfl
    have hiLower : p ≤ ii.val := by dsimp [ii]; omega
    have hjLower : p ≤ jj.val := by dsimp [jj]; omega
    have hiUpper : ii.val ≤ q + 1 := by
      dsimp [ii, N] at *
      omega
    have hjUpper : jj.val ≤ q + 1 := by
      dsimp [jj, N] at *
      omega
    have hlocal := hAint ii jj hiLower hiUpper hjLower hjUpper
    change A (e ii) (e jj) = _
    have hij : ii = jj ↔ i = j := by
      constructor
      · intro h
        apply Fin.ext
        have hv := congrArg Fin.val h
        dsimp [ii, jj] at hv
        omega
      · intro h
        subst j
        rfl
    have hforward : ii.val + 1 = jj.val ↔ i.val + 1 = j.val := by
      dsimp [ii, jj]
      omega
    have hbackward : jj.val + 1 = ii.val ↔ j.val + 1 = i.val := by
      dsimp [ii, jj]
      omega
    have hip : ii.val = p ↔ i.val = 0 := by dsimp [ii]; omega
    have hiq : ii.val = q ↔ i.val = q - p := by dsimp [ii]; omega
    have hjp : jj.val = p ↔ j.val = 0 := by dsimp [jj]; omega
    have hjq : jj.val = q ↔ j.val = q - p := by dsimp [jj]; omega
    simpa [hij, hforward, hbackward, hip, hiq, hjp, hjq] using hlocal
  exact not_cartan_path_two_heavy_edges_of_diagonal_mul_posDef
    A d hpos emb u v s t hN hqshift (by omega) hA' huv hst

open SimpleGraph

/-- Path-numbered support graphs inherit the arbitrary-gap heavy-bond
obstruction from the explicit interval-kernel theorem.  The premises expose
the two designated rank-two entries and require all other path edges to be
simple; no classification result is stored in a definition or structure. -/
public lemma not_cartan_path_two_heavy_edges_of_pathGraph
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    {n p q : ℕ} (e : Fin n ≃ κ)
    (hpath : ∀ i j,
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj (e i) (e j) ↔
        (pathGraph n).Adj i j)
    (hp : p + 1 < n) (hq : q + 1 < n) (hpq : p + 1 < q)
    (u v s t : ℤ)
    (hpforward : A (e ⟨p, by omega⟩) (e ⟨p + 1, hp⟩) = u)
    (hpreverse : A (e ⟨p + 1, hp⟩) (e ⟨p, by omega⟩) = v)
    (hqforward : A (e ⟨q, by omega⟩) (e ⟨q + 1, hq⟩) = s)
    (hqreverse : A (e ⟨q + 1, hq⟩) (e ⟨q, by omega⟩) = t)
    (hsimple : ∀ {i j : Fin n}, (pathGraph n).Adj i j →
      ¬(i.val = p ∧ j.val = p + 1) →
      ¬(j.val = p ∧ i.val = p + 1) →
      ¬(i.val = q ∧ j.val = q + 1) →
      ¬(j.val = q ∧ i.val = q + 1) →
      A (e i) (e j) = -1 ∧ A (e j) (e i) = -1) :
    2 ≤ u * v → 2 ≤ s * t → False := by
  have hA : ∀ i j : Fin n, A (e i) (e j) =
      if i = j then 2 else if i.val + 1 = j.val then
        if i.val = p then u else if i.val = q then s else -1
      else if j.val + 1 = i.val then
        if j.val = p then v else if j.val = q then t else -1
      else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    by_cases hf : i.val + 1 = j.val
    · rw [if_neg hij, if_pos hf]
      by_cases hip : i.val = p
      · have hjval : j.val = p + 1 := by omega
        have hi : i = ⟨p, by omega⟩ := Fin.ext (by simpa using hip)
        have hj : j = ⟨p + 1, hp⟩ := Fin.ext (by simpa using hjval)
        have hgoal : A (e i) (e j) = u := by
          rw [congrArg e hi, congrArg e hj]
          exact hpforward
        simpa [hip] using hgoal
      by_cases hiq : i.val = q
      · have hjval : j.val = q + 1 := by omega
        have hqp : q ≠ p := by omega
        have hi : i = ⟨q, by omega⟩ := Fin.ext (by simpa using hiq)
        have hj : j = ⟨q + 1, hq⟩ := Fin.ext (by simpa using hjval)
        have hgoal : A (e i) (e j) = s := by
          rw [congrArg e hi, congrArg e hj]
          exact hqforward
        simpa [hip, hiq, hqp] using hgoal
      have hadj : (pathGraph n).Adj i j := by
        rw [pathGraph_adj]
        exact Or.inl hf
      have hsp := hsimple hadj (by omega) (by omega) (by omega) (by omega)
      simp [hip, hiq]
      exact hsp.1
    by_cases hb : j.val + 1 = i.val
    · rw [if_neg hij, if_neg hf, if_pos hb]
      by_cases hjp : j.val = p
      · have hival : i.val = p + 1 := by omega
        have hj : j = ⟨p, by omega⟩ := Fin.ext (by simpa using hjp)
        have hi : i = ⟨p + 1, hp⟩ := Fin.ext (by simpa using hival)
        have hgoal : A (e i) (e j) = v := by
          rw [congrArg e hi, congrArg e hj]
          exact hpreverse
        simpa [hjp] using hgoal
      by_cases hjq : j.val = q
      · have hival : i.val = q + 1 := by omega
        have hqp : q ≠ p := by omega
        have hj : j = ⟨q, by omega⟩ := Fin.ext (by simpa using hjq)
        have hi : i = ⟨q + 1, hq⟩ := Fin.ext (by simpa using hival)
        have hgoal : A (e i) (e j) = t := by
          rw [congrArg e hi, congrArg e hj]
          exact hqreverse
        simpa [hjp, hjq, hqp] using hgoal
      have hadj : (pathGraph n).Adj i j := by
        rw [pathGraph_adj]
        exact Or.inr hb
      have hsp := hsimple hadj (by omega) (by omega) (by omega) (by omega)
      simp [hjp, hjq]
      exact hsp.1
    rw [if_neg hij, if_neg hf, if_neg hb]
    exact (cartan_pathGraph_nonadjacent_entries_eq_zero
      A hrank e hpath hij (by simp [pathGraph_adj, hf, hb])).1
  exact not_cartan_path_two_heavy_edges_of_diagonal_mul_posDef
    A d hpos e.toEmbedding u v s t hp hq hpq hA

/-! Exact arm-length permutations extracted from the multiset classification. -/

public lemma nat_three_arm_lengths_exact_cases_of_affine_forbidden
    (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hE6 : ¬ (2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c))
    (hE7 : ¬ ((3 ≤ a ∧ 3 ≤ b) ∨ (3 ≤ a ∧ 3 ≤ c) ∨
      (3 ≤ b ∧ 3 ≤ c)))
    (hE8 : ¬ ((5 ≤ a ∧ 2 ≤ b) ∨ (5 ≤ a ∧ 2 ≤ c) ∨
      (5 ≤ b ∧ 2 ≤ a) ∨ (5 ≤ b ∧ 2 ≤ c) ∨
      (5 ≤ c ∧ 2 ≤ a) ∨ (5 ≤ c ∧ 2 ≤ b))) :
    2 ≤ (a ::ₘ b ::ₘ c ::ₘ 0).count 1 ∨
    ((a = 1 ∧ b = 2 ∧ c = 2) ∨ (a = 2 ∧ b = 1 ∧ c = 2) ∨
      (a = 2 ∧ b = 2 ∧ c = 1)) ∨
    ((a = 1 ∧ b = 2 ∧ c = 3) ∨ (a = 1 ∧ b = 3 ∧ c = 2) ∨
      (a = 2 ∧ b = 1 ∧ c = 3) ∨ (a = 2 ∧ b = 3 ∧ c = 1) ∨
      (a = 3 ∧ b = 1 ∧ c = 2) ∨ (a = 3 ∧ b = 2 ∧ c = 1)) ∨
    ((a = 1 ∧ b = 2 ∧ c = 4) ∨ (a = 1 ∧ b = 4 ∧ c = 2) ∨
      (a = 2 ∧ b = 1 ∧ c = 4) ∨ (a = 2 ∧ b = 4 ∧ c = 1) ∨
      (a = 4 ∧ b = 1 ∧ c = 2) ∨ (a = 4 ∧ b = 2 ∧ c = 1)) := by
  rcases nat_three_arm_lengths_permutation_of_affine_forbidden a b c ha hb hc hE6 hE7 hE8 with h | h | h | h
  · exact Or.inl h
  · right; left
    have ha' : a = 1 ∨ a = 2 := by
      have hm : a ∈ (1 ::ₘ 2 ::ₘ 2 ::ₘ 0) := by rw [← h]; simp
      simpa using hm
    have hb' : b = 1 ∨ b = 2 := by
      have hm : b ∈ (1 ::ₘ 2 ::ₘ 2 ::ₘ 0) := by rw [← h]; simp
      simpa using hm
    have hc' : c = 1 ∨ c = 2 := by
      have hm : c ∈ (1 ::ₘ 2 ::ₘ 2 ::ₘ 0) := by rw [← h]; simp
      simpa using hm
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;>
      rcases hc' with rfl | rfl <;> simp_all
    all_goals have h1 := congrArg (Multiset.count 1) h
    all_goals have h2 := congrArg (Multiset.count 2) h
    all_goals simp at h1 h2
  · right; right; left
    have ha' : a = 1 ∨ a = 2 ∨ a = 3 := by
      have hm : a ∈ (1 ::ₘ 2 ::ₘ 3 ::ₘ 0) := by rw [← h]; simp
      simpa using hm
    have hb' : b = 1 ∨ b = 2 ∨ b = 3 := by
      have hm : b ∈ (1 ::ₘ 2 ::ₘ 3 ::ₘ 0) := by rw [← h]; simp
      simpa using hm
    have hc' : c = 1 ∨ c = 2 ∨ c = 3 := by
      have hm : c ∈ (1 ::ₘ 2 ::ₘ 3 ::ₘ 0) := by rw [← h]; simp
      simpa using hm
    rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
      rcases hc' with rfl | rfl | rfl <;> simp_all
    all_goals have h1 := congrArg (Multiset.count 1) h
    all_goals have h2 := congrArg (Multiset.count 2) h
    all_goals have h3 := congrArg (Multiset.count 3) h
    all_goals simp at h1 h2 h3
  · right; right; right
    have ha' : a = 1 ∨ a = 2 ∨ a = 4 := by
      have hm : a ∈ (1 ::ₘ 2 ::ₘ 4 ::ₘ 0) := by rw [← h]; simp
      simpa using hm
    have hb' : b = 1 ∨ b = 2 ∨ b = 4 := by
      have hm : b ∈ (1 ::ₘ 2 ::ₘ 4 ::ₘ 0) := by rw [← h]; simp
      simpa using hm
    have hc' : c = 1 ∨ c = 2 ∨ c = 4 := by
      have hm : c ∈ (1 ::ₘ 2 ::ₘ 4 ::ₘ 0) := by rw [← h]; simp
      simpa using hm
    rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
      rcases hc' with rfl | rfl | rfl <;> simp_all
    all_goals have h1 := congrArg (Multiset.count 1) h
    all_goals have h2 := congrArg (Multiset.count 2) h
    all_goals have h4 := congrArg (Multiset.count 4) h
    all_goals simp at h1 h2 h4

open SimpleGraph

/-- A positive-definite Cartan matrix with an exact simple three-arm support
cannot have at least two vertices on every arm. -/
public lemma not_cartan_three_arm_affineE6_prefix_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {n0 n1 n2 : ℕ}
    (e : Option (Fin (n0 + 1) ⊕ Fin (n1 + 1) ⊕ Fin (n2 + 1)) ≃ κ)
    (hcenter0 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inl j))) ↔ j = 0)
    (hcenter1 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inr (Sum.inl j)))) ↔ j = 0)
    (hcenter2 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inr (Sum.inr j)))) ↔ j = 0)
    (hpath0 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inl l))) ↔
        (pathGraph (n0 + 1)).Adj j l)
    (hpath1 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inl l)))) ↔
        (pathGraph (n1 + 1)).Adj j l)
    (hpath2 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inr j))))
        (e (some (Sum.inr (Sum.inr l)))) ↔
        (pathGraph (n2 + 1)).Adj j l)
    (hcross01 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inl l)))))
    (hcross02 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inr l)))))
    (hcross12 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inr l)))))
    (hcenterBond0 :
      A (e none) (e (some (Sum.inl 0))) = -1 ∧
      A (e (some (Sum.inl 0))) (e none) = -1)
    (hcenterBond1 :
      A (e none) (e (some (Sum.inr (Sum.inl 0)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inl 0)))) (e none) = -1)
    (hcenterBond2 :
      A (e none) (e (some (Sum.inr (Sum.inr 0)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inr 0)))) (e none) = -1)
    (hsimple0 : ∀ r : Fin (n0 + 1), 0 < r.val →
      A (e (some (Sum.inl ⟨r.val - 1, by omega⟩)))
          (e (some (Sum.inl r))) = -1 ∧
      A (e (some (Sum.inl r)))
          (e (some (Sum.inl ⟨r.val - 1, by omega⟩))) = -1)
    (hsimple1 : ∀ r : Fin (n1 + 1), 0 < r.val →
      A (e (some (Sum.inr (Sum.inl ⟨r.val - 1, by omega⟩))))
          (e (some (Sum.inr (Sum.inl r)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inl r))))
          (e (some (Sum.inr (Sum.inl ⟨r.val - 1, by omega⟩)))) = -1)
    (hsimple2 : ∀ r : Fin (n2 + 1), 0 < r.val →
      A (e (some (Sum.inr (Sum.inr ⟨r.val - 1, by omega⟩))))
          (e (some (Sum.inr (Sum.inr r)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inr r))))
          (e (some (Sum.inr (Sum.inr ⟨r.val - 1, by omega⟩)))) = -1)
    (hn0 : 0 < n0) (hn1 : 0 < n1) (hn2 : 0 < n2) : False := by
  let G : SimpleGraph κ := SimpleGraph.fromRel fun x y => A x y ≠ 0
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  let f0 : Fin (n0 + 1) → κ := fun j => e (some (Sum.inl j))
  let f1 : Fin (n1 + 1) → κ := fun j => e (some (Sum.inr (Sum.inl j)))
  let f2 : Fin (n2 + 1) → κ := fun j => e (some (Sum.inr (Sum.inr j)))
  have hf0 : Function.Injective f0 := by
    intro j l hjl
    simpa [f0] using e.injective hjl
  have hf1 : Function.Injective f1 := by
    intro j l hjl
    simpa [f1] using e.injective hjl
  have hf2 : Function.Injective f2 := by
    intro j l hjl
    simpa [f2] using e.injective hjl
  have hc0 : ∀ j, e none ≠ f0 j := by
    intro j hj
    simpa [f0] using e.injective hj
  have hc1 : ∀ j, e none ≠ f1 j := by
    intro j hj
    simpa [f1] using e.injective hj
  have hc2 : ∀ j, e none ≠ f2 j := by
    intro j hj
    simpa [f2] using e.injective hj
  have h01 : ∀ j l, f0 j ≠ f1 l := by
    intro j l hjl
    simpa [f0, f1] using e.injective hjl
  have h02 : ∀ j l, f0 j ≠ f2 l := by
    intro j l hjl
    simpa [f0, f2] using e.injective hjl
  have h12 : ∀ j l, f1 j ≠ f2 l := by
    intro j l hjl
    simpa [f1, f2] using e.injective hjl
  obtain ⟨ep, hpref⟩ :=
    simpleGraph_three_arm_affineE6_prefix_embedding
      G (e none) f0 f1 f2 hf0 hf1 hf2 hc0 hc1 hc2 h01 h02 h12
      (by simpa [G, f0] using hcenter0)
      (by simpa [G, f1] using hcenter1)
      (by simpa [G, f2] using hcenter2)
      (by simpa [G, f0] using hpath0)
      (by simpa [G, f1] using hpath1)
      (by simpa [G, f2] using hpath2)
      (by simpa [G, f0, f1] using hcross01)
      (by simpa [G, f0, f2] using hcross02)
      (by simpa [G, f1, f2] using hcross12)
      hn0 hn1 hn2
  have hedge : ∀ x y, G.Adj x y → A x y = -1 := by
    simpa [G] using
      cartan_three_arm_support_adj_entry_eq_neg_one A e
        hcenter0 hcenter1 hcenter2 hpath0 hpath1 hpath2
        hcross01 hcross02 hcross12 hcenterBond0 hcenterBond1 hcenterBond2
        hsimple0 hsimple1 hsimple2
  apply not_cartan_affineE6_of_support_numbering A d hdiag hpos ep hpref
  intro i j hij
  exact hedge (ep i) (ep j) ((hpref i j).mpr hij)

open SimpleGraph

/-- A positive-definite Cartan matrix with an exact simple three-arm support
cannot have one vertex on one arm and three vertices on each of the other two arms. -/
public lemma not_cartan_three_arm_affineE7_prefix_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {n0 n1 n2 : ℕ}
    (e : Option (Fin (n0 + 1) ⊕ Fin (n1 + 1) ⊕ Fin (n2 + 1)) ≃ κ)
    (hcenter0 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inl j))) ↔ j = 0)
    (hcenter1 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inr (Sum.inl j)))) ↔ j = 0)
    (hcenter2 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inr (Sum.inr j)))) ↔ j = 0)
    (hpath0 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inl l))) ↔
        (pathGraph (n0 + 1)).Adj j l)
    (hpath1 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inl l)))) ↔
        (pathGraph (n1 + 1)).Adj j l)
    (hpath2 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inr j))))
        (e (some (Sum.inr (Sum.inr l)))) ↔
        (pathGraph (n2 + 1)).Adj j l)
    (hcross01 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inl l)))))
    (hcross02 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inr l)))))
    (hcross12 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inr l)))))
    (hcenterBond0 :
      A (e none) (e (some (Sum.inl 0))) = -1 ∧
      A (e (some (Sum.inl 0))) (e none) = -1)
    (hcenterBond1 :
      A (e none) (e (some (Sum.inr (Sum.inl 0)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inl 0)))) (e none) = -1)
    (hcenterBond2 :
      A (e none) (e (some (Sum.inr (Sum.inr 0)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inr 0)))) (e none) = -1)
    (hsimple0 : ∀ r : Fin (n0 + 1), 0 < r.val →
      A (e (some (Sum.inl ⟨r.val - 1, by omega⟩)))
          (e (some (Sum.inl r))) = -1 ∧
      A (e (some (Sum.inl r)))
          (e (some (Sum.inl ⟨r.val - 1, by omega⟩))) = -1)
    (hsimple1 : ∀ r : Fin (n1 + 1), 0 < r.val →
      A (e (some (Sum.inr (Sum.inl ⟨r.val - 1, by omega⟩))))
          (e (some (Sum.inr (Sum.inl r)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inl r))))
          (e (some (Sum.inr (Sum.inl ⟨r.val - 1, by omega⟩)))) = -1)
    (hsimple2 : ∀ r : Fin (n2 + 1), 0 < r.val →
      A (e (some (Sum.inr (Sum.inr ⟨r.val - 1, by omega⟩))))
          (e (some (Sum.inr (Sum.inr r)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inr r))))
          (e (some (Sum.inr (Sum.inr ⟨r.val - 1, by omega⟩)))) = -1)
    (hn1 : 2 ≤ n1) (hn2 : 2 ≤ n2) : False := by
  let G : SimpleGraph κ := SimpleGraph.fromRel fun x y => A x y ≠ 0
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  let f0 : Fin (n0 + 1) → κ := fun j => e (some (Sum.inl j))
  let f1 : Fin (n1 + 1) → κ := fun j => e (some (Sum.inr (Sum.inl j)))
  let f2 : Fin (n2 + 1) → κ := fun j => e (some (Sum.inr (Sum.inr j)))
  have hf0 : Function.Injective f0 := by
    intro j l hjl
    simpa [f0] using e.injective hjl
  have hf1 : Function.Injective f1 := by
    intro j l hjl
    simpa [f1] using e.injective hjl
  have hf2 : Function.Injective f2 := by
    intro j l hjl
    simpa [f2] using e.injective hjl
  have hc0 : ∀ j, e none ≠ f0 j := by
    intro j hj
    simpa [f0] using e.injective hj
  have hc1 : ∀ j, e none ≠ f1 j := by
    intro j hj
    simpa [f1] using e.injective hj
  have hc2 : ∀ j, e none ≠ f2 j := by
    intro j hj
    simpa [f2] using e.injective hj
  have h01 : ∀ j l, f0 j ≠ f1 l := by
    intro j l hjl
    simpa [f0, f1] using e.injective hjl
  have h02 : ∀ j l, f0 j ≠ f2 l := by
    intro j l hjl
    simpa [f0, f2] using e.injective hjl
  have h12 : ∀ j l, f1 j ≠ f2 l := by
    intro j l hjl
    simpa [f1, f2] using e.injective hjl
  obtain ⟨ep, hpref⟩ :=
    simpleGraph_three_arm_affineE7_prefix_embedding
      G (e none) f0 f1 f2 hf0 hf1 hf2 hc0 hc1 hc2 h01 h02 h12
      (by simpa [G, f0] using hcenter0)
      (by simpa [G, f1] using hcenter1)
      (by simpa [G, f2] using hcenter2)
      (by simpa [G, f0] using hpath0)
      (by simpa [G, f1] using hpath1)
      (by simpa [G, f2] using hpath2)
      (by simpa [G, f0, f1] using hcross01)
      (by simpa [G, f0, f2] using hcross02)
      (by simpa [G, f1, f2] using hcross12)
      hn1 hn2
  have hedge : ∀ x y, G.Adj x y → A x y = -1 := by
    simpa [G] using
      cartan_three_arm_support_adj_entry_eq_neg_one A e
        hcenter0 hcenter1 hcenter2 hpath0 hpath1 hpath2
        hcross01 hcross02 hcross12 hcenterBond0 hcenterBond1 hcenterBond2
        hsimple0 hsimple1 hsimple2
  apply not_cartan_affineE7_of_support_numbering A d hdiag hpos ep hpref
  intro i j hij
  exact hedge (ep i) (ep j) ((hpref i j).mpr hij)

end Theory.AlgebraicGroup

