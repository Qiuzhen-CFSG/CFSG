module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The center argument for finite tree automorphisms

Repeatedly remove all leaves while the remaining graph is nonempty. Paths
between remaining vertices avoid leaves, so each remaining graph is a tree.
Cardinality induction terminates at a single vertex or an edge. Every
automorphism preserves degree and therefore all stages of this process.
The resulting invariant clique supplies a common fixed vertex for every family
of automorphisms preserving the two vertex colors.

This supplies the elementary finite-tree center argument for the defining-
characteristic rank-two Borel--Tits step in Aschbacher--Smith,
*The Classification of Quasithin Groups*, Theorem 0.1.2(1), printed pp. 3--4
and 481--482. No assumption on the order of the automorphism group is needed.
-/

@[expose] public section

namespace SimpleGraph

universe u
variable {V : Type u} {T : SimpleGraph V}

private theorem path_leaf_is_endpoint [Fintype V] [DecidableRel T.Adj]
    {x y z : V} {p : T.Walk x y} (hp : p.IsPath) (hz : z ∈ p.support)
    (hdeg : T.degree z = 1) : z = x ∨ z = y := by
  by_contra hn
  have hzx : z ≠ x := fun h => hn (Or.inl h)
  have hzy : z ≠ y := fun h => hn (Or.inr h)
  obtain ⟨a, b, ha, hb, rfl⟩ := hp.mem_support_iff_exists_append.mp hz
  have han : ¬a.Nil := Walk.not_nil_of_ne hzx.symm
  have hbn : ¬b.Nil := Walk.not_nil_of_ne hzy
  obtain ⟨w, _, hw⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  have he : a.penultimate = b.snd :=
    (hw _ (a.adj_penultimate han).symm).trans (hw _ (b.adj_snd hbn)).symm
  exact hp.ne_of_mem_support_of_append (b.adj_snd hbn).ne.symm
    (a.getVert_mem_support _) (b.getVert_mem_support _) he

private theorem nonLeaves_connected [Fintype V] [DecidableRel T.Adj]
    (hT : T.Connected) (hs : Set.Nonempty {v | T.degree v ≠ 1}) :
    (T.induce {v | T.degree v ≠ 1}).Connected := by
  rw [connected_iff_exists_forall_reachable]
  obtain ⟨x, hx⟩ := hs
  refine ⟨⟨x, hx⟩, fun y => ?_⟩
  obtain ⟨p, hp⟩ := hT.exists_isPath x y
  have hsupp : ∀ z ∈ p.support, T.degree z ≠ 1 := by
    intro z hz hdeg
    rcases path_leaf_is_endpoint hp hz hdeg with h | h
    · exact hx (h ▸ hdeg)
    · exact y.property (h ▸ hdeg)
  exact (p.induce _ hsupp).reachable

private theorem all_leaves_pairwise_adj [Fintype V] [DecidableRel T.Adj]
    (hT : T.Connected) (hleaf : ∀ v, T.degree v = 1) (x y : V) : x = y ∨ T.Adj x y := by
  obtain ⟨p, hp⟩ := hT.exists_isPath x y
  by_cases hn : p.Nil
  · exact Or.inl hn.eq
  · have hs := path_leaf_is_endpoint hp (p.getVert_mem_support _) (hleaf p.snd)
    rcases hs with h | h
    · exact False.elim ((p.adj_snd hn).ne h.symm)
    · exact Or.inr (h ▸ p.adj_snd hn)

private theorem invariant_center_aux (n : ℕ) :
    ∀ (W : Type u) [Fintype W], Fintype.card W = n →
      ∀ (T : SimpleGraph W), T.IsTree →
        ∃ s : Set W, s.Nonempty ∧
          (∀ x ∈ s, ∀ y ∈ s, x = y ∨ T.Adj x y) ∧
          ∀ f : T ≃g T, Set.MapsTo f s s := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W inst hcard T hT
    classical
    let : Nonempty W := hT.connected.nonempty
    by_cases hsub : Subsingleton W
    · exact ⟨Set.univ, Set.univ_nonempty, fun x _ y _ => Or.inl (hsub.elim x y),
        fun _ _ _ => Set.mem_univ _⟩
    let : Nontrivial W := not_subsingleton_iff_nontrivial.mp hsub
    let s : Set W := {v | T.degree v ≠ 1}
    by_cases hs : s.Nonempty
    · obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
      have hlt : Fintype.card s < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (x := v) (by simpa [s] using hv)
      have hTs : (T.induce s).IsTree :=
        ⟨nonLeaves_connected hT.connected hs, hT.isAcyclic.induce s⟩
      obtain ⟨t, ht, hcl, hinv⟩ := ih (Fintype.card s) hlt s rfl (T.induce s) hTs
      refine ⟨Subtype.val '' t, ht.image _, ?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact (hcl x hx y hy).imp (congrArg Subtype.val) id
      · intro f z hz
        obtain ⟨w, hw, rfl⟩ := hz
        let f' : T.induce s ≃g T.induce s :=
          { toEquiv := f.toEquiv.subtypeEquiv (fun v => by simp [s, f.degree_eq])
            map_rel_iff' := by intro a b; exact f.map_adj_iff }
        exact ⟨f' w, hinv f' hw, rfl⟩
    · have hleaf : ∀ v, T.degree v = 1 := by
        intro v
        by_contra h
        exact hs ⟨v, h⟩
      exact ⟨Set.univ, Set.univ_nonempty,
        fun x _ y _ => all_leaves_pairwise_adj hT.connected hleaf x y,
        fun _ _ _ => Set.mem_univ _⟩

/-- Simultaneous removal of leaves produces a nonempty clique preserved by every
automorphism of a finite tree. This is the central vertex or central edge. -/
theorem IsTree.exists_invariant_clique [Finite V] (hT : T.IsTree) :
    ∃ s : Set V, s.Nonempty ∧
      (∀ x ∈ s, ∀ y ∈ s, x = y ∨ T.Adj x y) ∧
      ∀ f : T ≃g T, Set.MapsTo f s s := by
  let := Fintype.ofFinite V
  exact invariant_center_aux (Fintype.card V) V rfl T hT

/-- Automorphisms of a finite tree preserving its two vertex colors have a common
fixed vertex. Color preservation prevents interchanging the central endpoints. -/
theorem IsTree.exists_fixed_vertex_of_color_preserving [Finite V]
    (hT : T.IsTree) (color : V → Bool)
    (hcol : ∀ {x y}, T.Adj x y → color x ≠ color y) :
    ∃ v : V, ∀ f : T ≃g T, (∀ x, color (f x) = color x) → f v = v := by
  obtain ⟨s, ⟨v, hv⟩, hcl, hinv⟩ := IsTree.exists_invariant_clique hT
  refine ⟨v, fun f hf => ?_⟩
  rcases hcl (f v) (hinv f hv) v hv with he | ha
  · exact he
  · exact False.elim (hcol ha (hf v))

end SimpleGraph
