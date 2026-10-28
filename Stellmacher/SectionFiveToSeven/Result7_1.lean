module

public import Stellmacher.SectionFiveToSeven.Defs

/-!
# Elementary properties of the Section 7 coset graph

This module proves Stellmacher (7.1) for the right-coset graph packaged by
`CosetGraphContext`.  Every edge has a common representative `k`: after
possibly swapping its endpoints it is `{P₁k, P₂k}`.  Right multiplication
therefore gives edge transitivity, conjugates the two base stabilizers, and
acts transitively on the neighbors of each vertex.  The two coset families are
disjoint because equal opposite-type vertices would turn a genuine edge into
an edge between two vertices of the same type.  Connectedness follows from
the path supplied by the context's distance interface.

The intrinsic theorem `lemma_seven_one_graph` uses only the graph context;
the original `lemma_seven_one` retains its Section Seven parameter as a
compatibility wrapper. This permits structural local-type arguments to use
neighbor transitivity without imposing global campaign hypotheses.

The source is `refs/latex/stellmacher-n-group.tex`, (7.1), corresponding to
Journal of Algebra 190 (1997), p. 32.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

variable {G : Type u} [Group G] [Finite G]
  {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)

private theorem coset₁_eq_of_mem {g k : G}
    (hk : k ∈ MulOpposite.op g • (P1 : Set G)) :
    Γ.coset₁ g = Γ.coset₁ k := by
  rw [Γ.coset₁_eq_iff]
  rcases Set.mem_smul_set.mp hk with ⟨p, hp, rfl⟩
  change MulOpposite.op g • (P1 : Set G) =
    MulOpposite.op (p * g) • (P1 : Set G)
  rw [show MulOpposite.op (p * g) = MulOpposite.op g * MulOpposite.op p by rfl,
    mul_smul, op_smul_coe_set hp]

private theorem coset₂_eq_of_mem {g k : G}
    (hk : k ∈ MulOpposite.op g • (P2 : Set G)) :
    Γ.coset₂ g = Γ.coset₂ k := by
  rw [Γ.coset₂_eq_iff]
  rcases Set.mem_smul_set.mp hk with ⟨p, hp, rfl⟩
  change MulOpposite.op g • (P2 : Set G) =
    MulOpposite.op (p * g) • (P2 : Set G)
  rw [show MulOpposite.op (p * g) = MulOpposite.op g * MulOpposite.op p by rfl,
    mul_smul, op_smul_coe_set hp]

omit [Finite G] in
private theorem right_coset_mul_eq_iff_conj_mem
    (P : Subgroup G) (g x : G) :
    MulOpposite.op (g * x) • (P : Set G) =
        MulOpposite.op g • (P : Set G) ↔
      g * x * g⁻¹ ∈ P := by
  constructor
  · intro hsets
    have hmem : g * x ∈ MulOpposite.op (g * x) • (P : Set G) :=
      Set.mem_smul_set.mpr ⟨1, P.one_mem, by simp⟩
    rw [hsets] at hmem
    rcases Set.mem_smul_set.mp hmem with ⟨p, hp, hp_eq⟩
    have hp_eq' : p * g = g * x := by simpa using hp_eq
    have : g * x * g⁻¹ = p := by
      rw [← hp_eq', mul_assoc, mul_inv_cancel, mul_one]
    rwa [this]
  · intro hp
    let p : G := g * x * g⁻¹
    have hp' : p ∈ P := hp
    have heq : g * x = p * g := by
      simp [p, mul_assoc]
    rw [heq]
    change MulOpposite.op (p * g) • (P : Set G) =
      MulOpposite.op g • (P : Set G)
    rw [show MulOpposite.op (p * g) =
        MulOpposite.op g * MulOpposite.op p by rfl,
      mul_smul, op_smul_coe_set hp']

private theorem stabilizer_coset₁ (g : G) :
    stabilizer Γ (Γ.coset₁ g) = conjugateBy P1 g⁻¹ := by
  ext x
  have hmem : x ∈ stabilizer Γ (Γ.coset₁ g) ↔
      Γ.act x (Γ.coset₁ g) = Γ.coset₁ g := by
    have hdef : (stabilizer Γ (Γ.coset₁ g) : Set G) =
        {y | Γ.act y (Γ.coset₁ g) = Γ.coset₁ g} :=
      Γ.stabilizer_def (Γ.coset₁ g)
    exact Set.ext_iff.mp hdef x
  rw [hmem, Γ.act_coset₁, Γ.coset₁_eq_iff,
    right_coset_mul_eq_iff_conj_mem]
  constructor
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp [mul_assoc]
  · rintro ⟨p, hp, hp_eq⟩
    change g⁻¹ * p * (g⁻¹)⁻¹ = x at hp_eq
    rw [← hp_eq]
    simpa [mul_assoc] using hp

private theorem stabilizer_coset₂ (g : G) :
    stabilizer Γ (Γ.coset₂ g) = conjugateBy P2 g⁻¹ := by
  ext x
  have hmem : x ∈ stabilizer Γ (Γ.coset₂ g) ↔
      Γ.act x (Γ.coset₂ g) = Γ.coset₂ g := by
    have hdef : (stabilizer Γ (Γ.coset₂ g) : Set G) =
        {y | Γ.act y (Γ.coset₂ g) = Γ.coset₂ g} :=
      Γ.stabilizer_def (Γ.coset₂ g)
    exact Set.ext_iff.mp hdef x
  rw [hmem, Γ.act_coset₂, Γ.coset₂_eq_iff,
    right_coset_mul_eq_iff_conj_mem]
  constructor
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp [mul_assoc]
  · rintro ⟨p, hp, hp_eq⟩
    change g⁻¹ * p * (g⁻¹)⁻¹ = x at hp_eq
    rw [← hp_eq]
    simpa [mul_assoc] using hp

private theorem mem_stabilizer_iff {g : G} {d : Γ.Vertex} :
    g ∈ stabilizer Γ d ↔ Γ.act g d = d := by
  have hdef : (stabilizer Γ d : Set G) = {x | Γ.act x d = d} :=
    Γ.stabilizer_def d
  exact Set.ext_iff.mp hdef g

private theorem coset₁_ne_coset₂ (g h : G) :
    Γ.coset₁ g ≠ Γ.coset₂ h := by
  intro heq
  have hedge : Γ.adjacent (Γ.coset₁ g) (Γ.coset₂ g) := by
    rw [Γ.adj_cosets]
    apply Set.nonempty_iff_ne_empty.mp
    refine ⟨g, ?_, ?_⟩
    · exact Set.mem_smul_set.mpr ⟨1, P1.one_mem, by simp⟩
    · exact Set.mem_smul_set.mpr ⟨1, P2.one_mem, by simp⟩
  exact Γ.no_adj_coset₂_coset₂ h g (heq ▸ hedge)

private theorem adjacent_irrefl (d : Γ.Vertex) : ¬ Γ.adjacent d d := by
  rcases Γ.coset₁_surjective d with ⟨g, hg | hg⟩
  · rw [hg]
    exact Γ.no_adj_coset₁_coset₁ g g
  · rw [hg]
    exact Γ.no_adj_coset₂_coset₂ g g

private theorem edge_common_rep {d l : Γ.Vertex} (hdl : Γ.adjacent d l) :
    ∃ k : G,
      (d = Γ.coset₁ k ∧ l = Γ.coset₂ k) ∨
      (d = Γ.coset₂ k ∧ l = Γ.coset₁ k) := by
  rcases Γ.coset₁_surjective d with ⟨g, hd | hd⟩ <;>
    rcases Γ.coset₁_surjective l with ⟨h, hl | hl⟩
  · exact (Γ.no_adj_coset₁_coset₁ g h (hd ▸ hl ▸ hdl)).elim
  · have hinter := (Γ.adj_cosets g h).mp (hd ▸ hl ▸ hdl)
    rcases Set.nonempty_iff_ne_empty.mpr hinter with ⟨k, hkg, hkh⟩
    exact ⟨k, Or.inl ⟨hd.trans (coset₁_eq_of_mem Γ hkg),
      hl.trans (coset₂_eq_of_mem Γ hkh)⟩⟩
  · have hinter := (Γ.adj_cosets h g).mp
      (Γ.adjacent_symm (hd ▸ hl ▸ hdl))
    rcases Set.nonempty_iff_ne_empty.mpr hinter with ⟨k, hkh, hkg⟩
    exact ⟨k, Or.inr ⟨hd.trans (coset₂_eq_of_mem Γ hkg),
      hl.trans (coset₁_eq_of_mem Γ hkh)⟩⟩
  · exact (Γ.no_adj_coset₂_coset₂ g h (hd ▸ hl ▸ hdl)).elim

private theorem adjacent_iff_distance_eq_one {d l : Γ.Vertex} :
    Γ.adjacent d l ↔ Γ.distance d l = 1 := by
  constructor
  · intro hdl
    let f : Fin 2 → Γ.Vertex := ![d, l]
    have hpath : ∀ i : Fin 1, Γ.adjacent (f i.castSucc) (f i.succ) := by
      intro i
      fin_cases i
      exact hdl
    have hle : Γ.distance d l ≤ 1 := by
      simpa [f] using Γ.distance_le_of_path 1 f hpath
    have hne : Γ.distance d l ≠ 0 := by
      intro hzero
      have hEq := (Γ.distance_zero_iff d l).mp hzero
      exact adjacent_irrefl Γ d (hEq ▸ hdl)
    omega
  · intro hdist
    rcases Γ.distance_path d l with ⟨f, hstart, hend, hpath⟩
    have hpos : 0 < Γ.distance d l := hdist ▸ Nat.zero_lt_one
    have hedge := hpath ⟨0, hpos⟩
    have hi : (⟨0, hpos⟩ : Fin (Γ.distance d l)).succ =
        ⟨Γ.distance d l, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp [hdist]
    rw [hi, hend] at hedge
    simpa [hstart] using hedge

private theorem mem_neighborhood_iff_adjacent {d l : Γ.Vertex} :
    l ∈ neighborhood Γ d ↔ Γ.adjacent d l := by
  rw [neighborhood, Γ.neighbors_def]
  change Γ.distance l d = 1 ↔ Γ.adjacent d l
  rw [Γ.distance_symm]
  exact (adjacent_iff_distance_eq_one Γ).symm

omit [Finite G] in
private theorem conjugateBy_inf (A B : Subgroup G) (g : G) :
    conjugateBy A g ⊓ conjugateBy B g = conjugateBy (A ⊓ B) g := by
  exact (Subgroup.map_inf A B (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm

public structure LemmaSevenOneConclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) : Prop where
  connected : IsConnected Γ
  edge_not_vertex_transitive : IsEdgeTransitive Γ ∧ ¬ IsVertexTransitive Γ
  distinguished_edge : ∃ a b : Γ.Vertex,
    IsAdjacent Γ a b ∧ stabilizer Γ a = P1 ∧ stabilizer Γ b = P2
  vertex_stabilizers_conjugate :
    ∀ d : Γ.Vertex, ∃ g : G,
      stabilizer Γ d = conjugateBy P1 g ∨
        stabilizer Γ d = conjugateBy P2 g
  edge_stabilizers_conjugate :
    ∀ d l : Γ.Vertex, IsAdjacent Γ d l →
      ∃ g : G,
        stabilizer Γ d ⊓ stabilizer Γ l = conjugateBy (P1 ⊓ P2) g
  local_transitivity : ∀ d : Γ.Vertex,
    IsActionTransitiveOn Γ (stabilizer Γ d) (neighborhood Γ d)

/-- **Stellmacher (7.1).**  Elementary properties of the coset graph,
including the conjugacy description of vertex and edge stabilizers. -/
public theorem lemma_seven_one_graph
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) :
    LemmaSevenOneConclusion Γ := by
  refine
    { connected := ?_
      edge_not_vertex_transitive := ?_
      distinguished_edge := ?_
      vertex_stabilizers_conjugate := ?_
      edge_stabilizers_conjugate := ?_
      local_transitivity := ?_ }
  · intro d l
    exact ⟨Γ.distance d l, Γ.distance_path d l⟩
  · constructor
    · intro d l d' l' hdl hd'l'
      rcases edge_common_rep Γ hdl with ⟨g, hg | hg⟩
      · rcases edge_common_rep Γ hd'l' with ⟨k, hk | hk⟩
        · refine ⟨g⁻¹ * k, Or.inl ⟨?_, ?_⟩⟩
          · rw [hg.1, hk.1, Γ.act_coset₁]
            simp
          · rw [hg.2, hk.2, Γ.act_coset₂]
            simp
        · refine ⟨g⁻¹ * k, Or.inr ⟨?_, ?_⟩⟩
          · rw [hg.1, hk.2, Γ.act_coset₁]
            simp
          · rw [hg.2, hk.1, Γ.act_coset₂]
            simp
      · rcases edge_common_rep Γ hd'l' with ⟨k, hk | hk⟩
        · refine ⟨g⁻¹ * k, Or.inr ⟨?_, ?_⟩⟩
          · rw [hg.1, hk.2, Γ.act_coset₂]
            simp
          · rw [hg.2, hk.1, Γ.act_coset₁]
            simp
        · refine ⟨g⁻¹ * k, Or.inl ⟨?_, ?_⟩⟩
          · rw [hg.1, hk.1, Γ.act_coset₂]
            simp
          · rw [hg.2, hk.2, Γ.act_coset₁]
            simp
    · intro htrans
      rcases htrans (Γ.coset₁ 1) (Γ.coset₂ 1) with ⟨g, hg⟩
      rw [Γ.act_coset₁, one_mul] at hg
      exact coset₁_ne_coset₂ Γ g 1 hg
  · refine ⟨Γ.coset₁ 1, Γ.coset₂ 1, ?_, ?_, ?_⟩
    · rw [IsAdjacent, Γ.adj_cosets]
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨1,
        Set.mem_smul_set.mpr ⟨1, P1.one_mem, by simp⟩,
        Set.mem_smul_set.mpr ⟨1, P2.one_mem, by simp⟩⟩
    · rw [stabilizer_coset₁]
      ext x
      simp [conjugateBy]
    · rw [stabilizer_coset₂]
      ext x
      simp [conjugateBy]
  · intro d
    rcases Γ.coset₁_surjective d with ⟨g, hg | hg⟩
    · exact ⟨g⁻¹, Or.inl (hg ▸ stabilizer_coset₁ Γ g)⟩
    · exact ⟨g⁻¹, Or.inr (hg ▸ stabilizer_coset₂ Γ g)⟩
  · intro d l hdl
    rcases edge_common_rep Γ hdl with ⟨g, hg | hg⟩
    · refine ⟨g⁻¹, ?_⟩
      rw [hg.1, hg.2, stabilizer_coset₁, stabilizer_coset₂]
      exact conjugateBy_inf P1 P2 g⁻¹
    · refine ⟨g⁻¹, ?_⟩
      rw [hg.1, hg.2, stabilizer_coset₂, stabilizer_coset₁, inf_comm]
      exact conjugateBy_inf P1 P2 g⁻¹
  · intro d l m hl hm
    have hdl : Γ.adjacent d l := (mem_neighborhood_iff_adjacent Γ).mp hl
    have hdm : Γ.adjacent d m := (mem_neighborhood_iff_adjacent Γ).mp hm
    rcases edge_common_rep Γ hdl with ⟨g, hg | hg⟩
    · rcases edge_common_rep Γ hdm with ⟨k, hk | hk⟩
      · refine ⟨⟨g⁻¹ * k, (mem_stabilizer_iff Γ).mpr ?_⟩, ?_⟩
        · rw [hg.1, Γ.act_coset₁]
          have hcos : Γ.coset₁ k = Γ.coset₁ g := hk.1.symm.trans hg.1
          simpa using hcos
        · change Γ.act (g⁻¹ * k) l = m
          rw [hg.2, hk.2, Γ.act_coset₂]
          simp
      · exact (coset₁_ne_coset₂ Γ g k (hg.1.symm.trans hk.1)).elim
    · rcases edge_common_rep Γ hdm with ⟨k, hk | hk⟩
      · exact (coset₁_ne_coset₂ Γ k g (hk.1.symm.trans hg.1)).elim
      · refine ⟨⟨g⁻¹ * k, (mem_stabilizer_iff Γ).mpr ?_⟩, ?_⟩
        · rw [hg.1, Γ.act_coset₂]
          have hcos : Γ.coset₂ k = Γ.coset₂ g := hk.1.symm.trans hg.1
          simpa using hcos
        · change Γ.act (g⁻¹ * k) l = m
          rw [hg.2, hk.2, Γ.act_coset₁]
          simp

/-- The original Section Seven interface, with its supplied hypotheses retained. -/
public theorem lemma_seven_one
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (_h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2) :
    LemmaSevenOneConclusion Γ :=
  lemma_seven_one_graph Γ

end Stellmacher.SectionsFiveToSeven
