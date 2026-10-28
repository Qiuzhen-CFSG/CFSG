module

public import Theory.Combinatorics.PairGraphTriangleClosure.Triangulation
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Four-transitive cycle bases on unordered pairs

A group acting four-transitively on the point set acts on its unordered pairs
by graph automorphisms. Every triangle uses at most four points, and multiple
transitivity moves that support into a translate of any fixed four-point set.
Triangulability therefore makes the translated local cycles a nonabelian cycle
base. The edge-support version is the interface for graph uniqueness systems.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §5.2,
proof of Theorem 5.2.10, printed p.658; cycle closure is as in Aschbacher,
*Sporadic Groups*, §§33–34 and §37.
-/

@[expose] public section

open SimpleGraph
open scoped Pointwise
namespace Theory.Combinatorics.PairGraph
variable {α G : Type*} [DecidableEq α] [Group G] [MulAction G α]

/-- The induced action on unordered pairs. -/
instance vertexMulAction : MulAction G (Vertex α) where
  smul g v := ⟨g • v.val, (Finset.card_smul_finset g v.val).trans v.property⟩
  one_smul v := Subtype.ext (one_smul G v.val)
  mul_smul g h v := Subtype.ext (mul_smul g h v.val)

@[simp] theorem smul_vertex_val (g : G) (v : Vertex α) :
    (g • v).val = g • v.val := rfl

/-- The induced pair action preserves adjacency. -/
theorem smul_adj (g : G) {v w : Vertex α} (h : (graph α).Adj v w) :
    (graph α).Adj (g • v) (g • w) := by
  refine ⟨fun heq => h.1 ((MulAction.injective g) heq), ?_⟩
  obtain ⟨a, ha⟩ := h.2
  refine ⟨g • a, Finset.mem_inter.mpr ?_⟩
  exact ⟨Finset.smul_mem_smul_finset (Finset.mem_inter.mp ha).1,
    Finset.smul_mem_smul_finset (Finset.mem_inter.mp ha).2⟩

/-- Each acting element gives a genuine automorphism of the pair graph. -/
def actionIso (g : G) : graph α ≃g graph α where
  toEquiv := MulAction.toPerm g
  map_rel_iff' := by
    intro v w
    constructor
    · intro h
      simpa using smul_adj g⁻¹ h
    · exact smul_adj g

@[simp] theorem actionIso_apply (g : G) (v : Vertex α) : actionIso g v = g • v := rfl

/-- Cycles whose inverse translate lies on the chosen set of points. -/
def translatedCycles (s : Finset α) : WalkClosure.Cycles (graph α) :=
  fun _ p => ∃ g : G, p.map (actionIso g⁻¹).toHom ∈ cyclesOn s (g⁻¹ • _)

/-- The walk-map definition is equivalent to translating all supporting pairs. -/
theorem mem_translatedCycles_iff (s : Finset α) {x} (p : (graph α).Walk x x) :
    p ∈ translatedCycles (G := G) s x ↔
      ∃ g : G, ∀ v ∈ p.support, (g⁻¹ • v).val ⊆ s := by
  change (∃ g : G, ∀ v ∈ (p.map (actionIso g⁻¹).toHom).support, v.val ⊆ s) ↔ _
  simp only [Walk.support_map, List.forall_mem_map]
  rfl

/-- Four-transitivity implies transitivity on four-element subsets. -/
theorem exists_smul_finset_eq [MulAction.IsMultiplyPretransitive G α 4]
    (s t : Finset α) (hs : s.card = 4) (ht : t.card = 4) :
    ∃ g : G, g • s = t := by
  let es : s ≃ Fin 4 := Fintype.equivFinOfCardEq (by simpa using hs)
  let et : t ≃ Fin 4 := Fintype.equivFinOfCardEq (by simpa using ht)
  let fs : Fin 4 ↪ α := es.symm.toEmbedding.trans (Function.Embedding.subtype _)
  let ft : Fin 4 ↪ α := et.symm.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G fs ft
  refine ⟨g, ?_⟩
  have hi (i : Fin 4) : g • fs i = ft i := congrArg (fun f : Fin 4 ↪ α => f i) hg
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_smul_finset.mp ha
    have hi' := hi (es ⟨b, hb⟩)
    have : g • b = ft (es ⟨b, hb⟩) := by simpa [fs] using hi'
    rw [this]
    exact (et.symm _).property
  · rw [Finset.card_smul_finset, hs, ht]

/-- Any set of at most four points lies in a translate of the chosen four-set. -/
theorem exists_translate_cover [Finite α] [MulAction.IsMultiplyPretransitive G α 4]
    (s t : Finset α) (hs : s.card = 4) (ht : t.card ≤ 4) :
    ∃ g : G, t ⊆ g • s := by
  classical
  let := Fintype.ofFinite α
  obtain ⟨t', htt', ht'⟩ := Finset.exists_superset_card_eq ht
    (show 4 ≤ Fintype.card α from hs ▸ s.card_le_univ)
  obtain ⟨g, hg⟩ := exists_smul_finset_eq (G := G) s t' hs ht'
  exact ⟨g, hg.symm ▸ htt'⟩

open WalkClosure

/-- Every triangle is supported on at most four underlying points. -/
theorem triangle_support {x : Vertex α} (p : (graph α).Walk x x) (hp : p.length = 3) :
    ∃ t : Finset α, t.card ≤ 4 ∧ p ∈ cyclesOn t x := by
  cases p with
  | nil => simp at hp
  | @cons x a x h₁ p =>
    cases p with
    | nil => simp at hp
    | @cons a b x h₂ p =>
      cases p with
      | nil => simp at hp
      | cons h₃ p =>
        cases p with
        | nil =>
          refine ⟨x.val ∪ a.val ∪ b.val, path_support_card_le_four h₁ h₂, ?_⟩
          intro v hv
          simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl
          · exact Finset.subset_union_left.trans Finset.subset_union_left
          · exact Finset.subset_union_right.trans Finset.subset_union_left
          · exact Finset.subset_union_right
          · exact Finset.subset_union_left.trans Finset.subset_union_left
        | cons h₄ p =>
          simp only [Walk.length_cons] at hp
          omega

/-- Every triangle is a translate of a cycle on the chosen four points. -/
theorem triangle_mem_translatedCycles [Finite α] [MulAction.IsMultiplyPretransitive G α 4]
    (s : Finset α) (hs : s.card = 4) {x} (p : (graph α).Walk x x) (hp : p.length = 3) :
    p ∈ translatedCycles (G := G) s x := by
  obtain ⟨t, ht, hpt⟩ := triangle_support p hp
  obtain ⟨g, hg⟩ := exists_translate_cover (G := G) s t hs ht
  apply (mem_translatedCycles_iff s p).mpr
  refine ⟨g, ?_⟩
  intro v hv
  exact Finset.subset_smul_finset_iff.mp ((hpt v hv).trans hg)

/-- Translates of the cycles on four points form a nonabelian cycle base. -/
theorem fourSubset_isCycleBase [Finite α] [MulAction.IsMultiplyPretransitive G α 4]
    (s : Finset α) (hs : s.card = 4) :
    IsCycleBase (translatedCycles (G := G) s) := by
  apply isCycleBase_of_triangles triangulable
  intro x p hp
  exact .cycle p (triangle_mem_translatedCycles s hs p hp)

/-- A local edge relation containing the induced graph on four points is a base. -/
theorem fourSubset_edge_isCycleBase [Finite α] [MulAction.IsMultiplyPretransitive G α 4]
    (s : Finset α) (hs : s.card = 4) (R : Vertex α → Vertex α → Prop)
    (hR : ∀ {v w}, (graph α).Adj v w → v.val ⊆ s → w.val ⊆ s → R v w) :
    IsCycleBase (Γ := graph α) (fun _ p => ∃ g : G, Supported (fun a b => R (g⁻¹ • a) (g⁻¹ • b)) p) := by
  intro x p
  apply (fourSubset_isCycleBase (G := G) s hs x p).of_generators
  intro y q hq
  obtain ⟨g, hg⟩ := (mem_translatedCycles_iff s q).mp hq
  apply Rel.cycle
  refine ⟨g, ?_⟩
  have aux : ∀ {u v} (r : (graph α).Walk u v),
      (∀ w ∈ r.support, (g⁻¹ • w).val ⊆ s) →
      Supported (fun a b => R (g⁻¹ • a) (g⁻¹ • b)) r := by
    intro u v r hr
    induction r with
    | nil => trivial
    | cons h r ih =>
      refine ⟨hR (smul_adj g⁻¹ h) (hr _ (by simp)) (hr _ (by simp)), ih ?_⟩
      intro w hw
      exact hr w (by simp [hw])
  exact aux q hg
end Theory.Combinatorics.PairGraph
