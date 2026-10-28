module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.OrbitAction.Orbit
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.OrbitAction.NeighborChecks

/-!
# The full neighborhood in the literal Hall–Janko subgroup graph

The checked tree of 36 rows constructs normalizer elements sending the
marked neighbor to every listed vertex. Adjacency is transported from the
existing A₄ edge. An adjacent join has exponent dividing six, whereas the
checked word for each other nonbase row has a nontrivial sixth power.
This excludes every unlisted vertex and proves neighbor transitivity and
valency 36 for the original graph.

Source: Aschbacher, *Sporadic Groups*, 47.5(2) and 47.10, pp.263–267.
All groups, conjugations and joins use the unchanged ATLAS carrier markings.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.OrbitAction
open Subgroup Theory.GroupTheory GeneratorPair FirstFusion Data

theorem inclusion_rep (i : Fin 280) : inclusion (rep i) = permRep i := by
  have hw (w : List (Fin 3)) : inclusion (evalWord letter w) = evalWord permLetter w := by
    induction w with
    | nil => exact map_one _
    | cons s w ih => simp only [evalWord, map_mul, inclusion_letter, ih]
  exact hw _

def normalizerElement (s : Fin 3) : Carrier :=
  let q := normalizerGenerator s
  rep q.1 * letter q.2 * (rep (nextRow q.1 q.2))⁻¹

theorem normalizerElement_mem (s : Fin 3) : normalizerElement s ∈ M :=
  step_mem _ _

theorem inclusion_normalizerElement (s : Fin 3) :
    inclusion (normalizerElement s) = normalizerPerm s := by
  simp only [normalizerElement, normalizerPerm, map_mul, map_inv, inclusion_rep, inclusion_letter]

set_option maxRecDepth 4000 in
theorem neighbor_zero : vertex (neighborRow 0) = neighbor := by
  apply Subtype.ext
  rw [vertex_val]
  change zpowers (element (neighborRow 0)) = zpowers y
  apply congrArg zpowers
  apply inclusion_injective
  apply Equiv.ext
  intro p
  rw [row_spec, neighbor_zero_value]
  have hy : inclusion y = cPerm * xPerm * cPerm⁻¹ := by
    change inclusion (conjugator * x * conjugator⁻¹) = _
    simp only [map_mul, map_inv, inclusion_x, conjugator, cPerm,
      (show inclusion a = tableA from generatorA_eq_table),
      (show inclusion b = tableB from generatorB_eq_table)]
  rw [hy]

theorem neighbor_step (j : Fin 36) (hj : j ≠ 0) :
    normalizerElement (neighborLetter j) • vertex (neighborRow (neighborParent j)) =
      vertex (neighborRow j) := by
  have hc : normalizerElement (neighborLetter j) * element (neighborRow (neighborParent j)) *
      (normalizerElement (neighborLetter j))⁻¹ =
      if neighborFlip j then (element (neighborRow j))⁻¹ else element (neighborRow j) := by
    apply inclusion_injective
    apply Equiv.ext
    intro p
    rw [map_mul, map_mul, map_inv, inclusion_normalizerElement]
    change normalizerPerm (neighborLetter j)
      (inclusion (element (neighborRow (neighborParent j))) ((normalizerPerm (neighborLetter j))⁻¹ p)) = _
    rw [row_spec, ← normalizer_inv_value, ← normalizer_value, ← neighbor_transitions j p hj]
    cases hf : neighborFlip j
    · simp only [Bool.false_eq_true, ↓reduceIte, signedValue, row_spec]
    · simp only [↓reduceIte, ← element_square, pow_two, map_mul, Equiv.Perm.mul_apply,
        row_spec, signedValue]
  apply Subtype.ext
  rw [smul_val, vertex_val, MonoidHom.map_zpowers, vertex_val]
  change zpowers (normalizerElement (neighborLetter j) * element (neighborRow (neighborParent j)) *
    (normalizerElement (neighborLetter j))⁻¹) = _
  rw [hc]
  cases hf : neighborFlip j <;> simp only [↓reduceIte, Bool.false_eq_true, zpowers_inv]

theorem neighbor_reachable (j : Fin 36) :
    ∃ m : M, (m : Carrier) • neighbor = vertex (neighborRow j) := by
  have aux : ∀ n : Nat, ∀ j : Fin 36, j.val = n →
      ∃ m : M, (m : Carrier) • neighbor = vertex (neighborRow j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      by_cases hz : j = 0
      · subst j
        exact ⟨1, by simpa only [OneMemClass.coe_one, one_smul] using neighbor_zero.symm⟩
      obtain ⟨m, hm⟩ := ih (neighborParent j).val (hj ▸ neighbor_tree j hz) (neighborParent j) rfl
      refine ⟨⟨normalizerElement (neighborLetter j), normalizerElement_mem _⟩ * m, ?_⟩
      change (normalizerElement (neighborLetter j) * (m : Carrier)) • neighbor = _
      rw [mul_smul, hm]
      exact neighbor_step j hz
  exact aux j.val j rfl

theorem listed_neighbor_adjacent (j : Fin 36) : graph.Adj base (vertex (neighborRow j)) := by
  obtain ⟨m, hm⟩ := neighbor_reachable j
  have hx : (m : Carrier) • base = base := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [base_stabilizer]
    exact m.property
  simpa only [hx, hm] using preserves (m : Carrier) adjacent

private theorem alternating_four_sixth_power (u : alternatingGroup (Fin 4)) : u ^ 6 = 1 := by
  have h : ∀ u : alternatingGroup (Fin 4), u ^ 6 = 1 := by decide +kernel
  exact h u

private theorem sixth_power_of_adj {A : Vertex} (ha : graph.Adj base A)
    {z : Carrier} (hz : z ∈ base.val ⊔ A.val) : z ^ 6 = 1 := by
  obtain ⟨e⟩ := (graph_adj_iff _ _).mp ha
  have hp : (⟨z, hz⟩ : ↥(base.val ⊔ A.val)) ^ 6 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact alternating_four_sixth_power _
  exact congrArg Subtype.val hp

set_option maxRecDepth 4000 in
/-- The finite exclusion tests apply to the literal subgroup join. -/
theorem adjacent_isNeighbor (i : Fin 280) (ha : graph.Adj base (vertex i)) : isNeighbor i = true := by
  have hi : i ≠ 0 := by
    intro h
    subst i
    have hv : vertex 0 = base := by simp only [vertex, rep_zero, inv_one, one_smul]
    exact ha.1 hv.symm
  by_contra hn
  have hn : isNeighbor i = false := Bool.eq_false_iff.mpr hn
  let z : Carrier := x * if obstructionSign i then element i ^ 2 else element i
  have hz : z ∈ base.val ⊔ (vertex i).val := by
    apply (base.val ⊔ (vertex i).val).mul_mem
    · exact mem_sup_left (mem_zpowers x)
    · apply mem_sup_right
      rw [vertex_val]
      split
      · exact pow_mem (mem_zpowers _) _
      · exact mem_zpowers _
  have hp (p : Fin 100) : inclusion z p = productValue i p := by
    dsimp only [z, productValue]
    rw [map_mul, Equiv.Perm.mul_apply]
    rw [inclusion_x, ← value_zero]
    apply congrArg (value 0)
    cases hb : obstructionSign i
    · simp only [Bool.false_eq_true, ↓reduceIte, signedValue, row_spec]
    · simp only [↓reduceIte, pow_two, map_mul, Equiv.Perm.mul_apply, row_spec, signedValue]
  have he := congrArg (fun u : Carrier => inclusion u (obstructionPoint i)) (sixth_power_of_adj ha hz)
  rw [map_pow, map_one] at he
  simp only [Equiv.Perm.coe_pow] at he
  rw [funext hp] at he
  exact nonneighbor_obstruction i hi hn he

/-- Exhaustive coverage of all neighbors by the orbit of the distinguished edge. -/
theorem neighbors (A : Vertex) (ha : graph.Adj base A) :
    ∃ m : M, (m : Carrier) • neighbor = A := by
  obtain ⟨i, rfl⟩ := vertex_surjective A
  obtain ⟨j, rfl⟩ := (isNeighbor_iff i).mp (adjacent_isNeighbor i ha)
  exact neighbor_reachable j

noncomputable def neighborEquiv : Fin 36 ≃ {A : Vertex // graph.Adj base A} :=
  Equiv.ofBijective (fun j => ⟨vertex (neighborRow j), listed_neighbor_adjacent j⟩)
    ⟨fun i j h => neighbor_rows_injective (vertex_injective (congrArg Subtype.val h)), by
      rintro ⟨A, ha⟩
      obtain ⟨i, hi⟩ := vertex_surjective A
      obtain ⟨j, hj⟩ := (isNeighbor_iff i).mp (adjacent_isNeighbor i (hi ▸ ha))
      exact ⟨j, Subtype.ext (by change vertex (neighborRow j) = A; rw [hj, hi])⟩⟩

theorem card_neighbors : Nat.card {A : Vertex // graph.Adj base A} = 36 := by
  rw [← Nat.card_congr neighborEquiv, Nat.card_fin]

end Sporadic.LeechRelated.J2.RecognitionGeometry.OrbitAction
