module

public import Theory.GroupAction.TypedCosetGeometry.Residues.Connectivity

/-!
# Rank-two coset geometry

The two types are `false` and `true`. Vertices are the disjoint union of the
two coset spaces, with incidence given by a common representative. We reuse
the typed-coset construction and prove orbit, edge and local transitivity.
Generation is needed only for connectedness; the ambient group may be infinite.

The library uses left cosets and a left action. `rightVertex F i x` represents
the source right coset `(F i) x` by its inverse left coset `x⁻¹ (F i)`.
The right-translation and intersection lemmas below verify this convention,
including the source conjugate `x⁻¹ (F i) x` for its stabilizer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), F.7.2 and F.7.3(1)–(5), printed pp.311–312.
The second coset in the adjacency formula in F.7.2 has the opposite type.
-/

@[expose] public section

namespace Subgroup.CosetGeometry.RankTwo

open scoped Pointwise

variable {G : Type*} [Group G] (F : Bool → Subgroup G)

abbrev Vertex := CosetGeometry.Vertex F
abbrev graph := incidenceGraph F
abbrev base := CosetGeometry.base F
abbrev stabilizer (v : Vertex F) := MulAction.stabilizer G v

/-- The typed vertex construction is the disjoint union of the two coset spaces. -/
def vertexEquivSum : Vertex F ≃ (G ⧸ F false) ⊕ (G ⧸ F true) where
  toFun v := match v with
    | ⟨false, q⟩ => Sum.inl q
    | ⟨true, q⟩ => Sum.inr q
  invFun v := match v with
    | Sum.inl q => ⟨false, q⟩
    | Sum.inr q => ⟨true, q⟩
  left_inv v := by rcases v with ⟨i, q⟩; cases i <;> rfl
  right_inv v := by cases v <;> rfl

/-- The two fibers of the type map are exactly the two vertex orbits. -/
theorem same_orbit_iff (v w : Vertex F) :
    (∃ g : G, g • v = w) ↔ v.type = w.type := by
  constructor
  · rintro ⟨g, rfl⟩; rfl
  · intro h
    obtain ⟨a, ha⟩ := exists_smul_base F v
    obtain ⟨b, hb⟩ := exists_smul_base F w
    refine ⟨b * a⁻¹, ?_⟩
    rw [mul_smul, ← ha, inv_smul_smul, h, hb]

/-- An incident ordered pair is a translate of its two standard vertices. -/
theorem incident_common_translate {v w : Vertex F} (h : Incident F v w) :
    ∃ g : G, g • base F v.type = v ∧ g • base F w.type = w := by
  obtain ⟨g, hv, hw⟩ := h
  refine ⟨g, ?_, ?_⟩
  · rcases v with ⟨i, q⟩
    change CosetGeometry.Vertex.mk i (g • ((1 : G) : G ⧸ F i)) = _
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using
      congrArg (CosetGeometry.Vertex.mk i) hv
  · rcases w with ⟨i, q⟩
    change CosetGeometry.Vertex.mk i (g • ((1 : G) : G ⧸ F i)) = _
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using
      congrArg (CosetGeometry.Vertex.mk i) hw

/-- Unordered edges form a single orbit, including the standard edge. -/
theorem edge_transitive {v w : Vertex F} (h : (graph F).Adj v w) :
    ∃ g : G, ({v, w} : Set (Vertex F)) = {g • base F false, g • base F true} := by
  obtain ⟨g, hv, hw⟩ := incident_common_translate F h.2
  refine ⟨g, ?_⟩
  have ht := h.1
  cases hi : v.type <;> cases hj : w.type
  · exact (ht (hi.trans hj.symm)).elim
  · rw [hi] at hv; rw [hj] at hw; rw [hv, hw]
  · rw [hi] at hv; rw [hj] at hw; rw [hv, hw, Set.pair_comm]
  · exact (ht (hi.trans hj.symm)).elim

/-- An action preserving the two types cannot invert an edge. -/
theorem fixes_edge_iff {v w : Vertex F} (h : (graph F).Adj v w) (g : G) :
    ({g • v, g • w} : Set (Vertex F)) = {v, w} ↔ g • v = v ∧ g • w = w := by
  constructor
  · intro he
    have hv : g • v ∈ ({v, w} : Set (Vertex F)) := by rw [← he]; simp
    have hw : g • w ∈ ({v, w} : Set (Vertex F)) := by rw [← he]; simp
    have hv' : g • v = v := by
      rcases Set.mem_insert_iff.mp hv with hv | hv
      · exact hv
      · have ht : (g • v).type = w.type :=
          congrArg (fun t : Vertex F => t.type) (Set.mem_singleton_iff.mp hv)
        exact (h.1 ht).elim
    have hw' : g • w = w := by
      rcases Set.mem_insert_iff.mp hw with hw | hw
      · exact (h.1 (congrArg CosetGeometry.Vertex.type hw).symm).elim
      · exact Set.mem_singleton_iff.mp hw
    exact ⟨hv', hw'⟩
  · rintro ⟨hv, hw⟩; rw [hv, hw]

/-- The setwise stabilizer of the standard unordered edge is the intersection. -/
theorem base_edge_stabilizer (g : G) :
    ({g • base F false, g • base F true} : Set (Vertex F)) =
      {base F false, base F true} ↔ g ∈ F false ⊓ F true := by
  rw [fixes_edge_iff F ⟨Bool.false_ne_true, incident_base F false true⟩]
  change g ∈ stabilizer F (base F false) ∧ g ∈ stabilizer F (base F true) ↔ _
  simp only [stabilizer, base, stabilizer_base, mem_inf]

/-- The actual setwise stabilizer of an unordered edge equals its pointwise stabilizer. -/
theorem edge_stabilizer {v w : Vertex F} (h : (graph F).Adj v w) :
    MulAction.stabilizer G ({v, w} : Set (Vertex F)) = stabilizer F v ⊓ stabilizer F w := by
  ext g
  change g • ({v, w} : Set (Vertex F)) = {v, w} ↔ _
  rw [Set.smul_set_insert, Set.smul_set_singleton, fixes_edge_iff F h g]
  rfl

/-- Stabilizers at arbitrary cosets are actual conjugate subgroups. -/
theorem stabilizer_translate (g : G) (v : Vertex F) :
    stabilizer F (g • v) = (stabilizer F v).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g v

/-- Generation by the two vertex groups gives connectedness. -/
theorem connected (hgen : F false ⊔ F true = ⊤) : (graph F).Connected := by
  apply incidenceGraph_connected F
  simpa only [iSup_bool_eq, sup_comm] using hgen

/-- Neighbors of a vertex form one orbit of its stabilizer. -/
theorem locally_transitive {v w z : Vertex F}
    (hw : (graph F).Adj v w) (hz : (graph F).Adj v z) :
    ∃ g ∈ stabilizer F v, g • w = z := by
  obtain ⟨a, hav, haw⟩ := incident_common_translate F hw.2
  obtain ⟨b, hbv, hbz⟩ := incident_common_translate F hz.2
  have htypes : w.type = z.type := by
    have h₁ := hw.1
    have h₂ := hz.1
    cases hi : v.type <;> cases hj : w.type <;> cases hk : z.type <;> simp_all
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · change (b * a⁻¹) • v = v
    calc
      (b * a⁻¹) • v = b • (a⁻¹ • v) := mul_smul _ _ _
      _ = b • (a⁻¹ • (a • base F v.type)) :=
        congrArg (fun t : Vertex F => b • (a⁻¹ • t)) hav.symm
      _ = v := by rw [inv_smul_smul, hbv]
  · rw [mul_smul, ← haw, inv_smul_smul, htypes, hbz]

/-- The common normal core is the kernel on all vertices. -/
theorem global_kernel :
    (MulAction.toPermHom G (Vertex F)).ker = (F false ⊓ F true).normalCore := by
  rw [action_kernel]
  simp only [iInf_bool_eq, inf_comm]

/-- The source right coset `(F i) x`, expressed in the left-coset vertex type. -/
def rightVertex (i : Bool) (x : G) : Vertex F := x⁻¹ • base F i

/-- Right multiplication in the source is inverse left multiplication here. -/
theorem rightVertex_mul (i : Bool) (x g : G) :
    rightVertex F i (x * g) = g⁻¹ • rightVertex F i x := by
  simp only [rightVertex, mul_inv_rev, mul_smul]

/-- Fixing a source right coset under right multiplication agrees with its stabilizer here. -/
theorem rightVertex_mul_eq_iff (i : Bool) (x g : G) :
    rightVertex F i (x * g) = rightVertex F i x ↔
      g ∈ stabilizer F (rightVertex F i x) := by
  rw [rightVertex_mul]
  change g⁻¹ ∈ stabilizer F (rightVertex F i x) ↔ g ∈ stabilizer F (rightVertex F i x)
  exact (stabilizer F (rightVertex F i x)).inv_mem_iff

/-- Equality in a source right-coset space has the literal right-coset criterion. -/
theorem rightVertex_eq_iff (i : Bool) (x y : G) :
    rightVertex F i x = rightVertex F i y ↔ x * y⁻¹ ∈ F i := by
  change CosetGeometry.Vertex.mk i (x⁻¹ • ((1 : G) : G ⧸ F i)) =
    CosetGeometry.Vertex.mk i (y⁻¹ • ((1 : G) : G ⧸ F i)) ↔ _
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
    CosetGeometry.Vertex.mk.injEq, heq_eq_eq, true_and, QuotientGroup.eq, inv_inv]

/-- The corrected F.7.2 adjacency formula is intersection of opposite right cosets. -/
theorem rightVertex_adj_iff (i j : Bool) (x y : G) :
    (graph F).Adj (rightVertex F i x) (rightVertex F j y) ↔
      i ≠ j ∧ ∃ z : G, z * x⁻¹ ∈ F i ∧ z * y⁻¹ ∈ F j := by
  change (i ≠ j ∧ Incident F (rightVertex F i x) (rightVertex F j y)) ↔ _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨z, hx, hy⟩
    refine ⟨z⁻¹, ?_, ?_⟩
    · change (z : G ⧸ F i) = (x⁻¹ • ((1 : G) : G ⧸ F i)) at hx
      simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
        QuotientGroup.eq] using hx
    · change (z : G ⧸ F j) = (y⁻¹ • ((1 : G) : G ⧸ F j)) at hy
      simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
        QuotientGroup.eq] using hy
  · rintro ⟨z, hx, hy⟩
    refine ⟨z⁻¹, ?_, ?_⟩
    · change ((z⁻¹ : G) : G ⧸ F i) = (x⁻¹ • ((1 : G) : G ⧸ F i))
      simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
        QuotientGroup.eq, inv_inv] using hx
    · change ((z⁻¹ : G) : G ⧸ F j) = (y⁻¹ • ((1 : G) : G ⧸ F j))
      simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
        QuotientGroup.eq, inv_inv] using hy

/-- The book's `G_i^x` is the stabilizer `x⁻¹ G_i x`. -/
theorem stabilizer_rightVertex (i : Bool) (x : G) :
    stabilizer F (rightVertex F i x) = (F i).map (MulAut.conj x⁻¹).toMonoidHom := by
  rw [rightVertex, stabilizer_translate]
  simp only [stabilizer, base, stabilizer_base]

end Subgroup.CosetGeometry.RankTwo
