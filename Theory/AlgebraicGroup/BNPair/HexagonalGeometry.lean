module

public import Theory.AlgebraicGroup.BNPair.DihedralGeometry

/-!
# The coset geometry of a marked hexagonal Tits system

`HexagonalDatum` identifies the actual Weyl quotient with the dihedral group
of order twelve, marks its two simple reflections, and identifies the vertex
subgroups with the corresponding standard parabolics. It has no geometric
assumptions. Vertices, incidence, the group action and the normalizer apartment
are those of `DihedralGeometry`.

Bruhat decomposition supplies apartment coverage. The rank-one Bruhat cells
identify normalizer vertices, and a twelve-cycle apartment gives diameter six.
The construction, girth and cycle-conjugacy proofs are in the descendants.

Adapted from the checked octagonal development in `BNPair.DihedralGeometry`.
Source: the BN-pair and parabolic construction in GLS3 §§2.3 and 2.6,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section

namespace Theory.AlgebraicGroup.TitsSystem.HexagonalGeometry

open Subgroup DihedralGeometry
open scoped Pointwise

variable {X I : Type*} [Group X]

/-- The standard normalizer orbit is the support of a simple twelve-cycle. -/
def StandardApartmentCycle (T : TitsSystem (X := X)) (F : I → Subgroup X) : Prop :=
  ∃ v, ∃ p : (graph F).Walk v v,
    p.IsCycle ∧ p.length = 12 ∧ {w | w ∈ p.support} = apartment T F

/-- Algebraic marking of a hexagonal Weyl quotient and its two parabolics. -/
structure HexagonalDatum (T : TitsSystem (X := X)) (F : I → Subgroup X) where
  typeEquiv : I ≃ Bool
  simple : I → (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N)
  simple_range : Set.range simple = T.S
  weylEquiv : (T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) ≃* DihedralGroup 6
  map_simple : ∀ i, weylEquiv (simple i) =
    DihedralGroup.sr (if typeEquiv i then 1 else 0)
  parabolic_eq : ∀ i, F i = T.standardParabolic {simple i}

variable (F : I → Subgroup X) (T : TitsSystem (X := X))

/-- Once the normalizer orbit is a twelve-cycle, Bruhat coverage gives the
required diameter bound on the entire coset graph. -/
theorem diameter_bound_of_standardApartmentCycle (hB : ∀ i, T.B ≤ F i)
    (hA : StandardApartmentCycle T F) (v w : CosetGeometry.Vertex F) :
    ∃ p : (graph F).Walk v w, p.length ≤ 6 := by
  classical
  obtain ⟨k, hv, hw⟩ := exists_apartment_for_vertices F T hB v w
  obtain ⟨v', hv', rfl⟩ := Set.mem_smul_set.mp hv
  obtain ⟨w', hw', rfl⟩ := Set.mem_smul_set.mp hw
  obtain ⟨a, c, _, hlen, hsupp⟩ := hA
  rw [← hsupp] at hv' hw'
  let q := c.rotate v' hv'
  have hwq : w' ∈ q.support := by
    exact (c.mem_support_rotate_iff v' hv').mpr hw'
  have hsum : (q.takeUntil w' hwq).length + (q.dropUntil w' hwq).length = 12 := by
    rw [← SimpleGraph.Walk.length_append, q.take_spec hwq]
    simpa only [q, SimpleGraph.Walk.length_rotate] using hlen
  have hshort : ∃ p : (graph F).Walk v' w', p.length ≤ 6 := by
    by_cases hle : (q.takeUntil w' hwq).length ≤ 6
    · exact ⟨q.takeUntil w' hwq, hle⟩
    · refine ⟨(q.dropUntil w' hwq).reverse, ?_⟩
      rw [SimpleGraph.Walk.length_reverse]
      omega
  obtain ⟨p, hp⟩ := hshort
  refine ⟨(p.map (smulHom F k)).copy (smulHom_apply F k v') (smulHom_apply F k w'), ?_⟩
  simpa only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map] using hp

variable {F T}

namespace HexagonalDatum

variable (D : HexagonalDatum T F)

theorem simple_mem (i : I) : D.simple i ∈ T.S := by
  rw [← D.simple_range]
  exact ⟨i, rfl⟩

include D in
theorem borel_le (i : I) : T.B ≤ F i := by
  rw [D.parabolic_eq]
  exact T.B_le_standardParabolic _

/-- Distinct vertex types have distinct marked simple reflections. -/
theorem simple_injective : Function.Injective D.simple := by
  intro i j hij
  apply D.typeEquiv.injective
  have h := congrArg D.weylEquiv hij
  rw [D.map_simple, D.map_simple] at h
  cases hi : D.typeEquiv i <;> cases hj : D.typeEquiv j <;> simp_all
  all_goals exact absurd h (by decide)

/-- The rank-one Weyl subgroup contains exactly the identity and its marked
reflection. -/
theorem mem_closure_simple_iff (i : I)
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    w ∈ closure ({D.simple i} : Set _) ↔ w = 1 ∨ w = D.simple i := by
  constructor
  · intro hw
    have hs2 := (T.involutions _ (D.simple_mem i)).2
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact Or.inr (Set.mem_singleton_iff.mp hx)
    | one => exact Or.inl rfl
    | mul a b ha hb iha ihb =>
      rcases iha with rfl | rfl <;> rcases ihb with rfl | rfl
      all_goals simp_all [pow_two]
    | inv a ha iha =>
      rcases iha with rfl | rfl
      all_goals simp_all [pow_two, mul_eq_one_iff_inv_eq]
  · rintro (rfl | rfl)
    · exact (closure _).one_mem
    · exact subset_closure (Set.mem_singleton _)

/-- The vertex subgroup is precisely the union of its two Bruhat cells. -/
theorem mem_parabolic_iff (i : I) (x : X) :
    x ∈ F i ↔ x ∈ T.B ∨ x ∈ T.bruhatCell (D.simple i) := by
  rw [D.parabolic_eq, T.mem_standardParabolic_iff
    (Set.singleton_subset_iff.mpr (D.simple_mem i))]
  simp only [D.mem_closure_simple_iff, or_and_right, exists_or, exists_eq_left, T.bruhatCell_one]
  rfl

include D in
/-- The stabilizer of a standard chamber is exactly the Borel subgroup. -/
theorem parabolic_inf_eq_borel (i j : I) (hne : i ≠ j) : F i ⊓ F j = T.B := by
  apply le_antisymm
  · intro x hx
    rcases (D.mem_parabolic_iff i x).mp hx.1 with h | h
    · exact h
    rcases (D.mem_parabolic_iff j x).mp hx.2 with h' | h'
    · exact h'
    exact (hne (D.simple_injective (T.doubleCoset_index_unique h h'))).elim
  · exact le_inf (D.borel_le i) (D.borel_le j)

/-- A normalizer representative belongs to a vertex subgroup exactly when
its Weyl class belongs to the corresponding rank-one subgroup. -/
theorem representative_mem_parabolic_iff (i : I) (n : T.N) :
    (n : X) ∈ F i ↔
      QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n = 1 ∨
      QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n = D.simple i := by
  have hn := T.representative_mem_bruhatCell _ n rfl
  rw [D.mem_parabolic_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (T.doubleCoset_index_unique hn (by
        change (n : X) ∈ T.bruhatCell 1
        rwa [T.bruhatCell_one]))
    · exact Or.inr (T.doubleCoset_index_unique hn h)
  · rintro (h | h)
    · exact Or.inl (by simpa [h] using hn)
    · exact Or.inr (by simpa [h] using hn)

/-- Equality of apartment vertices is tested in the marked dihedral quotient,
with the inverse-left convention for the genuine left cosets. -/
theorem normalizer_smul_base_eq_iff (i : I) (n n' : T.N) :
    (n : X) • CosetGeometry.base F i = (n' : X) • CosetGeometry.base F i ↔
      D.weylEquiv (QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) (n⁻¹ * n')) = 1 ∨
      D.weylEquiv (QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) (n⁻¹ * n')) =
        DihedralGroup.sr (if D.typeEquiv i then 1 else 0) := by
  rw [smul_base_eq_iff]
  change (↑(n⁻¹ * n') : X) ∈ F i ↔ _
  rw [D.representative_mem_parabolic_iff]
  rw [← D.map_simple i, ← D.weylEquiv.map_one, D.weylEquiv.injective.eq_iff,
    D.weylEquiv.injective.eq_iff]

end HexagonalDatum
end Theory.AlgebraicGroup.TitsSystem.HexagonalGeometry
