module

public import Theory.AlgebraicGroup.RootData.RelativeRoots

universe u v

/-!
The descending subgroup series defined by relative-root height.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def RelativeRootSeries
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) {ι : Type v} [Finite ι]
    (e : D.Root ≃ ι) (base : Finset ι) (coeff : ι → ι → ℤ)
    (J : Set D.Root) (i : ℕ) : Subgroup (Variety.Point K) :=
  RootSubgroupGenerated D
    {α | (i : ℤ) ≤ RelativeRootHeight coeff base (e '' J) (e α)}

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_antitone
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) {ι : Type v} [Fintype ι]
    (e : D.Root ≃ ι) (base : Finset ι) (coeff : ι → ι → ℤ)
    (J : Set D.Root) :
    Antitone (RelativeRootSeries D e base coeff J) := by
  intro i j hij
  rw [RelativeRootSeries, RelativeRootSeries, RootSubgroupGenerated, RootSubgroupGenerated]
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨α, hα, hx⟩ := hx
  have hij' : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
  exact ⟨α, hij'.trans hα, hx⟩

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public theorem relativeRootSeries_eq_bot_of_height_lt
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) {ι : Type v} [Fintype ι]
    (e : D.Root ≃ ι) (base : Finset ι) (coeff : ι → ι → ℤ)
    (J : Set D.Root) (i : ℕ)
    (hi : ∀ α, RelativeRootHeight coeff base (e '' J) (e α) < (i : ℤ)) :
    RelativeRootSeries D e base coeff J i = ⊥ := by
  have hroots :
      {α | (i : ℤ) ≤ RelativeRootHeight coeff base (e '' J) (e α)} = ∅ := by
    ext α
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    exact iff_false_intro (not_le.mpr (hi α))
  rw [RelativeRootSeries, hroots, RootSubgroupGenerated]
  simp

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- A root-set identification at relative height one gives the corresponding
first relative-root subgroup identification. -/
public theorem relativeRootSeries_one_eq_of_root_set_eq
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) {ι : Type v} [Fintype ι]
    (e : D.Root ≃ ι) (base : Finset ι) (coeff : ι → ι → ℤ)
    (J : Set D.Root) (roots : Set D.Root)
    (U : Subgroup (Variety.Point K))
    (hroots : {α | (1 : ℤ) ≤ RelativeRootHeight coeff base (e '' J) (e α)} = roots)
    (hU : U = RootSubgroupGenerated D roots) :
    RelativeRootSeries D e base coeff J 1 = U := by
  rw [RelativeRootSeries]
  change RootSubgroupGenerated D
    {α | (1 : ℤ) ≤ RelativeRootHeight coeff base (e '' J) (e α)} = U
  rw [hroots, ← hU]

end

end Theory.AlgebraicGroup
