module
public import Theory.GroupAction.Lemmas

/-!
# Commutator modules preserved by a normalizing actor

If B normalizes A, its action preserves [V,A]. Conjugating a commutator
v⁻¹(a • v) by b rewrites it as the commutator of b • v with bab⁻¹∈A.
Closure induction gives forward stability, and acting by b⁻¹ gives the
reverse implication required for an invariant subgroup.

This generic action fact is extracted from the local-family infrastructure
for Stellmacher (1.6), `refs/latex/stellmacher-n-group.tex`, journal p. 18.
It also makes the normalized C₃ sixteen-point calculation available at the
Theory layer without a campaign import.
-/

/-- A subgroup normalizing the actor preserves its action-commutator
module. -/
public theorem commutatorAction_isInvariant_of_normalizing_actor
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (B A : Subgroup G) (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    IsInvariant B V (commutatorAction A V) := by
  have hforward : ∀ g : B, ∀ v : V,
      v ∈ commutatorAction A V → g • v ∈ commutatorAction A V := by
    intro g v hv
    rw [commutatorAction_eq_closure] at hv ⊢
    refine Subgroup.closure_induction
      (p := fun w _ => g • w ∈ Subgroup.closure
        {d : V | ∃ a : A, ∃ v : V, d = v⁻¹ * a • v})
      (x := v) ?_ ?_ ?_ ?_ hv
    · rintro w ⟨a, z, rfl⟩
      let aga : A := ⟨(g : G) * (a : G) * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBA g.property) (a : G)).mp
          a.property⟩
      refine Subgroup.subset_closure ⟨aga, g • z, ?_⟩
      change (g : G) • (z⁻¹ * (a : G) • z) =
        ((g : G) • z)⁻¹ * (aga : G) • ((g : G) • z)
      simp [aga, smul_mul', smul_inv', ← mul_smul, mul_assoc]
    · simp
    · intro y z _ _ hy hz
      simpa [smul_mul'] using
        (Subgroup.closure {d : V | ∃ a : A, ∃ v : V,
          d = v⁻¹ * a • v}).mul_mem hy hz
    · intro y _ hy
      simpa [smul_inv'] using
        (Subgroup.closure {d : V | ∃ a : A, ∃ v : V,
          d = v⁻¹ * a • v}).inv_mem hy
  constructor
  intro g v
  constructor
  · exact hforward g v
  · intro hgv
    have := hforward g⁻¹ (g • v) hgv
    simpa [inv_smul_smul] using this
