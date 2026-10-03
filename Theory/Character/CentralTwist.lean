module

public import Theory.Character.Divisibility

/-!
# Central translates of irreducible characters

A central element acts by a scalar on an irreducible complex representation.
Taking traces gives the character of its translate. Applying the representation
to a power relation shows that the scalar satisfies the same relation.

The proof uses Schur's lemma for the central multiplication intertwiner.
Source: standard complex representation theory; this is the central-element
step in generalized decomposition, as used by Fong, *Some Sylow subgroups of
order 32*, J. Algebra 6 (1967), pp. 73–74.
-/

public section
noncomputable section

/-- A central translate of an irreducible character is a scalar multiple;
the scalar satisfies every power relation of the central element. -/
theorem IsIrreducibleCharacter.exists_central_scalar {G : Type*} [Group G] [Finite G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) {z : G} (hz : z ∈ Subgroup.center G) :
    ∃ c : ℂ, (∀ v, χ (z * v) = c * χ v) ∧
      (∀ n : ℕ, z ^ n = 1 → c ^ n = 1) := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  let := hρ
  let f := Representation.IntertwiningMap.centralMul (ρ := ρ) z hz
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  have hc' : ρ z = c • (1 : Module.End ℂ (Fin n → ℂ)) :=
    (congrArg Representation.IntertwiningMap.toLinearMap hc).symm
  refine ⟨c, ?_, ?_⟩
  · intro v
    simp [Representation.character, map_mul, hc', Algebra.smul_mul_assoc, map_smul]
  · intro k hk
    let : Nontrivial (Fin n → ℂ) := irreducible_nontrivial ρ
    apply (FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ (Fin n → ℂ)))
    simpa [Algebra.algebraMap_eq_smul_one, map_pow, hc', smul_pow] using congrArg ρ hk

