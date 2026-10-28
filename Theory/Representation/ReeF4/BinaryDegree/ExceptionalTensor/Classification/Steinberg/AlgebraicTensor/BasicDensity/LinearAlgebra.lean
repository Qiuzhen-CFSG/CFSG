module

public import Theory.Representation.JacobsonDensity

/-!
# Linear algebra for the short-root density argument

A nilpotent family of operators has a nonzero common-kernel vector in each
nonzero invariant subspace: keep applying a generator until the last nonzero
word. Irreducibility of the generated algebra then implies full associative
algebra density over an algebraically closed field by Jacobson density.

These lemmas supply the linear-algebra steps of Steinberg, *Representations
of Algebraic Groups* (1963), proof 11.1(1). They do not assume or establish
restricted-module classification.
-/

public section

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- An irreducible family of endomorphisms generates the full endomorphism
algebra over an algebraically closed field. -/
theorem adjoin_eq_top_of_irreducible [IsAlgClosed F] [FiniteDimensional F V] [Nontrivial V]
    (X : ι → Module.End F V)
    (hirr : ∀ W : Submodule F V, (∀ i v, v ∈ W → X i v ∈ W) →
      W = ⊥ ∨ W = ⊤) : Algebra.adjoin F (Set.range X) = ⊤ := by
  let A := Algebra.adjoin F (Set.range X)
  let : IsSimpleModule A V := by
    rw [isSimpleModule_iff, isSimpleOrder_iff]
    refine ⟨inferInstance, ?_⟩
    intro W
    have hW (i : ι) (v : V) (hv : v ∈ W.restrictScalars F) :
        X i v ∈ W.restrictScalars F :=
      W.smul_mem (⟨X i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : A) hv
    rcases hirr (W.restrictScalars F) hW with h | h
    · left
      apply le_bot_iff.mp
      intro v hv
      have : v ∈ W.restrictScalars F := hv
      simpa [h] using this
    · right
      apply top_unique
      intro v hv
      have : v ∈ W.restrictScalars F := by rw [h]; trivial
      exact this
  apply Algebra.eq_top_iff.mpr
  intro T
  obtain ⟨a, ha⟩ :=
    Representation.jacobson_density_surjective_isAlgClosed (F := F) (A := A) (V := V) T
  have heq : (a : Module.End F V) = T := ha
  exact heq ▸ a.property

/-- Every word in operators preserving a subspace also preserves it. -/
theorem word_apply_mem (X : ι → Module.End F V) (W : Submodule F V)
    (hW : ∀ i v, v ∈ W → X i v ∈ W)
    (l : List ι) {v : V} (hv : v ∈ W) : (l.map X).prod v ∈ W := by
  induction l with
  | nil => simpa using hv
  | cons i l ih => simpa using hW i _ ih

/-- A nonzero vector annihilated by all words of a fixed length yields a
nonzero primitive vector in the same invariant subspace. -/
theorem exists_primitive_of_word_annihilation (X : ι → Module.End F V) (W : Submodule F V)
    (hW : ∀ i v, v ∈ W → X i v ∈ W)
    (n : ℕ) {v : V} (hvW : v ∈ W) (hv : v ≠ 0)
    (hkill : ∀ l : List ι, l.length = n → (l.map X).prod v = 0) :
    ∃ u ∈ W, u ≠ 0 ∧ ∀ i, X i u = 0 := by
  induction n generalizing v with
  | zero =>
    have hz := hkill [] rfl
    exact (hv (by simpa using hz)).elim
  | succ n ih =>
    by_cases h : ∀ i, X i v = 0
    · exact ⟨v, hvW, hv, h⟩
    · push Not at h
      obtain ⟨i, hi⟩ := h
      apply ih (hW i v hvW) hi
      intro l hl
      have hz := hkill (l ++ [i]) (by simp [hl])
      simpa only [List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, Module.End.mul_apply] using hz
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
