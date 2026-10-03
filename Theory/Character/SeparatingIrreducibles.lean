module

public import Theory.Character.Completeness

/-!
# Irreducible characters detect nonidentity elements

The irreducible complex characters span all functions on conjugacy classes.
Consequently, if every irreducible character takes its degree at an element,
that element is the identity. The proof applies the spanning statement to the
indicator of the identity class. This is the standard completeness argument
in ordinary character theory.
-/

public section
noncomputable section

/-- Some irreducible character distinguishes a nonidentity element from the identity. -/
theorem exists_irreducibleConjCharacter_ne_degree {G : Type*} [Group G] [Finite G] {g : G} (hg : g ≠ 1) :
    ∃ χ : ConjClassFunction G, IsIrreducibleConjCharacter χ ∧
      χ (ConjClasses.mk g) ≠ χ (ConjClasses.mk 1) := by
  classical
  obtain ⟨ι, hι, χ, hχ, hspan⟩ := classFunction_span_irreducible_characters (G := G)
  let := hι
  by_contra! hnone
  have heq : ∀ f : ConjClassFunction G,
      f (ConjClasses.mk g) = f (ConjClasses.mk 1) := by
    intro f
    have hf : f ∈ Submodule.span ℂ (Set.range χ) := hspan ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hnone _ (hχ.1 i)
    | zero => rfl
    | add x y hx hy hx' hy' => exact congrArg₂ (· + ·) hx' hy'
    | smul a x hx hx' => exact congrArg (a * ·) hx'
  have hclasses : ConjClasses.mk g ≠ ConjClasses.mk 1 := by
    intro he
    exact hg (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp he))
  have := heq (Pi.single (ConjClasses.mk 1) 1)
  simp [hclasses] at this
