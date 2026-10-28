module

public import Theory.Character.Multiplicity

/-!
# Completeness from the sum of squared degrees

A nonredundant family of genuine irreducible characters is complete when its
squared degrees sum to the group order. Embed it in a complete family; any
omitted row would contribute a strictly positive squared degree.
-/

open scoped BigOperators

/-- The degree-square equality detects completeness of an irreducible family. -/
public theorem completeIrreducibleFamily_of_sum_degree_normSq
    {G : Type*} [Group G] [Finite G] {I : Type*} [Fintype I]
    (χ : I → ConjClassFunction G)
    (hirr : ∀ i, IsIrreducibleConjCharacter (χ i))
    (hinj : Function.Injective χ)
    (hs : ∑ i, Complex.normSq (χ i (ConjClasses.mk 1)) = (Nat.card G : ℝ)) :
    IsCompleteIrreducibleCharacterFamily χ := by
  classical
  obtain ⟨J, hJ, θ, hθ, ht⟩ :=
    exists_completeIrreducibleCharacterFamily_sum_degree_normSq (G := G)
  let := hJ
  choose f hf using fun i => hθ.2.1 (χ i) (hirr i)
  have hfi : Function.Injective f := by
    intro i j he
    apply hinj
    rw [← hf i, ← hf j, he]
  have hs' : ∑ j ∈ Finset.univ.image f,
      Complex.normSq (θ j (ConjClasses.mk 1)) = (Nat.card G : ℝ) := by
    rw [Finset.sum_image (fun i _ j _ he => hfi he)]
    simpa only [hf] using hs
  have hsurj : Function.Surjective f := by
    intro j
    by_contra hn
    have hnot : j ∉ Finset.univ.image f := by simpa using hn
    have hpos : 0 < Complex.normSq (θ j (ConjClasses.mk 1)) := by
      apply Complex.normSq_pos.mpr
      intro hz
      have hp := (hθ.1 j).degree_re_pos
      rw [hz, Complex.zero_re] at hp
      exact lt_irrefl _ hp
    have hlt := Finset.sum_lt_sum_of_subset
      (Finset.subset_univ (Finset.univ.image f)) (Finset.mem_univ j) hnot hpos
      (fun k _ _ => Complex.normSq_nonneg (θ k (ConjClasses.mk 1)))
    rw [hs', ht] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hirr, ?_, hinj⟩
  intro φ hφ
  obtain ⟨j, hj⟩ := hθ.2.1 φ hφ
  obtain ⟨i, rfl⟩ := hsurj j
  exact ⟨i, (hf i).symm.trans hj⟩
