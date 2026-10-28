module

public import Theory.AlgebraicGroup.RootSystems.Weyl

universe u

namespace Theory.AlgebraicGroup

section

variable {ι M N : Type*} [Finite ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {P : RootPairing ι ℝ M N} [P.IsRootSystem]
  [P.IsCrystallographic] [P.IsReduced]

/-- Membership in a standard Weyl-parabolic subgroup recovers the simple
reflection support: no simple reflection outside `J` lies in `W_J`. -/
public lemma RootPairing.Base.simpleReflection_mem_parabolicSubgroup_iff
    (b : P.Base) (J : Set b.support) (j : b.support) :
    b.simpleReflection j ∈ b.parabolicSubgroup J ↔ j ∈ J := by
  constructor
  · intro hj
    have hlen : b.wordLength (b.simpleReflection j) = 1 := by
      have hpos : b.IsPos (P.weylGroupToPerm (1 : P.weylGroup) j) := by
        simpa using b.isPos_of_mem_support j.property
      have h := (wordLength_simpleReflection_iff_isPositive
        b (1 : P.weylGroup) j).1.2 hpos
      simpa [b.wordLength_one] using h
    have hprod : b.wordProd [j] = b.simpleReflection j := by
      simp [RootPairing.Base.wordProd]
    exact b.minimal_word_mem_parabolic_iff J (b.simpleReflection j) hj
      [j] hlen.symm hprod j (by simp)
  · intro hj
    exact Subgroup.subset_closure ⟨j, hj, rfl⟩

/-- The standard Weyl-parabolic construction is order-reflecting. -/
public lemma RootPairing.Base.parabolicSubgroup_le_iff
    (b : P.Base) (J K : Set b.support) :
    b.parabolicSubgroup J ≤ b.parabolicSubgroup K ↔ J ⊆ K := by
  constructor
  · intro h j hj
    apply (simpleReflection_mem_parabolicSubgroup_iff b K j).1
    exact h (show b.simpleReflection j ∈ b.parabolicSubgroup J from
      Subgroup.subset_closure ⟨j, hj, rfl⟩)
  · intro h
    apply Subgroup.closure_mono
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, h hj, rfl⟩

/-- The standard Weyl-parabolic construction is injective on simple-root
subsets. -/
public lemma RootPairing.Base.parabolicSubgroup_eq_iff
    (b : P.Base) (J K : Set b.support) :
    b.parabolicSubgroup J = b.parabolicSubgroup K ↔ J = K := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · exact (parabolicSubgroup_le_iff b J K).mp (h ▸ le_rfl)
    · exact (parabolicSubgroup_le_iff b K J).mp (h ▸ le_rfl)
  · intro h
    subst K
    rfl

end

end Theory.AlgebraicGroup
