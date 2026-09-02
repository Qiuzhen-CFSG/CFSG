module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Theory.GroupAction.Defs
public import Theory.GroupAction.Invariant

open Theory.GroupAction

open scoped Pointwise

namespace Theory.GroupAction

section MinimalSubgroup

variable {G : Type*} [Group G] [Finite G]

/-- Generic minimal-subgroup engine: among the subgroups of `K` satisfying a family `F`,
there is one minimal with respect to inclusion. -/
public theorem exists_minimal_subgroup_of_mem_le (F : Subgroup G → Prop) (K : Subgroup G)
    (hFK : F K) :
    ∃ M : Subgroup G, F M ∧ M ≤ K ∧
      ∀ L : Subgroup G, F L → L ≤ M → L = M := by
  classical
  let Q : Subgroup G → Prop := fun K' =>
    ∃ M : Subgroup G, F M ∧ M ≤ K' ∧
      ∀ L : Subgroup G, F L → L ≤ M → L = M
  have hQ : ∀ n : ℕ, ∀ K' : Subgroup G, F K' → Nat.card K' = n → Q K' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K' hFK' hcard
      by_cases hmin : ∀ L : Subgroup G, F L → L ≤ K' → L = K'
      · refine ⟨K', hFK', le_rfl, hmin⟩
      · push Not at hmin
        rcases hmin with ⟨L, hFL, hLleK', hLneK'⟩
        have hcardL_lt : Nat.card L < n := by
          calc
            Nat.card L < Nat.card K' :=
              lt_of_le_of_ne (Subgroup.card_le_of_le (H := L) (K := K') hLleK') ?_
            _ = n := hcard
          intro hEq
          exact hLneK' (Subgroup.eq_of_le_of_card_ge (H := L) (K := K') hLleK' hEq.symm.le)
        rcases ih (Nat.card L) hcardL_lt L hFL rfl with
          ⟨M, hFM, hMleL, hMmin⟩
        exact ⟨M, hFM, hMleL.trans hLleK', hMmin⟩
  exact hQ (Nat.card K) K hFK rfl

/-- Any family `F` of subgroups of a finite group that contains `⊤` has an inclusion-minimal
member. (If `F` excludes `⊥`, that member is automatically nontrivial.) -/
public theorem exists_minimal_subgroup_of_mem_top (F : Subgroup G → Prop) (hFtop : F ⊤) :
    ∃ M : Subgroup G, F M ∧ ∀ L : Subgroup G, F L → L ≤ M → L = M := by
  rcases exists_minimal_subgroup_of_mem_le (F := F) (K := ⊤) hFtop with
    ⟨M, hFM, _hMleTop, hMmin⟩
  exact ⟨M, hFM, hMmin⟩

end MinimalSubgroup

section MinimalNormalInvariant

variable {G A : Type*} [Group G] [Finite G] [Group A] [MulDistribMulAction A G]

/-- Every nontrivial normal `A`-invariant subgroup contains a minimal one. -/
public theorem exists_minimal_normal_isInvariant_le (K : Subgroup G) (hK : K.Normal)
    [IsInvariant A G K] (hKne : K ≠ ⊥) :
    ∃ M : Subgroup G,
      M.Normal ∧ IsInvariant A G M ∧ M ≠ ⊥ ∧ M ≤ K ∧
        (∀ L : Subgroup G, L.Normal → IsInvariant A G L → L ≠ ⊥ → L ≤ M → L = M) := by
  let F : Subgroup G → Prop := fun L => L.Normal ∧ IsInvariant A G L ∧ L ≠ ⊥
  rcases exists_minimal_subgroup_of_mem_le (F := F) (K := K) ⟨hK, inferInstance, hKne⟩ with
    ⟨M, hM, hMleK, hMmin⟩
  refine ⟨M, hM.1, hM.2.1, hM.2.2, hMleK, ?_⟩
  intro L hLnorm hLinv hLne hLleM
  exact hMmin L ⟨hLnorm, hLinv, hLne⟩ hLleM

/-- Existence of a minimal nontrivial normal `A`-invariant subgroup in a finite nontrivial group. -/
public theorem exists_minimal_normal_isInvariant [Nontrivial G] :
    ∃ M : Subgroup G,
      M.Normal ∧ IsInvariant A G M ∧ M ≠ ⊥ ∧
        (∀ K : Subgroup G, K.Normal → IsInvariant A G K → K ≠ ⊥ → K ≤ M → K = M) := by
  have htopInv : IsInvariant A G (⊤ : Subgroup G) := by
    refine ⟨?_⟩
    intro a g
    simp
  letI : IsInvariant A G (⊤ : Subgroup G) := htopInv
  rcases exists_minimal_normal_isInvariant_le (A := A) (G := G) (K := (⊤ : Subgroup G))
    (hK := (by infer_instance : (⊤ : Subgroup G).Normal))
    (hKne := (by simp : (⊤ : Subgroup G) ≠ ⊥)) with
    ⟨M, hMnorm, hMinv, hMne, hMleTop, hMmin⟩
  exact ⟨M, hMnorm, hMinv, hMne, hMmin⟩

end MinimalNormalInvariant

end Theory.GroupAction
