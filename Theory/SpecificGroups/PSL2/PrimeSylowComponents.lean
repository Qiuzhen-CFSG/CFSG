module
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Theory.SpecificGroups.PSL2.PrimeCubicRank
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.GroupTheory.CComponent.SylowOvergroupUniqueExtensions

/-!
# Full-Sylow component tests in odd-prime PSL₂

Dickson's theorem makes every nonsolvable proper subgroup A₅. Consequently
three-free subgroups are solvable, and proper subgroups have at most one
C-component. The inherited top C-component supplies uniqueness in the whole
group. These tests close the odd-prime containing-pair row in Chapter 10,
without assuming distinct containing components or a cubic divisor.
Source: Aschbacher--Smith A.3.12(8) and 10.2.6, pp.47--48,748--749.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2.PrimeSylowComponents
variable {F : Type} [Field F] [Finite F] {p : ℕ}

/-- No three-free nonsolvable subgroup occurs in an odd-prime projective line group. -/
theorem isSolvable_of_three_free (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (A : Subgroup PSL(2,F)) (h3 : ¬ 3 ∣ Nat.card A) : Group.IsSolvable A := by
  classical
  by_contra hn
  let : Fact p.Prime := ⟨hp⟩
  by_cases ht : A = ⊤
  · apply h3
    rw [ht,card_top]
    exact prime_model_three_dvd_card hp ho hF (MulEquiv.refl _)
  obtain ⟨_,_,⟨e⟩⟩ := prime_nonsolvable_proper_is_alternating_five ho hF A ht hn
  apply h3
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The actual prime-field subgroup classification proves full-Sylow component uniqueness. -/
theorem sylow_unique (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (htop : (⊤ : Subgroup PSL(2,F)).IsCComponent) : SylowOvergroupComponentUnique PSL(2,F) := by
  intro S P hSP B C hB hC
  by_cases ht : P = ⊤
  · subst P
    exact (htop.eq_top_of_isCComponent hB).trans (htop.eq_top_of_isCComponent hC).symm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨_,_,⟨e⟩⟩ := prime_nonsolvable_proper_is_alternating_five ho hF P ht (by
    intro h
    let := h
    exact hB.not_isSolvable inferInstance)
  have hb : B = ⊤ := by
    by_contra hn
    exact hB.not_isSolvable (alternatingGroup.isSolvable_subgroup_of_equiv_five e B hn)
  have hc : C = ⊤ := by
    by_contra hn
    exact hC.not_isSolvable (alternatingGroup.isSolvable_subgroup_of_equiv_five e C hn)
  exact hb.trans hc.symm

end Theory.PSL2.PrimeSylowComponents
