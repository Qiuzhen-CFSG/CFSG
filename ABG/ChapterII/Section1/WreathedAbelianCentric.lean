module
public import ABG.ChapterII.Section1.WreathedOuterCentralizers
public import Theory.GroupTheory.SpecificGroups.AbelianTwoFactorAut

/-!
# Abelian centric subgroups of a wreathed group

An abelian subgroup `X` of the chosen wreathed presentation whose ambient
centralizer lies in `X` and whose automorphism group is not a two-group equals
the base `U`. This proves the abelian branch of Alperin--Brauer--Gorenstein,
Chapter II Section 1 Lemma 3(i), article p.10.

If `X` lies in `U`, commutativity of the base and centricity force equality.
Otherwise choose an element of `X` outside `U`. Its centralizer is abelian
by the outer-centralizer models, so it lies in the centralizer of `X` and
centricity again forces equality. The two possible models are cyclic and
`C_(2^n) x C_2`. Their automorphism groups are two-groups, using `n >= 2`
from the presentation to exclude the equal-factor Klein four case.
-/

open scoped IsMulCommutative
namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

/-- The abelian alternative in the exceptional centric subgroup criterion. -/
public theorem abelian_centric_exception_eq_U (X : Subgroup S)
    (hc : Subgroup.centralizer (X : Set S) ≤ X) (hab : IsMulCommutative X)
    (hAut : ¬ IsPGroup 2 (MulAut X)) : X = P.U := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  let := hab
  by_cases hXU : X ≤ P.U
  · apply le_antisymm hXU
    apply le_trans ?_ hc
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr (fun b hb =>
      (P.commute_of_mem_U (hXU hb) ha).eq)
  · obtain ⟨g, hg, hgu⟩ := SetLike.not_le_iff_exists.mp hXU
    let C := Subgroup.centralizer ({g} : Set S)
    have hXC : X ≤ C := by
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : X) ⟨g, hg⟩))
    have hmodels := P.outer_centralizer_models hgu
    have hcomm : IsMulCommutative C := by
      rcases hmodels with hcyc | he
      · let := hcyc
        infer_instance
      · obtain ⟨e⟩ := he
        apply IsMulCommutative.of_comm
        intro a b
        apply e.injective
        simp only [map_mul, mul_comm]
    have heq : X = C := by
      apply le_antisymm hXC
      apply le_trans ?_ hc
      exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm).trans
        (Subgroup.centralizer_le hXC)
    apply False.elim
    apply hAut
    rw [heq]
    rcases hmodels with hcyc | he
    · let := hcyc
      exact ((IsPGroup.of_card P.card).to_subgroup C).mulAut_of_isCyclic_two
    · obtain ⟨e⟩ := he
      exact abelian_two_factor_aut_isPGroup_of_equiv P.height e
end ABG.Wreathed.Presentation
