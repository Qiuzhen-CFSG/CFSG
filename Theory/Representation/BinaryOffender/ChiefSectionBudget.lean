module
public import Theory.Representation.BinaryOffender.TwoSectionBudget

/-!
# A strict budget from a non-FF module and a chief section

On the same elementary actor, a faithful non-FF section costs strictly more
than its rank and a faithful chief action of quadratic ratio at least one
costs at least its rank. Fixed codimensions along the literal submodule and
quotient maps give a strict two-rank bound. No common kernel is presumed.

Source: the section budget in Aschbacher--Smith D.3.9 and 9.2.2(1).
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {H V : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem rank_le_fixedCodim_of_image_quadraticRatio_ge_one
    (ρ : Representation (ZMod 2) H V)
    (hbound : 1 ≤ quadraticRatio (imageRepresentation ρ))
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1) :
    rank A ≤ fixedCodim ρ A := by
  by_contra! hlt
  have hn : IsStrongFFModule (imageRepresentation ρ) := by
    refine ⟨actionSubgroup ρ A,hA.actionSubgroup ρ hfaith,?_⟩
    rw [fixedCodim_actionSubgroup,actionSubgroup_rank ρ A hfaith]
    exact hlt
  exact (not_lt_of_ge hbound) ((isStrongFFModule_iff_quadraticRatio_lt_one _).mp hn)

/-- A non-FF submodule and a nontrivial chief section of its quotient consume
strictly more than two actor ranks, with kernels checked on that same actor. -/
theorem twice_rank_lt_fixedCodim_of_nonFF_and_chief
    (ρ : Representation (ZMod 2) H V) (U : Subrepresentation ρ)
    (W : Subrepresentation U.quotientRepresentation)
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hU : ∀ a ∈ A, (∀ v, U.toRepresentation a v = v) → a = 1)
    (hW : ∀ a ∈ A, (∀ v, W.toRepresentation a v = v) → a = 1)
    (hnU : ¬ IsFFModule (imageRepresentation U.toRepresentation))
    (hbW : 1 ≤ quadraticRatio (imageRepresentation W.toRepresentation)) :
    2 * rank A < fixedCodim ρ A := by
  have hu := rank_lt_fixedCodim_of_nonFF_image U.toRepresentation hA hU hnU
  have hw := rank_le_fixedCodim_of_image_quadraticRatio_ge_one W.toRepresentation hbW A hA hW
  have hqw := fixedCodim_subrepresentation_le U.quotientRepresentation W A
  have hs := fixedCodim_quotient_add_subrepresentation_le ρ U A
  omega

/-- The same budget applies to a literal chief subquotient of the quotient. -/
theorem twice_rank_lt_fixedCodim_of_nonFF_and_chief_subquotient
    (ρ : Representation (ZMod 2) H V) (U : Subrepresentation ρ)
    (W : Subrepresentation U.quotientRepresentation)
    (N : Subrepresentation W.toRepresentation)
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hU : ∀ a ∈ A, (∀ v, U.toRepresentation a v = v) → a = 1)
    (hW : ∀ a ∈ A, (∀ v, N.quotientRepresentation a v = v) → a = 1)
    (hnU : ¬ IsFFModule (imageRepresentation U.toRepresentation))
    (hbW : 1 ≤ quadraticRatio (imageRepresentation N.quotientRepresentation)) :
    2 * rank A < fixedCodim ρ A := by
  have hu := rank_lt_fixedCodim_of_nonFF_image U.toRepresentation hA hU hnU
  have hw := rank_le_fixedCodim_of_image_quadraticRatio_ge_one N.quotientRepresentation hbW A hA hW
  have hn := fixedCodim_quotient_add_subrepresentation_le W.toRepresentation N A
  have hqw := fixedCodim_subrepresentation_le U.quotientRepresentation W A
  have hs := fixedCodim_quotient_add_subrepresentation_le ρ U A
  omega
end Representation.BinaryOffender
