module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Residual

/-!
# The B.5 alternatives in the presence of two distinct components

A quasisimple generalized Fitting subgroup admits only one ordinary
component. The symmetric-three actor is solvable. In the corrected outer
A₆–C₃ configuration every perfect subgroup lies in the original A₆ factor,
so its only component is that factor. Thus two distinct actual components
leave precisely the two product alternatives, retaining every module field.

This is the group-theoretic branch selection used by the two-orbit argument
in 13.6.14. It does not assume minimal parabolicity or a module decomposition.
Source: Aschbacher–Smith B.5.6, printed p.105; 13.6.14, p.929.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterB.SourceInduction
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]

/-- Two distinct components select the product rows of the corrected B.5
classification, with their full original representation data. -/
theorem AdequateAlternative.product_rows_of_two_components
    (ρ : Representation (ZMod 2) D V) (h : AdequateAlternative ρ)
    {A B : Subgroup D} (hA : IsComponent D A) (hB : IsComponent D B) (hne : A ≠ B) :
    Nonempty (SourceTwoFactorCase ρ) ∨ Nonempty (HyperplaneCase ρ) := by
  rcases h with ht | h
  · let := ht
    exact (hne (Subsingleton.elim _ _)).elim
  cases h with
  | quasisimple hq _ =>
    have hF : IsComponent D (generalizedFitting D) :=
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal,hq⟩
    exact (hne ((hA.eq_of_le hF (component_le_generalizedFitting D A hA)).trans
      (hB.eq_of_le hF (component_le_generalizedFitting D B hB)).symm)).elim
  | symmetricThree c =>
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
      (f := c.equiv.toMonoidHom) c.equiv.injective
    let := hA.2
    let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
    let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
    exact (Group.IsPerfect.not_isSolvable A inferInstance).elim
  | twoFactors c => exact Or.inl ⟨c⟩
  | outerSixThree c =>
    let := c.first_normal
    let := c.quotient_first_solvable
    have he {C : Subgroup D} (hC : IsComponent D C) : C = c.first := by
      let := hC.2
      exact hC.eq_of_le c.first_isComponent (le_of_isPerfect_of_solvable_quotient C c.first)
    exact (hne ((he hA).trans (he hB).symm)).elim
  | hyperplane c => exact Or.inr ⟨c⟩

end CFSG.Quasithin.ChapterB.SourceInduction
