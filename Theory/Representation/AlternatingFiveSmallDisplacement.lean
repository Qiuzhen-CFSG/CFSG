module

public import Theory.Representation.AlternatingFiveInvolutionDisplacement
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# An alternating-five involution detects two nontrivial sections

Every nontrivial binary A₅ action is faithful. Its involutions move at
least two dimensions. Displacement on an invariant subspace and its
quotient adds to at most the full displacement. Consequently an involution
moving at most three dimensions forces one of these two actions to be
trivial, without a classification of the irreducible modules.

Source application: Aschbacher–Smith, the two-noncentral-chief-factor
branch concluding 14.7.40, printed p.1063.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.AlternatingFiveSmallDisplacement
private theorem alternating_injective_of_nontrivial
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 5)) E) (hn : τ ≠ 1) :
    Function.Injective τ := by
  rcases (MonoidHom.normal_ker τ).eq_bot_or_eq_top with hk | hk
  · exact τ.ker_eq_bot_iff.mp hk
  · apply False.elim
    apply hn
    apply MonoidHom.ext
    intro a
    exact show a ∈ τ.ker from hk ▸ mem_top a

/-- Displacement at most three excludes two nontrivial sections. -/
theorem submodule_or_quotient_trivial
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 5)) E)
    (a : alternatingGroup (Fin 5)) (ha : orderOf a = 2)
    (hd : Module.finrank (ZMod 2) (τ a - LinearMap.id).range ≤ 3)
    (P : Subrepresentation τ) : P.toRepresentation = 1 ∨ P.quotientRepresentation = 1 := by
  by_cases hp : P.toRepresentation = 1
  · exact Or.inl hp
  by_cases hq : P.quotientRepresentation = 1
  · exact Or.inr hq
  have hpl := AlternatingFiveInvolutionDisplacement.displacement_lower P.toRepresentation
    (alternating_injective_of_nontrivial _ hp) a ha
  have hql := AlternatingFiveInvolutionDisplacement.displacement_lower P.quotientRepresentation
    (alternating_injective_of_nontrivial _ hq) a ha
  have hb := fixedCodim_quotient_add_subrepresentation_le τ P (zpowers a)
  rw [fixedCodim_zpowers_eq_displacement_rank,fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank] at hb
  omega


end Representation.AlternatingFiveSmallDisplacement
