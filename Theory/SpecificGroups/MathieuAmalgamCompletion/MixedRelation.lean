module

public import Theory.SpecificGroups.MathieuAmalgamCompletion.Relators
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

/-!
# Matching the literal mixed relator with the source commutator

The certificate uses GAP's inverse-first convention. Conjugation by xy
turns that word into the repository commutator xyx⁻¹y⁻¹, so the source
square-one relation gives exactly the recorded twenty-seventh relator.
-/

public section
open Subgroup.CosetWordCertificate
open scoped commutatorElement
namespace Theory.SpecificGroups.MathieuAmalgamCompletion
variable {G : Type*} [Group G]

/-- The actual source commutator-square equation gives the literal final
word of the finite completion certificate, with the same generators. -/
theorem mixed_relator_of_commutator_square (g : Fin 4→G)
    (h : ⁅g 2,g 3⁆^2=1) : eval g (relator 26)=1 := by
  have hc : (g 2*g 3)*(g 2)⁻¹*(g 3)⁻¹*g 2*g 3*(g 2*g 3)⁻¹=⁅g 2,g 3⁆ := by
    simp only [commutatorElement_def]
    group
  have hconj : (MulAut.conj (g 2*g 3)) ((g 2)⁻¹*(g 3)⁻¹*g 2*g 3)=⁅g 2,g 3⁆ := by
    simpa only [MulAut.conj_apply,mul_assoc] using hc
  have hp : ((g 2)⁻¹*(g 3)⁻¹*g 2*g 3)^2=1 := by
    apply (MulAut.conj (g 2*g 3)).injective
    rw [map_pow,hconj,map_one,h]
  simpa [relator,decode,eval,FreeGroup.lift_mk,pow_two,mul_assoc] using hp

end Theory.SpecificGroups.MathieuAmalgamCompletion
