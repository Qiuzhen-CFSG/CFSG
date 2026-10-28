module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.Images
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.G64Source
public import Theory.Representation.PermutationTransvectionCubicCentralizer

/-!
# The symmetric alternatives in the split G.6.4 application

A faithful binary actor with a transvection and no commuting cubic in its
derived subgroup cannot have any of the S₆-natural, S₇-natural, or S₆-core
action models. Transport the representation along the actual actor isomorphism,
apply the intrinsic permutation centralizer theorem, and transport its witness
back, preserving order and derived-subgroup membership.

The six-letter natural quotient and augmentation core remain separate model
conclusions. The intrinsic obstruction applies to any faithful binary module,
so it excludes both without identifying their distinct vector spaces.

These deductions retain the no-cubic hypothesis explicitly. In the source
application its proof requires semisimple kernel transport and the actual
displacement-plane stabilizer restriction; those belong to the parent assembly.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first split
paragraph of 15.3.58, printed p.1149, using G.6.4 on printed pp.345–346.
-/

public section

open Representation
open Representation.PermutationTransvectionCubicCentralizer
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.PermutationSieve

universe u
variable {A E : Type u} [Group A] [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (σ : Representation (ZMod 2) A E) (hσ : Function.Injective σ)
    (t : A) (ht : IsTransvection σ t)
    (hno : ∀ c ∈ commutator A, orderOf c = 3 → ¬ Commute c t)

include hσ ht hno

private theorem six_impossible (e : A ≃* Equiv.Perm (Fin 6)) : False := by
  have ht' : IsTransvection (σ.comp e.symm.toMonoidHom) (e t) := by
    obtain ⟨f, v, hf, hv, hfv, hact⟩ := ht
    refine ⟨f, v, hf, hv, hfv, ?_⟩
    intro w
    change σ (e.symm (e t)) w = _
    rw [e.symm_apply_apply]
    exact hact w
  have hn : e t ≠ 1 := fun h => ht.ne_one (e.injective (h.trans e.map_one.symm))
  have hsq : (e t) ^ 2 = 1 := by
    rw [← map_pow, transvection_square hσ ht, map_one]
  have hc := exists_commuting_cubic_six_of_displacement (σ.comp e.symm.toMonoidHom)
    (hσ.comp e.symm.injective) (e t) hn hsq (transvection_displacement_rank ht').le
  obtain ⟨c, hc, ho, hct⟩ := exists_commuting_cubic_map e.symm hc
  exact hno c hc ho (by simpa only [e.symm_apply_apply] using hct)

omit [Finite E] in
private theorem seven_impossible (e : A ≃* Equiv.Perm (Fin 7)) : False := by
  have hn : e t ≠ 1 := fun h => ht.ne_one (e.injective (h.trans e.map_one.symm))
  have hsq : (e t) ^ 2 = 1 := by
    rw [← map_pow, transvection_square hσ ht, map_one]
  have hc := exists_commuting_cubic_seven_of_involution (e t) hn hsq
  obtain ⟨c, hc, ho, hct⟩ := exists_commuting_cubic_map e.symm hc
  exact hno c hc ho (by simpa only [e.symm_apply_apply] using hct)

/-- Exclude the six-letter natural quotient from the faithful action models. -/
theorem not_natural_six :
    ¬ HasActionModel σ (BinaryPermutation.naturalRepresentation (Fin 6)) := by
  rintro ⟨e, _, _⟩
  exact six_impossible σ hσ t ht hno e

omit [Finite E] in
/-- Exclude the seven-letter natural action. Only the marked involution is needed. -/
theorem not_natural_seven :
    ¬ HasActionModel σ (BinaryPermutation.naturalRepresentation (Fin 7)) := by
  rintro ⟨e, _, _⟩
  exact seven_impossible σ hσ t ht hno e

/-- Exclude the six-letter augmentation core, retaining its separate model predicate. -/
theorem not_core_six :
    ¬ HasActionModel σ (BinaryPermutation.coreRepresentation (Fin 6)) := by
  rintro ⟨e, _, _⟩
  exact six_impossible σ hσ t ht hno e

/-- Removing all three symmetric alternatives leaves the binary linear models
of G.6.4(4). The no-cubic premise is still an input to this conditional deduction. -/
theorem linear_of_central_alternative (hmodels : G64CentralAlternative σ) :
    ∃ n, 2 ≤ n ∧ n ≤ 5 ∧ HasActionModel σ (linearRepresentation n) := by
  rcases hmodels with h | h | h | h
  · exact h
  · exact (not_natural_six σ hσ t ht hno h).elim
  · exact (not_natural_seven σ hσ t ht hno h).elim
  · exact (not_core_six σ hσ t ht hno h).elim

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.PermutationSieve
