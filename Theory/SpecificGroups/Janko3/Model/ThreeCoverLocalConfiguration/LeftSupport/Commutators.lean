module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.Words
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.LeftSupport.BasicCommutators
import Mathlib.Tactic.FinCases

/-!
# Commutator words for the concrete J₃ centralizer candidate

Each of the five literal generators is a product of the three commutators
of generators 2, 3, 4 and their inverses (indices here are zero-based).
The displayed words are checked in the faithful degree-6156 permutation
representation. They will prove perfectness without assuming the abstract
centralizer structure from GLS3, Table 5.3h, printed p.269.

The short words were discovered by breadth-first search in the retained
ATLAS permutations. Only the kernel-checked equalities below are used.
-/

namespace Sporadic.Janko3.ThreeCoverConfig.LeftSupportCertificate
open Theory.GroupTheory OrderCertificate TwoLocal TwoLocal.CentralizerCertificate
open scoped commutatorElement
set_option maxRecDepth 40000
set_option Elab.async false

/-- Three elementary commutators and their inverses. -/
@[expose] public def commutatorLetter {G : Type*} [Group G] (c : Fin 5 → G) : Fin 6 → G
  | 0 => ⁅c 2, c 3⁆
  | 1 => ⁅c 2, c 4⁆
  | 2 => ⁅c 3, c 4⁆
  | 3 => ⁅c 2, c 3⁆⁻¹
  | 4 => ⁅c 2, c 4⁆⁻¹
  | 5 => ⁅c 3, c 4⁆⁻¹

/-- Witnesses expressing the five centralizer generators in commutators. -/
@[expose] public def commutatorWord : Fin 5 → List (Fin 6)
  | 0 => [1, 1, 1, 1, 1]
  | 1 => [1, 1, 1, 1, 1]
  | 2 => [0, 2, 0, 5, 4, 5]
  | 3 => [0, 5, 1, 2, 2]
  | 4 => [0, 2, 0, 2, 3]

@[expose] public def centralizerPerm : Fin 5 → Equiv.Perm (Fin 6156)
  | 0 => C0G0
  | 1 => C0G1
  | 2 => C0G2
  | 3 => C0G3
  | 4 => C0G4

public theorem centralizerPerm_eq (i : Fin 5) :
    centralizerPerm i = (centralizerGenerator i : Equiv.Perm (Fin 6156)) := by
  fin_cases i
  · exact C0G0_eq_generator
  · exact C0G1_eq_generator
  · exact C0G2_eq_generator
  · exact C0G3_eq_generator
  · exact C0G4_eq_generator

@[expose] public def commutatorPerm : Fin 6 → Equiv.Perm (Fin 6156)
  | 0 => c23Perm
  | 1 => c24Perm
  | 2 => c34Perm
  | 3 => c23Perm⁻¹
  | 4 => c24Perm⁻¹
  | 5 => c34Perm⁻¹

private theorem commutatorLetter_eq (i : Fin 6) :
    commutatorPerm i =
      ((commutatorLetter centralizerGenerator i : Model) : Equiv.Perm (Fin 6156)) := by
  fin_cases i <;>
    simp only [commutatorPerm, commutatorLetter, c23Perm_eq, c24Perm_eq, c34Perm_eq,
      C0G2_eq_generator, C0G3_eq_generator, C0G4_eq_generator] <;> rfl

private theorem commutatorWord_eq (w : List (Fin 6)) :
    evalWord commutatorPerm w =
      ((evalWord (commutatorLetter centralizerGenerator) w : Model) : Equiv.Perm (Fin 6156)) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change commutatorPerm i * evalWord commutatorPerm w =
      ((commutatorLetter centralizerGenerator i : Model) : Equiv.Perm (Fin 6156)) *
        ((evalWord (commutatorLetter centralizerGenerator) w : Model) : Equiv.Perm (Fin 6156))
    rw [commutatorLetter_eq, ih]

set_option maxHeartbeats 4000000 in
public theorem centralizerGenerator_word (i : Fin 5) :
    centralizerGenerator i =
      evalWord (commutatorLetter centralizerGenerator) (commutatorWord i) := by
  have h : ∀ j : Fin 5, checkLetters (fun k => decide
      ((centralizerPerm j) k =
        (evalWord commutatorPerm (commutatorWord j)) k)) = true := by
    apply allFin
    decide +kernel
  apply Subtype.ext
  rw [← centralizerPerm_eq, ← commutatorWord_eq]
  apply Equiv.ext
  exact allLetters _ (h i)

end Sporadic.Janko3.ThreeCoverConfig.LeftSupportCertificate
