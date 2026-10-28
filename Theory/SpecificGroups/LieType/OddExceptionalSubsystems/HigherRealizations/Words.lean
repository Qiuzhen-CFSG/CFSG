module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.Generators
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Word comparison for the marked folded matrix groups

All three word maps use the same alphabet: a sign, a numbered F4 node and
a field parameter. The source word map is surjective because those are the
literal defining generators of the E6 folded subgroup. Equality of the
matrix-word kernels therefore constructs an injective homomorphism with
the required signed formulas. The kernel equalities are explicit outstanding
representation-theoretic inputs, not conclusions asserted in this file.

This isolates the admissible-lattice comparison required in GLS3 §2.6.2--3
(`refs/KGroup/GLS3/chapter2.tex`) for the A.2.17 exceptional inclusions.
-/

@[expose] public section
noncomputable section

namespace TwistedE6.FoldedSubsystem.HigherRealizations

variable (F : Type*) [Field F]

abbrev FoldedWord := FreeGroup (Bool × Fin 4 × F)

def sourceWord : FoldedWord F →* splitSubgroup F :=
  FreeGroup.lift fun x => f4Simple F x.1 x.2.1 x.2.2

def e7Word : FoldedWord F →* ExceptionalSplit.e7Cover F :=
  FreeGroup.lift fun x => e7FoldedSimple F x.1 x.2.1 x.2.2

def e8Word : FoldedWord F →* ExceptionalSplit.e8Cover F :=
  FreeGroup.lift fun x => e8FoldedSimple F x.1 x.2.1 x.2.2

@[simp] theorem sourceWord_of (s : Bool) (i : Fin 4) (t : F) :
    sourceWord F (FreeGroup.of (s, i, t)) = f4Simple F s i t :=
  FreeGroup.lift_apply_of

@[simp] theorem e7Word_of (s : Bool) (i : Fin 4) (t : F) :
    e7Word F (FreeGroup.of (s, i, t)) = e7FoldedSimple F s i t :=
  FreeGroup.lift_apply_of

@[simp] theorem e8Word_of (s : Bool) (i : Fin 4) (t : F) :
    e8Word F (FreeGroup.of (s, i, t)) = e8FoldedSimple F s i t :=
  FreeGroup.lift_apply_of

theorem sourceWord_surjective : Function.Surjective (sourceWord F) := by
  apply MonoidHom.range_eq_top.mp
  apply top_le_iff.mp
  apply source_le_of_f4Simple_mem
  intro s i t
  exact ⟨FreeGroup.of (s, i, t), sourceWord_of F s i t⟩

section Descent

variable {G : Type*} [Group G]

/-- Descend a target word evaluation through the actual source matrix relations. -/
def descendWord (w : FoldedWord F →* G)
    (hk : (sourceWord F).ker ≤ w.ker) : splitSubgroup F →* G :=
  (sourceWord F).liftOfSurjective (sourceWord_surjective F) ⟨w, hk⟩

@[simp] theorem descendWord_sourceWord (w : FoldedWord F →* G)
    (hk : (sourceWord F).ker ≤ w.ker) (a : FoldedWord F) :
    descendWord F w hk (sourceWord F a) = w a :=
  (sourceWord F).liftOfRightInverse_comp_apply _ _ _ a

theorem descendWord_injective (w : FoldedWord F →* G)
    (hk : (sourceWord F).ker = w.ker) :
    Function.Injective (descendWord F w hk.le) := by
  apply (injective_iff_map_eq_one _).mpr
  intro h hh
  obtain ⟨a, rfl⟩ := sourceWord_surjective F h
  rw [descendWord_sourceWord] at hh
  have ha : a ∈ (sourceWord F).ker := hk.ge hh
  exact ha

end Descent

/-- The E7 matrix map conditional on the precise word-kernel comparison. -/
def e7CoverMapOfWordKernels (hk : (sourceWord F).ker = (e7Word F).ker) :
    splitSubgroup F →* ExceptionalSplit.e7Cover F :=
  descendWord F (e7Word F) hk.le

/-- The E8 matrix map conditional on the precise word-kernel comparison. -/
def e8CoverMapOfWordKernels (hk : (sourceWord F).ker = (e8Word F).ker) :
    splitSubgroup F →* ExceptionalSplit.e8Cover F :=
  descendWord F (e8Word F) hk.le

theorem e7CoverMapOfWordKernels_injective
    (hk : (sourceWord F).ker = (e7Word F).ker) :
    Function.Injective (e7CoverMapOfWordKernels F hk) :=
  descendWord_injective F (e7Word F) hk

theorem e8CoverMapOfWordKernels_injective
    (hk : (sourceWord F).ker = (e8Word F).ker) :
    Function.Injective (e8CoverMapOfWordKernels F hk) :=
  descendWord_injective F (e8Word F) hk

@[simp] theorem e7CoverMapOfWordKernels_f4Simple
    (hk : (sourceWord F).ker = (e7Word F).ker) (s : Bool) (i : Fin 4) (t : F) :
    e7CoverMapOfWordKernels F hk (f4Simple F s i t) = e7FoldedSimple F s i t := by
  rw [← sourceWord_of F s i t]
  exact (descendWord_sourceWord F (e7Word F) hk.le _).trans (e7Word_of F s i t)

@[simp] theorem e8CoverMapOfWordKernels_f4Simple
    (hk : (sourceWord F).ker = (e8Word F).ker) (s : Bool) (i : Fin 4) (t : F) :
    e8CoverMapOfWordKernels F hk (f4Simple F s i t) = e8FoldedSimple F s i t := by
  rw [← sourceWord_of F s i t]
  exact (descendWord_sourceWord F (e8Word F) hk.le _).trans (e8Word_of F s i t)

end TwistedE6.FoldedSubsystem.HigherRealizations
