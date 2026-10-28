module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCentralizer
public import Theory.GroupTheory.SolvableResidual.TwoKernel
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Perfectness of the original triple-six point residual

The actual point centralizer has A5 quotient by its two-core. The two-residual
therefore equals the solvable residual, so its literal image in the original
ambient group is perfect.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 12.7.4(3),
printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The two-residual of the original point centralizer is its perfect
solvable residual, using the actual A5 quotient and two-group kernel. -/
theorem tripleSixPointCentralizerResidual_eq_solvableResidual
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) =
      solvableResidual (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let e := tripleSixPointCentralizerEquiv D a t ht heven
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (C ⧸ pCore 2 C) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  apply pResidual_eq_solvableResidual_of_perfect_image
    (QuotientGroup.mk' (pCore 2 C)) (QuotientGroup.mk'_surjective _)
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup

/-- The literal ambient subgroup Lt from 12.7.4 is perfect. -/
theorem tripleSixPointCentralizerResidual_perfect (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    Group.IsPerfect
      ((pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype) := by
  rw [tripleSixPointCentralizerResidual_eq_solvableResidual D a t ht heven]
  exact Group.IsPerfect.map _

end CFSG.Quasithin.Chapter12.Section07
