module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddPartDescent
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.LargePrimary.Complete
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.Complete

/-!
# The actual SU3 lift of a binary projective covering

The proved large-prime and three-primary bounds discharge every remaining
odd-kernel premise of scalar-cover descent. For a quasisimple target with
trivial two-core, the actual SU3 group maps onto it compatibly with its
specified projection onto PSU3, including field order eight.

Source: Aschbacher--Smith I.1.3 and K.3.3, pp.407 and 456.
-/

public section
open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover
variable {F L : Type*} [Field F] [Finite F]
  [Group L] [Finite L] [IsQuasisimple L] (J : HermitianForm 3 F)

/-- The complete binary scalar-cover descent, retaining its literal triangle. -/
theorem exists_even_scalar_lift {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hcore : pCore 2 L = ⊥) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      f.comp k = J.specialToProjective :=
  OddPartDescent.exists_lift_even J hn hcard hconj
    (fun _ hr hr3 => EvenKernelBound.LargePrimary.not_dvd_universal_kernel J hn hr hr3 hcard hconj)
    (fun ho => EvenKernelBound.ThreePrimary.not_nine_dvd_universal_kernel J hn ho hcard hconj)
    f hf hcore
end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover
