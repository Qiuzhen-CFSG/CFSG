module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.EvenCoverLifting.Orthogonal.Kernels
public import Theory.SpecificGroups.ClassicalOrthogonal.EvenCoverKernels.Plus

/-!
# Higher split orthogonal applications of odd-prime kernel exclusion

Rank-four exclusion and a rank-raising argument imply a two-group universal
kernel in every rank at least four. The existing descent kills its image in a
cover with trivial two-core. These applications retain the literal projective
model and the full `KnownSimple.OrthogonalPlusParameters` constructor.

Both family-specific exclusions are still explicit inputs. This conditional
assembly is not a proof of their source calculation. Source: GLS3 Section 6.1,
Tables 6.1.2–6.1.3 and Theorem 6.1.4; Aschbacher–Smith B.1.13, pp.73–74.
In particular no identity-universal-cover assertion is made for D₄(2).
-/

public section
open Subgroup Theory.GroupTheory
open ClassicalOrthogonal.EvenCoverKernels.Plus
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.EvenOrthogonal
universe u
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]

/-- Consume the independent base and induction calculations on the actual
quotient model, with its quasisimplicity inherited from the source. -/
theorem lift_plus_of_rank_induction (hcore : pCore 2 L = ⊥) {r q : ℕ}
    (hr : 4 ≤ r) (he : Even q)
    (hfour : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      OddPrimeKernelExclusion 4 F)
    (hstep : ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
      (n : ℕ), 4 ≤ n → OddPrimeKernelExclusion n F → OddPrimeKernelExclusion (n + 1) F)
    (h : ClassicalGroup.IsPOmegaPlus (L ⧸ center L) r q) :
    ClassicalGroup.IsPOmegaPlus L r q := by
  apply lift_plus_of_universal_kernel hcore he _ h
  intro F _ _ _ _
  exact universal_kernel_isTwoGroup_of_rank_induction hr (hfour F) (hstep F)

/-- The same kernel calculation supplies the original even-Lie catalogue
alternative, retaining its exact rank and field parameters. -/
theorem evenLie_of_plus_rank_induction (hcore : pCore 2 L = ⊥) {r q : ℕ}
    (hr : 4 ≤ r) (hp : KnownSimple.OrthogonalPlusParameters r q) (he : Even q)
    (hfour : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      OddPrimeKernelExclusion 4 F)
    (hstep : ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
      (n : ℕ), 4 ≤ n → OddPrimeKernelExclusion n F → OddPrimeKernelExclusion (n + 1) F)
    (h : ClassicalGroup.IsPOmegaPlus (L ⧸ center L) r q) : IsEvenLieGroup L := by
  apply evenLie_of_plus_kernel hcore hp he _ h
  intro F _ _ _ _
  exact universal_kernel_isTwoGroup_of_rank_induction hr (hfour F) (hstep F)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.EvenOrthogonal
