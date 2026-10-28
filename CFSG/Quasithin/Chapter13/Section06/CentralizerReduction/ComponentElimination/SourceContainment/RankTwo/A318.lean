module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# The component clauses of A.3.18 used in 13.6.20

This interface retains the prime-to-p residual and the literal image of
the C-component in H/O_{p′}(H). In the cover case, it retains both the
full component model list and the distinction between (3a) and (3b).

`EarlierA318ComponentCases` is an explicit universal earlier-source input,
not a proof of A.3.18. It asks only for the component clauses of that
theorem: its further classification of the ambient extensions and their
outer actors is not needed by this consumer. In particular we do not use
the legacy nonsplit-extension record, which incorrectly requires an outer
element of order three in the nonsplit coset. No such element is required
here, and the projective model is imposed on L*, not L/O₂(L).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
A.3.16–18, printed pp.51–53; the application is 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
open Chapter1.Section02.LocalModels
universe u

/-- The component-level conclusions of A.3.18. The additional ambient
extension, fixed-point and conjugacy clauses of the full source theorem
may be forgotten when supplying this interface. -/
inductive A318ComponentCase (H : Type u) [Group H] (C : Subgroup H) (p : ℕ) : Prop
  | residual (h : C = primeToResidual p H)
  | projective (hp : p = 3) (unitary : Bool) (q : ℕ)
      (hmod : q % 3 = (if unitary then 2 else 1))
      (model : IsPSLSign (C.map (QuotientGroup.mk' (pPrimeCore p H))) unitary 3 q)
  | cover (hp : p = 3)
      (model :
        (∃ (unitary : Bool) (q : ℕ), q % 3 = (if unitary then 2 else 1) ∧
          IsSLSign (C.map (QuotientGroup.mk' (pPrimeCore p H))) unitary 3 q) ∨
        IsAlternatingCover (C.map (QuotientGroup.mk' (pPrimeCore p H))) 6 ∨
        IsAlternatingCover (C.map (QuotientGroup.mk' (pPrimeCore p H))) 7 ∨
        IsM22Cover (C.map (QuotientGroup.mk' (pPrimeCore p H))))
      (cases : C = closure {x : H | orderOf x = 3} ∨
        ∃ (unitary : Bool) (q : ℕ), q % 3 = (if unitary then 2 else 1) ∧
          IsSLSign (C.map (QuotientGroup.mk' (pPrimeCore p H))) unitary 3 q)

/-- Universal A.3.18 with only its component conclusions requested.
The hypothesis is the source C-component condition, not ordinary
quasisimple-component membership. The rank belongs to C itself. -/
def EarlierA318ComponentCases (κ : GroupClass.{u}) : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], IsSQTK κ H →
    ∀ C : Subgroup H, C.IsCComponent → IsQuasisimple (C ⧸ pCore 2 C) →
      ∀ p : ℕ, p.Prime → Odd p → 1 < primeRank p C → A318ComponentCase H C p

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
