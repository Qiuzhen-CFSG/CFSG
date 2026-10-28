module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd

/-!
# Odd centers of finite quasisimple Held covers

The proved even and odd marked M₁ relations exclude every finite perfect
central double cover of the concrete Held group. If a finite quasisimple
group with this central quotient had even center, the prime-kernel reduction
would produce such a double cover. Thus its center has odd order.

This supplies the precise two-primary consequence of Aschbacher--Smith
I.1.1 and I.1.3, printed p.407, needed in E.6.18. Both marked-word contracts
are discharged. The proof uses the checked local bounds and coset cover
from John Bray's ATLAS `Held/Model/Source/HeG1-P1.M`, without invoking that
file's informal argument from triviality of the Schur multiplier.
-/

public section
namespace Held.CentralCovers
open PerfectCentralCovering Theory.GroupTheory
open TwoPrimary.FaithfulPresentation.M1Restriction
universe u

/-- The concrete Held group has no finite perfect central double cover. -/
theorem no_double_cover {E : Type u} [Group E] [Finite E] (f : Cover E He) :
    Nat.card f.toMonoidHom.ker ≠ 2 :=
  no_double_cover_of_binary_m1 binaryEvenRelations binaryOddRelations f

/-- Every finite quasisimple group whose actual central quotient is Held
has odd center. No presentation or word-identity premises remain. -/
theorem odd_center {X : Type u} [Group X] [Finite X] [IsQuasisimple X]
    (h : Nonempty ((X ⧸ Subgroup.center X) ≃* He)) :
    Odd (Nat.card (Subgroup.center X)) := by
  obtain ⟨e⟩ := h
  exact TwoPrimary.odd_center_of_no_double_cover (fun _ _ _ f => no_double_cover f) e

end Held.CentralCovers
