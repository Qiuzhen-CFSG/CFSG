module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.QuotientTransport
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.ChapterA.Section03.Basic

/-!
# The embedded geometry needed for the J₄ to M₂₄ reduction

The proposed route chooses an overgroup H of the actual A, invariant under
the particular stabilizing automorphism. Its quotient is identified with the
concrete M₂₄, and the actual image of A must satisfy both the E₁₆ extension
clause and the Sylow-local C-component condition. None of these geometric
facts follows merely from the quotient label in A.3.12(17).

This module specifies that outstanding geometric obligation. It supplies no
witness. The separate M₂₄ stabilizer calculation is also an explicit input to
the conditional assembly; neither input is an asserted source theorem here.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.12(14),(17)
and its proof via Sylow overgroups, printed pp.47–48; proof of 1.3.9, p.514.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer
open Section02.LocalModels

universe u
variable {G : Type u} [Group G]

/-- A genuine invariant embedded overgroup, with the specific smaller section
retained under the actual quotient isomorphism. -/
structure InvariantMathieuOvergroup (A : Subgroup G) (α : MulAut G) where
  overgroup : Subgroup G
  le_overgroup : A ≤ overgroup
  invariant : overgroup.map α.toMonoidHom = overgroup
  quotientEquiv : XiQuotient overgroup ≃* Sporadic.Mathieu.M24
  image_extension : HasExtension ((twoQuotientImage A overgroup).map quotientEquiv.toMonoidHom)
    (ElementaryModel 2 4) (fun Z _ => ClassicalGroup.IsPSL Z 4 2)
  sylow : Sylow 2 Sporadic.Mathieu.M24
  image_local : (twoQuotientImage A overgroup).map quotientEquiv.toMonoidHom ∈
    ChapterA.Section03.localCComponents (sylow : Subgroup Sporadic.Mathieu.M24)

/-- The exact M₂₄ input, on the concrete carrier. The sibling stabilizer
calculation must prove this using the embedded E₁₆ extension. -/
def MathieuFourStabilizerTheorem : Prop :=
  ∀ (B : Subgroup Sporadic.Mathieu.M24) (S : Sylow 2 Sporadic.Mathieu.M24),
    ClassicalGroup.IsPSL (XiQuotient B) 4 2 →
    HasExtension B (ElementaryModel 2 4) (fun Z _ => ClassicalGroup.IsPSL Z 4 2) →
    B ∈ ChapterA.Section03.localCComponents (S : Subgroup Sporadic.Mathieu.M24) →
    TwoStabilizerActsInner B

/-- The missing J₄ geometric assertion, retaining the original Sylow-local
embedding. In particular it requires invariance, not just an M₂₄ section
somewhere in the ambient group. -/
def JankoFourInvariantMathieuTheorem : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q], (Q ≃* Janko4.Model) →
    ∀ (A : Subgroup Q) (S : Sylow 2 Q),
      ClassicalGroup.IsPSL (XiQuotient A) 4 2 →
      A ∈ ChapterA.Section03.localCComponents (S : Subgroup Q) →
      ∀ α : MulAut Q, (∃ n : ℕ, α ^ (2 ^ n) = 1) →
        A.map α.toMonoidHom = A → Nonempty (InvariantMathieuOvergroup A α)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer
