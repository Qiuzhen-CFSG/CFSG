module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.Model
public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# Literal alternatives for the normalized slice of 7.0.1

The orthogonal alternative marks the actual component and its action on the
original vector space by the Hermitian four-space over GF(2^n). The existing
`OrthogonalModel.minus_intertwines` identifies it with the genuine minus
orthogonal action; `groupEquiv` identifies the component with SL₂(2^(2n)),
which is PSL₂ in characteristic two. The field exponent is strictly greater
than one, as in the 12.2.2 application.

These definitions specify obligations, not a classification theorem. The
Mathieu predicate uses concrete isomorphisms of the actual central quotient
and merely separates independent source branches. The eventual conclusion
still requires the actual orthogonal action or a concrete ambient J₄.

Source: Aschbacher--Smith, 7.0.1 and 12.2.2, printed pp.695 and795.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open Subgroup Representation.BinaryOffender
variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- The surviving non-FF classical action, including its original component
marking and the binary intertwiner on the entire orbit space. -/
def OrthogonalMinusAlternative (ρ : Representation (ZMod 2) A E) (L : Subgroup A) : Prop :=
  ∃ (n : ℕ) (hn : 1 < n),
    letI : NeZero n := ⟨by omega⟩
    Nonempty (ChapterK.RankOne.OrthogonalModel n ρ L)

/-- Exactly the four concrete Mathieu central quotients in the normalized
rows of Table7.1.1, including covers through the actual central quotient. -/
def HasMathieuCentralQuotient (L : Type*) [Group L] : Prop :=
  Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M12) ∨
  Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M22) ∨
  Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M23) ∨
  Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M24)

/-- The precise target of the normalized source assembly. No equality
between the orbit and its chosen seed is included in this definition. -/
def Alternatives (G : Type*) [Group G]
    (ρ : Representation (ZMod 2) A E) (L : Subgroup A) : Prop :=
  IsFFModule (normalizerRepresentation (ρ.comp L.subtype)) ∨
    OrthogonalMinusAlternative ρ L ∨ Nonempty (G ≃* Janko4.Model)

end CFSG.Quasithin.Chapter7.NormalizedSource
