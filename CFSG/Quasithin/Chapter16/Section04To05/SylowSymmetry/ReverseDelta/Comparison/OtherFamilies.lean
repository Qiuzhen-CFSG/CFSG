module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.InnerOnly
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.Divisibility
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.OddTwo
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.InnerOnly

/-!
# Odd-characteristic and sporadic residual comparisons

The Fermat–Mersenne PSL₂ alternative is excluded, including parameters five
and seven, using the genuine inner row and explicit outer table rows.
Inner-only sporadic rows reduce the full catalogue to M₁₂, M₂₂, J₂ and HS.
Odd-prime transport through both covering kernels is available for the
remaining comparisons. All family identifications are actual isomorphisms.

The PSL₃(3), M₂₂/J₂, and HS exclusions remain separate obligations. Thus
`remaining_models` is a reduction and does not assert the final M₁₂
identification. Earlier table inputs must be propagated by its assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
16.1.5 and proof of 16.4.11(2), printed pp.1171–1172 and 1193.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The proved exclusions reduce (E2)(ii)–(iii) to these five actual models.
The four alternatives other than M₁₂ still require their residual comparisons. -/
theorem remaining_models (d : Contrary T z L g R r)
    (oddTables : OddTwoTables) (innerRows : InnerOnlySporadicRows)
    (h : OtherPreliminaries.IsOtherEvenTypeComponent L) :
    ClassicalGroup.IsPSL L 3 3 ∨
    Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M12) ∨
    Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M22) ∨
    Nonempty ((L ⧸ center L) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
    Nonempty ((L ⧸ center L) ≃* Sporadic.LeechRelated.HS.Carrier) := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact (not_pslTwo_family d oddTables h).elim
  · exact Or.inr (sporadic_remaining d innerRows h)

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
